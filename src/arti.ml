(** This module provides the companion implementation to our functional pearl. *)

(** OCaml has built-in syntax for product types (tuples), but not for
    sum types. *)
type ('a, 'b) sum =
| L of 'a
| R of 'b

(** {2 Polymorphic sets, implemented as RBT}  *)
module PSet = struct


  (* This code is different from the other implementation of RBT
     below, by intension*)
  module RBT = struct
    type 'a t =
    | Empty
    | Red of 'a t * 'a * 'a t
    | Black of 'a t * 'a * 'a t

    let empty = Empty

    let rec mem compare x = function
      | Empty -> false
      | Red (l,v,r) | Black (l,v,r) ->
	begin
	  match compare x v with
	  | -1 -> mem compare x l
	  | 0 -> true
	  | _ -> mem compare x r
	end

    let blacken = function
      | Red (l,v,r) -> Black (l,v,r)
      | (Empty | Black _) as n -> n

    let balance = function
      | Black ((Red (Red (a, x, b), y, c)
		   | Red (a, x, Red (b, y, c))), z, d)
      | Black (a, x, (Red (Red (b, y, c), z, d)
			 | Red (b, y, Red (c, z, d))))
	-> Red (Black (a, x, b), y, Black (c, z, d))
      | n -> n

    let insert compare x n =
      let rec insert x t = match t with
	| Empty -> Red (Empty, x, Empty)
	| Red (l,v,r) ->
	  begin match compare x v with
	  | -1 -> Red (insert x l,v,r)
	  | 0 -> Red (l,v,r)
	  | _ -> Red (l,v,insert x r)
	  end
	| Black (l,v,r) ->
	  begin match compare x v with
	  | -1 -> balance (Black (insert x l,v,r))
	  | 0 -> Black (l,v,r)
	  | _ -> balance (Black (l,v,insert x r))
	  end
      in blacken (insert x n)

    let rec elements = function
      | Empty -> []
      | Red (l,v,r) | Black (l, v, r) ->
	elements l @ (v::elements r)

    (* let rec fold_left f acc = function *)
    (*   | Empty -> acc *)
    (*   | Red (l,v,r) | Black (l,v,r) -> *)
    (* 	let acc = fold_left f acc l in *)
    (* 	let acc = f acc v in *)
    (* 	fold_left f acc r *)

    let rec iter f = function
      | Empty -> ()
      | Red (l,v,r) | Black (l,v,r) ->
	iter f l;
	f v;
	iter f r


    let rec cardinal = function
      | Empty -> 0
      | Red (l,_,r) | Black (l,_,r) -> cardinal l + cardinal r + 1
  end

  (** {2 Wrapping the set with the associated comparison function.}  *)
  type 'a t =
    {
      set: 'a RBT.t;
      compare: 'a -> 'a -> int;
    }

  let create compare = {set= RBT.empty; compare}
  let insert x s = {s with set = RBT.insert s.compare x s.set}
  let mem x s = RBT.mem s.compare x s.set
  let cardinal s = RBT.cardinal s.set
  let elements s = RBT.elements s.set
  (* let fold_left f acc s  = RBT.fold_left f acc s.set *)
  let iter f s = RBT.iter f s.set
end

type ident = string

(** Internally, a type descriptor is made up of:
    - a unique identifier
    - a size annotation: the maximum number of elements of this type that we are going to build;
    - an enumeration of the inhabitants of the type
    - a function that generates a new ['a] different from all the
    ['a]s we have constructed so far; this function is only available
    for ground types (e.g.  int)
*)
type 'a ty =
    {
      uid: int;
      size: int;
      ident: string;
      mutable enum: 'a PSet.t;
      fresh: ('a PSet.t -> 'a) option;
    }

type ('a, 'b) bijection = ('a -> 'b) * ('b -> 'a)

(** The GADT [('ty, 'head) negative] describes currified functions of
 * type ['ty] whose return datatype is a positive type ['head]. The
 * words "negative" (for functions) and "positive" (for products
 * and sums) comes from focusing, a point of view that is surprisingly
 * adapted here.
 *
 * - the [Fun] constructor models function types [P -> N], where [P] is
 * a positive type and [N] is negative (functions returned by functions
 * corresponds to currification). The return type of [P -> N], as
 * a currified function, is the return type of [N].
 *
 * - the [Ret] constructor corresponds to the final end of
 * a multi-arrow function type, or to 0-ary functions. It takes
 * a positive datatype (in focusing terms, it is the "shift" that
 * embeds positives into negatives).  *)
type (_, _) negative =
| Fun : 'a positive * ('b, 'c) negative -> ('a -> 'b, 'c) negative
| Ret : 'a positive -> ('a, 'a) negative

(** The GADT ['a positive] describes first-order datatypes (sums,
    products and atomic types) of type ['a].

    Note that there is no embedding of negatives into positives: our
    functions are first-orders and cannot take functions as arguments
    themselves. In logic, this corresponds to the restriction from all
    propositions to Horn Clauses, which have good proof-search
    properties.

    It may be possible to later remove this limitation to the type
    language, but it could be fairly difficult.
*)
and _ positive =
| Ty : 'a ty -> 'a positive
| Sum : 'a positive * 'b positive -> ('a, 'b) sum positive
| Prod : 'a positive  * 'b positive -> ('a * 'b) positive
| Bij : 'a positive * ('a, 'b) bijection -> 'b positive

type elem = Elem : ('a,'b) negative * 'a -> elem
type atom = Atom : 'a ty -> atom

(** {2 The core module of our type descriptors } *)
module Ty = struct

  let gensym: unit -> int =
    let r = ref (-1) in
    fun () -> incr r; !r

  let mem (x: 'a) (s: 'a ty): bool =
    PSet.mem x s.enum

  let cardinal s = PSet.cardinal s.enum

  let equal s1 s2 = s1.uid = s2.uid

  let add (x: 'a) (s: 'a ty): unit =
    s.enum <- PSet.insert x s.enum

  let elements (s: 'a ty): 'a list =
    PSet.elements s.enum

  (* ------------------------------------------------------------------------ *)

  (** Functions for creating new ['a t]s. *)

  (** This function allows one to declare a new type descriptor. All the
      * arguments are filled with sensible defaults. *)
  let declare
      ?(cmp=(Pervasives.compare))
      ?(initial=[])
      ?(ident="<abstract>")
      ?fresh
      ()
      : 'a ty =
    {
      enum = List.fold_left (fun acc x -> PSet.insert x acc) (PSet.create cmp) initial;
      uid = gensym ();
      size = 1000;
      fresh;
      ident
    }

  (** This function populates an existing type descriptor who has a
      built-in generator by calling repeatedly the said generator. *)
  let populate n ty =
    match ty.fresh with
    | None -> ()
    | Some fresh ->
      for __ = 0 to n - 1 do
        (add (fresh ty.enum) ty)
      done
end

(* -------------------------------------------------------------------------- *)

(** {2 Main routines for dealing with our GADT } *)

(** Recursively find the positive head of a negative type *)
let rec codom : type a b. (a,b) negative -> b positive = function
  | Fun (_,fd) -> codom fd
  | Ret ty -> ty

let rec pos_atoms : type a . a positive -> atom list = function
  | Ty ty -> [Atom ty]
  | Sum (ta, tb) -> pos_atoms ta @ pos_atoms tb
  | Prod (ta, tb) -> pos_atoms ta @ pos_atoms tb
  | Bij (t, _bij) -> pos_atoms t

let rec neg_atoms : type a b . (a, b) negative -> atom list = function
  | Ret _ -> []
  | Fun (p, n) -> pos_atoms p @ neg_atoms n

let eq_atom (Atom t1) (Atom t2) = Ty.equal t1 t2

module Eval = struct

  type _ set =
    | Set   : 'a PSet.t -> 'a set
    | Bij   : 'a set * ('a, 'b) bijection -> 'b set
    | Union   : 'a set * 'b set -> ('a,'b) sum set
    | Product : 'a set * 'b set -> ('a * 'b) set

  let rec iter:
  type a.  (a -> unit) -> a set -> unit = fun f s ->
    begin match s with
      | Set ps -> PSet.iter f  ps
      | Union (pa,pb) ->
	iter (fun a -> f (L a)) pa;
	iter (fun b -> f (R b)) pb;
      | Bij (ps, bij) ->
        iter (fun a -> f (fst bij a)) ps
      | Product (pa,pb) ->
	iter (fun a -> iter (fun b -> f (a,b)) pb) pa
    end

  type (_,_) scaffold =
    | Nil : 'a positive -> ('a,'a) scaffold
    | Cons: 'a set * ('b,'c) scaffold -> ('a -> 'b,'c) scaffold


    (** Now comes the reason for separating positives and negatives in
	two distinct groups: they are used in very different ways to
	produce new elements.

	When available, a function of type [a], described as a [(a, b)
	negative], can be applied to deduce new values of type
	[b]. This requires producing known values for its (positive)
	arguments.

	There are two pitfalls here.

	First, it is completely inefficient to build a list of results
	by evaluating a function and merge them in the codom type
	afterwards. This list is potentially big, and one can run into
	Stack_overflow issues.

	Second, it is tempting to add new elements to the mutable
	enumeration of the types on the fly, but we can run into
	non-termination, as soon as we have a function of type [t -> _
	-> t].

	Therefore, we proceed by building a scaffold (a snapshot of the
	enumeration of the types before evaluating the function), and
	will iterate on this fix snapshot.  *)

  let rec scaffold:
  type a b. (a,b) negative -> (a,b) scaffold =
      function
	| Ret p -> Nil p
	| Fun (p,n) -> Cons (produce p,(scaffold n))
  and
    produce:
  type a. a positive -> a set =
      function
	| Ty ty ->
	  Set (ty.enum)
        | Bij (p, bij) ->
          Bij (produce p, bij)
	| Prod (pa,pb) ->
	  Product (produce pa, produce pb)
	| Sum (pa, pb) ->
	  Union (produce pa, produce pb)

    (** A positive datatype can be destructed by pattern-matching to
	discover new values for the atomic types at its leaves. *)
  let rec destruct:
  type a . a positive -> a -> unit = function
    | Ty ty -> begin fun v -> Ty.add v ty end
    | Bij (t, bij) -> begin fun v -> destruct t (snd bij v) end
    | Prod (ta, tb) ->
      begin fun (a, b) ->
        destruct ta a;
        destruct tb b;
      end
    | Sum (ta, tb) ->
      begin function
        | L a -> destruct ta a
        | R b -> destruct tb b
      end

  let rec eval:
  type a b. (a,b) scaffold -> a -> unit = fun sd f ->
    match sd with
      | Nil p -> destruct p f
      | Cons (s,sd) ->
	iter (fun e -> eval sd (f e)) s

  let main:
  type a b.  (a,b) negative -> a -> unit = fun  n f ->
    let sd = scaffold n in
    eval sd f

end

(** Check a property over all the elements of ['a ty] that were
 * generated up to this point. This function returns [Some x] where [x] is an
 * element that fails to satisfy the property, and [None] is no such element
 * exists. *)

exception Found
let counter_example msg pos f =
  let r = ref None in
  let n = ref 0 in
  begin
    try Eval.iter
	  (fun e ->
	    incr n;
	    if not (f e)
	    then (r := Some e; raise Found))
	  (Eval.produce pos);
	Printf.eprintf "[%.12s] Passed %i tests without counter-examples\n" msg (!n);
    with Found -> ()
  end;
  !r

(* -------------------------------------------------------------------------- *)

(** {2 Describing signatures of modules that we wish to test } *)

module Sig :
sig
  type value
  val val_ : ident -> ('a,'b) negative -> 'a -> value
  val populate : value list -> unit
end
  =
struct
  module M = struct
    module HT = Hashtbl.Make(
      struct
	type t = atom
	let uid (Atom ty) = ty.uid
	let hash = uid
	let equal = eq_atom
      end
      )
    type key = atom
    type 'a t = 'a HT.t
    let create () = HT.create 1337
    let clear ht = HT.clear ht
    let add k v ht = HT.add ht k v
    let find k ht = HT.find ht k
    let iter f ht = HT.iter f ht
  end

  type elem_stats = { required : int; produced : int }

  module P = struct
    type property = elem_stats
    let bottom = { required = max_int; produced = 0 }
    let equal p1 p2 = p1.produced = p2.produced
    let is_maximal p = p.produced >= p.required
  end

  module F = Fix.Make(M)(P)

  let touch env ty = ignore (env (Atom ty))

  let populate sig_ =
    let eqs : F.variable -> (F.valuation -> F.property) =
      fun atom env ->
        (* use the proper constructors *)
        List.iter (fun (_, Elem (fd, f)) ->
          let inputs = neg_atoms fd in
          let head = codom fd in
          let outputs = pos_atoms head in
          if List.exists (eq_atom atom) outputs then begin
            List.iter (fun (Atom ty) -> touch env ty) inputs;
	    Eval.main fd f
          end
	) sig_;
	(* use fresh *)
        let (Atom ty) = atom in
	Ty.populate 10 ty;
	{ produced = Ty.cardinal ty;
          required = ty.size }
    in F.lfp eqs


  type value = string * elem

  (** A helper for constructor a signature item. *)
  let val_ id fd f : value = (id, Elem (fd, f))

  (** This is the function that you want to use: take the description
      of a module signature, then use it to generate elements for all
      the types in the module. *)
  let populate (s: value list) =
    let pop = populate s in
    let trigger (_id, Elem (fd, _f)) =
      let popa tom = ignore (pop tom) in
      List.iter popa (pos_atoms (codom fd)) in
    List.iter trigger s
end

(** Some constructors for our GADT. *)

let atom ty = Ty ty
let returning atom = Ret atom
let (@->) a b = Fun (a,b)
let (+@) a b = Sum (a, b)
let ( *@ ) a b = Prod (a, b)
let bij t f = Bij (t, f)

(** Derived representation constructors *)

(** For now we'll represent [foo option] as [(foo, unit) sum], and
    manually insert back and forth conversions; medium-term, type
    descriptions should have a constructor to hide type bijections. *)
type 'a structural_option = ('a, unit) sum

let of_option = function
  | Some v -> L v
  | None -> R ()
let to_option = function
  | L v -> Some v
  | R () -> None

let option_bij : ('a structural_option, 'a option) bijection =
  (to_option, of_option)

let unit = atom (Ty.declare ~initial:[()] () : unit ty)
let option p = bij (p +@ unit) option_bij
