(** This module provides the companion implementation to our functional pearl. *)

(** OCaml has built-in syntax for product types (tuples), but not for
    sum types. *)
type ('a, 'b) sum =
| L of 'a
| R of 'b

(** Auxiliary functions on lists *)
let concat_map f li = List.flatten (List.map f li)
let cartesian_product la lb =
  let rec prod acc = function
    | [] -> acc
    | b::lb ->
      let lab = List.rev_map (fun a -> (a, b)) la in
      prod (List.rev_append lab acc) lb
  in prod [] lb

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

    (* FIXME why are these unused? *)

    (* type color = R | B *)

    (* let color = function *)
    (*   | Red _ -> R *)
    (*   | Empty | Black _ -> B *)

    (* let mk col l v r = match col with *)
    (*   | B -> Black (l, v, r) *)
    (*   | R -> Red (l, v, r) *)

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
      mutable enum: 'a PSet.t;
      fresh: ('a PSet.t -> 'a) option;
    }


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
(*
  let merge (s: 'a ty) (l: 'a list) =
    let n = PSet.cardinal s.enum in
    s.enum <- List.fold_left (fun acc x -> PSet.insert x acc) s.enum l;
    n < PSet.cardinal s.enum
*)

  (* ------------------------------------------------------------------------ *)

  (** Functions for creating new ['a t]s. *)

  (** This function allows one to declare a new type descriptor. All the
      * arguments are filled with sensible defaults. *)
  let declare
      ?(cmp=(Pervasives.compare))
      ?(initial=[])
      ?fresh
      ()
      : 'a ty =
    {
      enum = List.fold_left (fun acc x -> PSet.insert x acc) (PSet.create cmp) initial;
      uid = gensym ();
      size = 1000;
      fresh;
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

  (** Check a property over all the elements of ['a ty] that were
   * generated up to this point. This function returns [Some x] where [x] is an
   * element that fails to satisfy the property, and [None] is no such element
   * exists. *)
  let counter_example msg ty f =
    let l = PSet.elements ty.enum in
    try Some (List.find (fun e -> not (f e)) l)
    with Not_found ->
      Printf.eprintf "[%.12s] Passed %i tests without counter-examples\n" msg (List.length l);
      None


end

(* -------------------------------------------------------------------------- *)

(** {2 Main routines for dealing with our GADT } *)

(** Some constructors for our GADT. *)

let returning ty = Ret (Ty ty)
let (@->) a b = Fun (Ty a,b)
let (+@) a b = Sum (a, b)
let ( *@ ) a b = Prod (a, b)

(** Recursively find the positive head of a negative type *)
let rec codom : type a b. (a,b) negative -> b positive = function
  | Fun (_,fd) -> codom fd
  | Ret ty -> ty

let rec atoms : type a . a positive -> atom list = function
  | Ty ty -> [Atom ty]
  | Sum (ta, tb) -> atoms ta @ atoms tb
  | Prod (ta, tb) -> atoms ta @ atoms tb

let eq_atom (Atom t1) (Atom t2) = Ty.equal t1 t2

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

  let in_env env ty =
    ignore (env (Atom ty));
    PSet.elements ty.enum

    (** Now comes the reason for separating positives and negatives in
        two distinct groups: they are used in very different ways to
        produce new elements.
        
        When available, a function of type [a], described as a [(a, b)
        negative], can be applied to deduce new values of type
        [b]. This requires producing known values for its (positive)
        arguments.
    *)
    let rec apply
    : type a b . F.valuation -> (a, b) negative -> a -> b list =
      fun env ty v -> match ty with
        | Ret _p -> [v]
        | Fun (p, n) ->
          produce env p |> concat_map (fun a -> apply env n (v a))

    and produce
    : type a . F.valuation -> a positive -> a list = fun env ->
      function
      | Ty ty -> in_env env ty
      | Prod (pa, pb) ->
        cartesian_product (produce env pa) (produce env pb)
      | Sum (pa, pb) ->
        let la = List.rev_map (fun v -> L v) (produce env pa) in
        let lb = List.rev_map (fun v -> R v) (produce env pb) in
        List.rev_append la lb

  (** A positive datatype can be destructed by pattern-matching to
      discover new values for the atomic types at its leaves. *)
  let rec destruct : type a . a positive -> a -> unit = function
    | Ty ty -> begin fun v -> Ty.add v ty end
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

  let populate sig_ =
    let eqs : F.variable -> (F.valuation -> F.property) =
      fun atom env ->
	(* use the proper constructors *)
	List.iter (fun (_, Elem (fd, f)) ->
	  let pos = codom fd in
          if List.exists (eq_atom atom) (atoms pos) then begin
	    let li = apply env fd f in
            List.iter (destruct pos) li
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
      List.iter popa (atoms (codom fd)) in
    List.iter trigger s
end


