(** This module provides the companion implementation to our functional pearl. *)


(** {2 Polymorphic sets, implemented as RBT}  *)
module PSet = struct


  (* This code is different from the other implementation of RBT below, by intension*)
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

    let rec fold_left f acc = function
      | Empty -> acc
      | Red (l,v,r) | Black (l,v,r) ->
	let acc = fold_left f acc l in
	let acc = f acc v in
	fold_left f acc r

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
  let fold_left f acc s  = RBT.fold_left f acc s.set
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
      mutable constructors: (ident * 'a elem) list;
    }
and
  (** The GADT [('b, 'a) fn] describes functions of type ['b] whose return type is
      * ['a].
      * - The base case is constant values: they have type ['a] and return ['a].
      * - The other case is an arrow: from a function with type ['b] that returns
      *   ['c], we can construct a function of type ['a -> 'b] which still returns
      *   ['c].
      * We attach to each branch a descriptor of the argument type ['a].
  *)
  (_,_) fn =
  | Constant : 'a ty -> ('a,'a) fn
  | Fun      : 'a ty * ('b, 'c) fn -> ('a -> 'b, 'c) fn
and
  'b elem =
    Elem : ('a,'b) fn * 'a -> 'b elem
;;



(** {2 The core module of our type descriptors } *)
module Ty = struct

  let gensym: unit -> int =
    let r = ref (-1) in
    fun () -> incr r; !r

  let mem (x: 'a) (s: 'a ty): bool =
    PSet.mem x s.enum

  let cardinal s = PSet.cardinal s.enum

  let add (x: 'a) (s: 'a ty): unit =
    s.enum <- PSet.insert x s.enum

  let elements (s: 'a ty): 'a list =
    PSet.elements s.enum

  let merge (s: 'a ty) (l: 'a list) =
    let n = PSet.cardinal s.enum in
    s.enum <- List.fold_left (fun acc x -> PSet.insert x acc) s.enum l;
    n < PSet.cardinal s.enum

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
      constructors = [];
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

let (@->) ty fd = Fun (ty,fd)
let returning ty = Constant ty

(** Recursively find the descriptor that corresponds to the codomain of a
 * function. *)
let rec codom :
type a b. (a,b) fn -> b ty =
    function
      | Fun (_,fd) -> codom fd
      | Constant ty -> ty
;;


(* -------------------------------------------------------------------------- *)

(** {2 Describing signatures of modules that we wish to test } *)

module Sig :
sig
  type value
  val val_ : ident -> ('a,'b) fn -> 'a -> value
  val populate : value list -> unit
end
  =
struct

  type descr = Descr : 'a ty -> descr

  module M = struct
    module HT = Hashtbl.Make(
      struct
	type t = descr
	let uid = function Descr d -> d.uid
	let hash = uid
	let equal t1 t2 = uid t1 = uid t2
      end
      )
    type key = descr
    type 'a t = 'a HT.t
    let create () = HT.create 1337
    let clear ht = HT.clear ht
    let add k v ht = HT.add ht k v
    let find k ht = HT.find ht k
    let iter f ht = HT.iter f ht
  end

  module P = struct
    type property = int
    let bottom = 0
    let equal = (=)
    let is_maximal (_:property) = false
  end

  module F = Fix.Make(M)(P)

  module Eval = struct
    (* There are two pitfalls here.

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

    type (_,_) scaffold =
      | Nil : ('a,'a) scaffold
      | Cons: 'a PSet.t * ('b,'c) scaffold -> ('a -> 'b,'c) scaffold

    let rec scaffold:
    type a b. (a,b) fn -> (a,b) scaffold =
	function
	  | Constant _ -> Nil
	  | Fun (ty,fd) -> Cons (ty.enum,(scaffold fd))



    let rec eval :
    type a b. (a,b) scaffold -> a -> b PSet.t -> b PSet.t  =
	fun sd f acc ->
	  match sd with
	    | Nil -> PSet.insert f acc
	    | Cons (s,sd) ->
	      PSet.fold_left (fun acc e -> eval sd (f e) acc) acc s

  end

  let rec touch:
  type a b. F.valuation -> (a,b) fn -> unit = fun env fd ->
    match fd with
      | Constant _ -> ()
      | Fun (ty,fd) ->
	ignore (env (Descr ty));
	touch env fd

  let eval:
  type a b. (a,b) fn -> a -> unit = fun fd f ->
      let sd = Eval.scaffold fd in
      let tgt = codom fd in
      tgt.enum <- Eval.eval sd f tgt.enum

  let populate =
    let eqs : F.variable -> (F.valuation -> F.property) = fun dty env ->
      match dty with
      | Descr ty ->
	begin
	  let c =  Ty.cardinal ty in
	  Printf.eprintf "type %s: %i\n%!" ty.ident c;
	  if ty.size <= c
	  then 				(* full *)
	    c
	  else
	    begin
	      (* use the proper constructors *)
	      List.iter (fun (id,e) ->
		match e with
		| Elem (fd,f) ->
		  (* touch the arguments of the function *)
		  touch env fd;

		  let ty = codom fd in
		  let c1 = Ty.cardinal ty in
		  Printf.eprintf "using %s\t%!" id;
		  eval fd f;
		  Printf.eprintf "found new elements (%i)\n%!" (Ty.cardinal ty - c1)
	      ) ty.constructors;
	      (* use fresh *)
	      Ty.populate 10 ty;
	      Ty.cardinal ty
	    end
	end
    in
    F.lfp eqs

  type value = descr

  (** A helper for constructor a signature item. *)
  let val_ id fd f : value =
    let tgt = codom fd in
    tgt.constructors <- (id, Elem (fd,f)) :: tgt.constructors;
    let r = Descr tgt in
    Printf.eprintf "declared %s\n%!" id;
    r

  (** This is the function that you want to use: take the description of
      a module signature, then use it to generate elements for all the
      types in the module. *)

  let populate (s: value list) = List.iter (fun dty -> ignore (populate dty)) s
end
