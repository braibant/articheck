(** This module provides the companion implementation to our functional pearl. *)

(** {2 The core module of our type descriptors } *)

module Ty = struct

  (** Internally, a type descriptor of ['a] is an imperative data structure made
   * up of:
   * - an equality function,
   * - the list of ['a]s we have constructed so far,
   * - a function that generates a new ['a] different from all the ['a]s we have
   * constructed so far; this function is only available for ground types (e.g.
   * int)
   * - ??
   * - a unique identifier. *)
  type 'a t = {
    eq: 'a -> 'a -> bool;
    mutable enum : 'a list;
    fresh : ('a list -> 'a) option;
    invar : 'a -> bool;
    uid : int;
  }

  let mem (x: 'a) (s: 'a t): bool =
    List.exists (fun y -> y = x) s.enum

  let add (x: 'a) (s: 'a t): unit =
    if mem x s then () else s.enum <- x::s.enum

  let elements (s: 'a t): 'a list =
    s.enum

  let gensym: unit -> int =
    let r = ref (-1) in
    fun () -> incr r; !r

  (* ------------------------------------------------------------------------ *)

  (** Functions for creating new ['a t]s. *)

  (** This function allows one to declare a new type descriptor. All the
   * arguments are filled with sensible defaults. *)
  let declare
    ?(eq=(=))
    ?(initial=[])
    ?fresh
    ?(invar = (fun _ -> true)) ()
  : 'a t = {
    eq;
    enum = initial;
    fresh;
    invar;
    uid = gensym ()
  }

  (* XXX: what is [invar]? this function is not used anywhere else in the code,
   * so it's hard to guess its purpose. Some original comments follow.
   *
   * generate a fresh type descriptor
   * maybe we could remember what is the base type, so that if we run
   * out of elements for the new type, we could generate new instances of
   * the old one, and select the one that fulfill the invariant.
  let (/) ty invar =
    let invar x = invar x && ty.invar x in
    {ty with uid = gensym (); invar} *)

  (** Check a property over all the elements of ['a ty] that were
   * generated up to this point. This function returns [Some x] where [x] is an
   * element that fails to satisfy the property, and [None] is no such element
   * exists. *)
  let counter_example ty f =
    try Some (List.find (fun e -> not (f e)) ty.enum)
    with Not_found -> None
end

(* -------------------------------------------------------------------------- *)

(** {2 Main routines for dealing with our GADT } *)

(** The type of our type descriptors. *)
type 'a ty = 'a Ty.t

(** OCaml has built-in syntax for product types (tuples), but not for
    sum types. *)
type ('a, 'b) sum =
| L of 'a
| R of 'b

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

(** Recursively find the positive head of a negative type *)
let rec codom : type a b. (a,b) negative -> b positive = function
  | Fun (_,fd) -> codom fd
  | Ret ty -> ty

(** Some constructors for our GADT. *)

let (@->) a b = Fun (a,b)
let (++) a b = Sum (a, b)
let ( ** ) a b = Prod (a, b)

(** Auxiliary functions on lists *)
let concat_map f li = List.flatten (List.map f li)
let cartesian_product la lb =
  let rec prod acc = function
    | [] -> acc
    | b::lb ->
      let lab = List.rev_map (fun a -> (a, b)) la in
      prod (List.rev_append lab acc) lb
  in prod [] lb

(** Now comes the reason for separating positives and negatives in two
    distinct groups: they are used in very different ways to produce
    new elements.

    When available, a function of type [a], described as a [(a, b)
    negative], can be applied to deduce new values of type [b]. This
    requires producing known values for its (positive) arguments.
*)
let rec apply : type a b . (a, b) negative -> a -> b list =
  fun ty v -> match ty with
    | Ret pos -> [v]
    | Fun (p, n) -> produce p |> concat_map (fun a -> apply n (v a))
and produce : type a . a positive -> a list = function
  | Ty ty -> ty.Ty.enum
  | Prod (pa, pb) -> cartesian_product (produce pa) (produce pb)
  | Sum (pa, pb) ->
    let la = List.rev_map (fun v -> L v) (produce pa) in
    let lb = List.rev_map (fun v -> R v) (produce pb) in
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


(* -------------------------------------------------------------------------- *)

(** {2 Populating our type descriptors } *)

(** Helper function that returns a function [tick]. Calling [tick] more than [n]
 * times will raise [exn]. *)
let blows_after_n (exn: exn) (n: int): unit -> unit =
  let count = ref 0 in
  fun () ->
    incr count;
    if !count > n then raise exn

(** Slightly higher-level function. This one takes a descriptor of a function of
 * type ['a] that produce ['b], as well as a function [f] with the right type.
 * It [eval]s [fd] so as to generate a list of ['b]s, finds the descriptor of
 * type ['b], and then mutates it to stores all the elements we have constructed
 * (within a reasonable number, of course). *)
let use (fd: ('a, 'b) negative) (f: 'a) =
  let prod = apply fd f in
  let ty = codom fd in
  let tick = blows_after_n Exit 1000 in
  (* [Gabriel] I had to use this for ncheck to terminate in finite
     time on large signatures *)
  try List.iter (fun x -> tick (); destruct ty x) prod;
  with Exit -> ()

(** This function populates an existing type descriptor who has a built-in
 * generator by calling repeatedly the said generator. *)
let populate n ty =
  match ty.Ty.fresh with
    | None -> invalid_arg "populate"
    | Some fresh ->
      for __ = 0 to n - 1 do
        Ty.(add (fresh ty.enum) ty)
      done


(* -------------------------------------------------------------------------- *)

(** {2 Describing signatures of modules that we wish to test } *)

module Sig = struct
  (** An element from a module signature is a function of type ['a], along with
   * its descriptor. *)
  type elem = Elem : ('a,'b) negative * 'a -> elem

  (** Elements have a name. *)
  type ident = string

  (** Finally, a signature item is the name of the element along with the
   * description of the element itself. *)
  type t = (ident * elem) list

  (** A helper for constructor a signature item. *)
  let val_ id fd f = (id, Elem (fd, f))
end

(** This is the function that you want to use: take the description of a module
 * signature, then iterate [n] times to generate elements for all the types in
 * the module. *)
let ncheck n (s: Sig.t) =
  for __ = 1 to n do
    List.iter (fun (_id, Sig.Elem (fd, f)) -> use fd f) s;
  done

(** Check a property over all the elements of datatype that were
 * generated up to this point. This function returns [Some x] where [x] is an
 * element that fails to satisfy the property, and [None] is no such element
 * exists. *)
let counter_example ty f =
  try Some (produce ty |> List.find (fun e -> not (f e)))
  with Not_found -> None

(* -------------------------------------------------------------------------- *)

(** {2 Examples } *)

(** {3 Sorted integer lists } *)

module SIList = struct
  type t = int list

  let empty = []

  let rec add x = function
    | [] -> [x]
    | t::q -> if t < x then t :: add x q else x::t::q
end

(** The description of the type of sorted integer lists. *)
let si_t = Ty (Ty.declare () : SIList.t ty)

(** Conversely, [int] is a ground type that can not only be compared with (=),
 * but also admits a generator. *)
let int_t =
  let ty : int ty = Ty.declare ~fresh:(fun _ -> Random.int 1000) () in
  (** Populate the descriptor. *)
  populate 10 ty;
  Ty ty

(** Use module [Sig] to build a description of the signature of [SIList]. *)
let silist_sig = Sig.([
  val_ "empty" (Ret si_t) SIList.empty;
  val_ "add" (int_t @-> si_t @-> Ret si_t) SIList.add;
])

(** Generate instances of [SIList.t]. *)
let () =
  ncheck 5 silist_sig

(** The property that we wish to test for is that the lists are well-sorted. We
 * define a predicate for that purpose and assert that no counter-example can be
 * found. *)
let is_sorted s = (List.sort Pervasives.compare s = s)

let () =
  assert (counter_example si_t is_sorted = None);
  ()


(** {3 Red-black trees } *)

module type RBT = sig
  (* private types to enforce abstraction
     but keep pretty-printing in the toplevel *)
  type 'a t = private
  | Empty
  | Red of 'a t * 'a * 'a t
  | Black of 'a t * 'a * 'a t

  val empty : 'a t
  (* XXX this function was not exported before, meaning it was untested? *)
  val mem : 'a -> 'a t -> bool
  val insert : 'a -> 'a t -> 'a t
  val elements : 'a t -> 'a list
  val is_balanced : 'a t -> bool

  (* public type, part of the user interface for the 'move' function *)
  type direction = Left | Right
  type 'a zipper
  type 'a pointer

  val zip_open : 'a t -> 'a pointer
  val zip_close : 'a pointer -> 'a t

  val move_up : 'a pointer -> 'a pointer option
  val move : direction -> 'a pointer -> 'a pointer option
end

module RBT : RBT  = struct
  type 'a t =
  | Empty
  | Red of 'a t * 'a * 'a t
  | Black of 'a t * 'a * 'a t

  let empty = Empty
  let rec mem x = function
    | Empty -> false
    | Red (l,v,r) | Black (l,v,r) ->
      begin
	match compare x v with
	| -1 -> mem x l
	| 0 -> true
	| _ -> mem x r
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

  type color = R | B

  let color = function
    | Red _ -> R
    | Empty | Black _ -> B

  let mk col l v r = match col with
    | B -> Black (l, v, r)
    | R -> Red (l, v, r)

  let insert x n =
    let rec insert x t = match t with
      | Empty -> Red (Empty, x, Empty)
      | Red (l,v,r) | Black (l,v,r) ->
        let l, r =
          if x <= v
          then insert x l, r
          else l, insert x r in
        balance (mk (color t) l v r)
    in blacken (insert x n)

  let rec elements = function
    | Empty -> []
    | Red (l,v,r) | Black (l, v, r) ->
      elements l @ (v::elements r)

(* http://en.wikipedia.org/wiki/Red-black_tree, simplified:

  In addition to the requirements imposed on a binary search tree the
  following must be satisfied by a red–black tree:

  - The root is black.
  - Every red node must have two black child nodes.
  - Every path from a given node to any of its descendant leaves
    contains the same number of black nodes.
*)
  let is_balanced t =
      let rec check_black_height t = match t with
        | Empty -> 0
        | Red (l, _, r) | Black (l, _, r) ->
          if color t = R && (color l, color r) <> (B, B) then
            raise Exit;
          let bhl = check_black_height l in
          let bhr = check_black_height r in
          if bhl <> bhr then raise Exit;
          bhl + (match color t with B -> 1 | R -> 0)
      in
    try
      ignore (check_black_height t);
      color t = B
    with Exit -> false

  type 'a zipper = 'a frame list
  and direction = Left | Right
  and 'a frame = {
    col : color;
    dir : direction;
    v : 'a;
    sibling : 'a t;
  }

  type 'a pointer = 'a t * 'a zipper

  let close_frame t frame =
    let t = match frame with
      | {dir = Left; col; v; sibling} -> mk col t v sibling
      | {dir = Right; col; v; sibling} -> mk col sibling v t in
    (* balancing here is crucial to preserve the rbtree invariants! *)
    balance t

  let zip_open t = (t, [])

  let zip_close (t, frames) =
    List.fold_left close_frame t frames

  let move_up (t, zip) = match zip with
    | [] -> None
    | frame::zip -> Some (close_frame t frame, zip)

  let move_frame dir t = match t with
    | Empty -> None
    | Red (l, v, r) | Black (l, v, r) ->
      let col = color t in
      match dir with
        | Left -> Some (l, {dir; col; v; sibling = r})
        | Right -> Some (r, {dir; col; v; sibling = l})

  let move dir (t, zip) =
    match move_frame dir t with
      | None -> None
      | Some (t, frame) -> Some (t, frame::zip)
end

let rbt_t = Ty (Ty.declare () : int RBT.t ty)

let rbt_sig = Sig.([
  val_ "empty" (Ret rbt_t) RBT.empty;
  val_ "insert" (int_t @-> rbt_t @-> Ret rbt_t) RBT.insert;
])

let () = ncheck 5 rbt_sig

let () =
  let is_sorted s = is_sorted (RBT.elements s) in
  assert (counter_example rbt_t is_sorted = None);
  assert (counter_example rbt_t RBT.is_balanced = None);
  ()

let dir_t = Ty (Ty.declare ~initial:RBT.([Left; Right]) () : RBT.direction ty)
let rbtopt_t = Ty (Ty.declare () : int RBT.t option ty)
let ptropt_t = Ty (Ty.declare () : int RBT.pointer option ty)

let zip_sig = RBT.(rbt_sig @ Sig.([
  val_ "Some" (rbt_t @-> Ret rbtopt_t)
    (fun z -> Some z);
  val_ "some zip_open" (rbt_t @-> Ret ptropt_t)
    (fun v -> Some (zip_open v));
  val_ "some zip_close" (ptropt_t @-> Ret rbtopt_t)
    (function None -> None | Some v -> Some (zip_close v));

  val_ "move_up" (ptropt_t @-> Ret ptropt_t)
    (function None -> None | Some v -> move_up v);
  val_ "move" (dir_t @-> ptropt_t @-> Ret ptropt_t)
    (fun dir -> function None -> None | Some v -> move dir v);
]))

let () = ncheck 1 zip_sig

let () =
  let prop = function
    | None -> true
    | Some v -> RBT.is_balanced v in
  assert (counter_example rbtopt_t prop = None)
