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

(** The GADT [('b, 'a) fn] describes functions of type ['b] whose return type is
 * ['a].
 * - The base case is constant values: they have type ['a] and return ['a].
 * - The other case is an arrow: from a function with type ['b] that returns
 *   ['c], we can construct a function of type ['a -> 'b] which still returns
 *   ['c].
 * We attach to each branch a descriptor of the argument type ['a].
 *)
type (_,_) fn =
| Constant : 'a ty -> ('a,'a) fn
| Fun      : 'a ty * ('b, 'c) fn -> ('a -> 'b, 'c) fn;;

(** Some constructors for our GADT. *)

let (@->) ty fd = Fun (ty,fd)
let returning ty = Constant ty

let (>>=) li f = List.flatten (List.map f li)

(** Given an description of functions of type [a] which return [b], and given an
 * initial element [a], generate all possible [b]s. This is the core function of
 * this module. *)
let rec eval : type a b. (a,b) fn -> a -> b list =
  fun fd f ->
    match fd with
    | Constant _ -> [f]
    | Fun (ty,fd) -> ty.Ty.enum >>= fun e -> eval fd (f e)

(** Recursively find the descriptor that corresponds to the codomain of a
 * function. *)
let rec codom : type a b. (a,b) fn -> b ty =
  function
    | Fun (_,fd) -> codom fd
    | Constant ty -> ty


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
let use (fd: ('a, 'b) fn) (f: 'a) =
  let prod = eval fd f in
  let ty = codom fd in
  let tick = blows_after_n Exit 1000 in
  (* [Gabriel] I had to use this for ncheck to terminate in finite
     time on large signatures *)
  try List.iter (fun x -> tick (); Ty.add x ty) prod;
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
  type elem = Elem : ('a,'b) fn * 'a -> elem

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

(** The description of the type of sorted integer lists. Elements of this type
 * can be compared using the polymorphic, structural comparison operator (=). *)
let si_t : SIList.t ty = Ty.declare ()

(** Conversely, [int] is a ground type that can not only be compared with (=),
 * but also admits a generator. *)
let int_t : int ty = Ty.declare ~fresh:(fun _ -> Random.int 1000) ()

(** Populate the descriptor of the built-in type [int]. *)
let () =
  populate 10 int_t

(** Use module [Sig] to build a description of the signature of [SIList]. *)
let silist_sig = Sig.([
  val_ "empty" (returning si_t) SIList.empty;
  val_ "add" (int_t @-> si_t @-> returning si_t) SIList.add;
])

(** Generate instances of [SIList.t]. *)
let () =
  ncheck 5 silist_sig

(** The property that we wish to test for is that the lists are well-sorted. We
 * define a predicate for that purpose and assert that no counter-example can be
 * found. *)
let () =
  let prop s = List.sort Pervasives.compare s = s in
  assert (Ty.counter_example si_t prop = None);
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

let rbt_t : int RBT.t ty = Ty.declare ()
let int_t : int ty = Ty.declare ~fresh:(fun _ -> Random.int 10) ()
let () = populate 5 int_t

let rbt_sig = Sig.([
  val_ "empty" (returning rbt_t) RBT.empty;
  val_ "insert" (int_t @-> rbt_t @-> returning rbt_t) RBT.insert;
])

let () = ncheck 5 rbt_sig

let () =
  let prop s = let s = RBT.elements s in List.sort Pervasives.compare s = s in
  assert (Ty.counter_example rbt_t prop = None);
  assert (Ty.counter_example rbt_t RBT.is_balanced = None);
  ()

let dir_t : RBT.direction ty = Ty.declare ~initial:RBT.([Left; Right]) ()
let rbtopt_t : int RBT.t option ty = Ty.declare ()
let ptropt_t : int RBT.pointer option ty = Ty.declare ()

let zip_sig = RBT.(rbt_sig @ Sig.([
  val_ "Some" (rbt_t @-> returning rbtopt_t)
    (fun z -> Some z);
  val_ "some zip_open" (rbt_t @-> returning ptropt_t)
    (fun v -> Some (zip_open v));
  val_ "some zip_close" (ptropt_t @-> returning rbtopt_t)
    (function None -> None | Some v -> Some (zip_close v));

  val_ "move_up" (ptropt_t @-> returning ptropt_t)
    (function None -> None | Some v -> move_up v);
  val_ "move" (dir_t @-> ptropt_t @-> returning ptropt_t)
    (fun dir -> function None -> None | Some v -> move dir v);
]))

let () = ncheck 1 zip_sig

let () =
  let prop = function
    | None -> true
    | Some v -> RBT.is_balanced v in
  assert (Ty.counter_example rbtopt_t prop = None)
