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

    type color = R | B

    let color = function
      | Red _ -> R
      | Empty | Black _ -> B

    let mk col l v r = match col with
      | B -> Black (l, v, r)
      | R -> Red (l, v, r)

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

  let create compare = {set= RBT.Empty; compare}
  let insert x s = {s with set = RBT.insert s.compare x s.set}
  let mem x s = RBT.mem s.compare x s.set
  let cardinal s = RBT.cardinal s.set
  let elements s = RBT.elements s.set
end

(** {2 The core module of our type descriptors } *)
module Ty = struct

  (** Internally, a type descriptor is made up of:
      - a unique identifier
      - a size annotation: the maximum number of elements of this type that we are going to build;
      - an enumeration of the inhabitants of the type
      - a function that generates a new ['a] different from all the
      ['a]s we have constructed so far; this function is only available
      for ground types (e.g.  int)
  *)
  type 'a t =
    {
      uid: int;
      size: int;
      mutable enum: 'a PSet.t;
      fresh: ('a PSet.t -> 'a) option;
    }


  let gensym: unit -> int =
    let r = ref (-1) in
    fun () -> incr r; !r

  let mem (x: 'a) (s: 'a t): bool =
    PSet.mem x s.enum

  let full s = s.size <= PSet.cardinal s.enum

  let add (x: 'a) (s: 'a t): unit =
    s.enum <- PSet.insert x s.enum

  let elements (s: 'a t): 'a list =
    PSet.elements s.enum

  let merge (s: 'a t) (l: 'a list) =
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
      ?fresh
      ()
      : 'a t =
    {
      enum = List.fold_left (fun acc x -> PSet.insert x acc) (PSet.create cmp) initial;
      uid = gensym ();
      size = 50;
      fresh;
    }

  (** This function populates an existing type descriptor who has a
      built-in generator by calling repeatedly the said generator. *)
  let populate n ty =
    match ty.fresh with
    | None -> invalid_arg "populate"
    | Some fresh ->
      for __ = 0 to n - 1 do
        (add (fresh ty.enum) ty)
      done

  (** Check a property over all the elements of ['a ty] that were
   * generated up to this point. This function returns [Some x] where [x] is an
   * element that fails to satisfy the property, and [None] is no such element
   * exists. *)
  let counter_example ty f =
    try Some (List.find (fun e -> not (f e)) (PSet.elements ty.enum))
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

(** Recursively find the descriptor that corresponds to the codomain of a
 * function. *)
let rec codom : type a b. (a,b) fn -> b ty =
  function
    | Fun (_,fd) -> codom fd
    | Constant ty -> ty



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


(* -------------------------------------------------------------------------- *)

(** {2 Populating the types of the module} *)

module Fun = struct



  type descr = Descr : 'a Ty.t -> descr

  module Graph = struct
    type node =
      {descr: descr;
       mutable incoming: edge list;
       mutable outgoing: edge list;
       mutable constructors: Sig.t;
       mutable mark: bool
      }
    and edge =
      {node1: node;
       node2: node;
       mutable destroyed: bool}

    module T (X: sig type 'a value end) = struct
      open Ty
      module HT = struct
	include X
	type t = Bind: 'a Ty.t * ('a value) option -> t
	let uid = function Bind (ty,_) -> ty.uid
	let equal t1 t2 = uid t1 = uid t2
	let hash = uid
      end
      module WHT = Weak.Make(HT)

      open HT
      let add t k v =
	WHT.merge t (Bind (k,Some v))

      let find t k =
	match WHT.find t (Bind (k,None)) with
	| Bind (_,None) -> raise Not_found
	| Bind (_,Some v) -> Obj.magic v

      let create () = WHT.create 1337

  end
    module N = T(struct type 'a value = node end)

    let create ty =
      {
	descr = Descr ty;
	incoming = [];
	outgoing = [];
	constructors = [];
	mark = true
      }

    let link (n1: node) (n2: node) =
      let e = {node1 = n1; node2 = n2; destroyed = false} in
      n1.outgoing <- e::n1.outgoing;
      n2.outgoing <- e::n2.outgoing

    let follow src edge =
      if edge.node1 == src then
	edge.node2
      else begin
	assert (edge.node2 == src);
	edge.node1
      end

    let successors node =
      let successors = List.filter (fun edge -> not edge.destroyed) node.outgoing in
      node.outgoing <- successors;
      List.map (follow node) successors

    (* smart constructor *)


    let nodes = N.create ()
    let node:
    type t. t Ty.t -> node =
      fun ty ->
	try N.find nodes ty
	with Not_found ->
	  let node = create  ty in
	  ignore (N.add nodes ty node);
	  node



    let rec links:
    type a b. (a,b) fn -> node -> unit =
      fun fd tgt ->
	match fd with
	| Fun (src,fd) ->
	  link (node src) tgt;
	  links fd tgt
	| Constant src ->
	  link (node src) tgt
    ;;

    (** Build a static graph from a signature *)
    let graph s =
      List.iter (fun (id,e) ->
	match e with
	| Sig.Elem (fd,_) ->
	  let tgt = node (codom fd) in
	  links fd (tgt);
	  tgt.constructors <- (id,e) :: tgt.constructors
      ) s

    let rec eval :
    type a b.  (a,b) fn -> a -> b list =
      fun  fd f ->
	match fd with
	| Constant _ -> [f]
	| Fun (ty,fd) -> (PSet.elements ty.Ty.enum) >>= fun e -> eval fd (f e)

    module Workset = struct

      let create () = Queue.create ()
      let add s x = Queue.push x s
      let repeat f s =
	while not (Queue.is_empty s) do
	  let n = Queue.pop s in
	      f n
	done
    end

    let workset = Workset.create ()

    let update node =
      match node.descr with Descr ty ->
	if not (Ty.full ty)
	then
	  let updated =
	    List.fold_left (fun updated (_,e) ->
	      match e with
	      | Sig.Elem (fd,f) ->
		let ty = codom fd in
		let l = eval fd f in
		updated || Ty.merge ty (l)
	    ) false node.constructors
	  in
	  if updated
	  then List.iter (Workset.add workset) (successors node)

    let check s =
      graph s;
      List.iter (fun (_,Sig.Elem (fd,_)) -> Workset.add workset (node (codom fd))) s;
      Workset.repeat update workset;


  end
  let check = Graph.check

end

(** This is the function that you want to use: take the description of a module
 * signature, then iterate [n] times to generate elements for all the types in
 * the module. *)

let check s = Fun.check s

(* -------------------------------------------------------------------------- *)

(** {2 Examples } *)

(** {3 Sorted integer lists } *)

module SIList = struct
  type t = int list

  let empty = []

  let rec add x = function
    | [] -> [x]
    | t::q -> if t < x then t :: add x q else x::t::q

  let pp l = Printf.sprintf "[%s]" (String.concat ";" (List.map string_of_int l))

end

(** The description of the type of sorted integer lists. Elements of this type
 * can be compared using the polymorphic, structural comparison operator (=). *)
let si_t : SIList.t ty = Ty.declare ()

(** Conversely, [int] is a ground type that can not only be compared with (=),
 * but also admits a generator. *)
let int_t : int ty = Ty.declare ~fresh:(fun _ -> Random.int 10) ()

(** Populate the descriptor of the built-in type [int]. *)
let () =
  Ty.populate 10 int_t

(** Use module [Sig] to build a description of the signature of [SIList]. *)
let silist_sig = Sig.([
  val_ "empty" (returning si_t) SIList.empty;
  val_ "add" (int_t @-> si_t @-> returning si_t) SIList.add;
])

(** Generate instances of [SIList.t]. *)
let () =
  check silist_sig

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
let () = Ty.populate 5 int_t

let rbt_sig = Sig.([
  val_ "empty" (returning rbt_t) RBT.empty;
  val_ "insert" (int_t @-> rbt_t @-> returning rbt_t) RBT.insert;
])

let () = check  rbt_sig

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

let () = check zip_sig

let () =
  let prop = function
    | None -> true
    | Some v -> RBT.is_balanced v in
  assert (Ty.counter_example rbtopt_t prop = None)
