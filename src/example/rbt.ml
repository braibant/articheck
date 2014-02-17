open Arti

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
let int_t : int ty = Ty.declare ~fresh:(fun _ -> Random.int 1000) ()
let () = Ty.populate 5 int_t

let rbt_sig = Sig.([
  val_ "empty" (returning rbt_t) RBT.empty;
  val_ "insert" (int_t @-> rbt_t @-> returning rbt_t) RBT.insert;
])

let () = Sig.populate  rbt_sig

let () =
  let prop s = let s = RBT.elements s in List.sort Pervasives.compare s = s in
  assert (Ty.counter_example "rbt sorted" rbt_t prop = None);
  assert (Ty.counter_example "rbt balanced" rbt_t RBT.is_balanced = None);
  ()

let dir_t : RBT.direction ty = Ty.declare ~initial:RBT.([Left; Right]) ()
let rbtopt_t : int RBT.t option ty = Ty.declare ()
let ptropt_t : int RBT.pointer option ty = Ty.declare ()

let zip_sig =
  let open RBT in
  Sig.(rbt_sig @
	 [
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
	 ])

let () = Sig.populate zip_sig

let () =
  let prop = function
    | None -> true
    | Some v -> RBT.is_balanced v in
  assert (Ty.counter_example "rbt balanced" rbtopt_t prop = None)
