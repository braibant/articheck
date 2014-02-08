module Ty = struct
  type 'a t = {
    eq: 'a -> 'a -> bool;
    mutable enum : 'a list;
    fresh : ('a list -> 'a) option;
    invar : 'a -> bool;
    uid : int;
  }

  let mem x s =
    List.exists (fun y -> y = x) s.enum

  let add x s =
    if mem x s then () else s.enum <- x::s.enum

  let elements s = s.enum

  let gensym =
    let r = ref (-1) in
    fun () -> incr r; !r

  let declare eq = {
    eq;
    enum = [];
    fresh = None;
    invar = (fun _ -> true);
    uid = gensym ()
  }

  let finite eq enum =
    { (declare eq) with enum }

  (* generate a fresh type descriptor *)
  (* maybe we could remember what is the base type, so that if we run
     out of elements for the new type, we could generate new instances of
     the old one, and select the one that fulfill the invariant. *)
  let (/) ty invar =
    let invar x = invar x && ty.invar x in
    {ty with uid = gensym (); invar}

  (* tag a type with a generator, without generating a fresh type descriptor *)
  let (&) ty fresh =
    match ty.fresh with
      | None ->
	{ty with fresh = Some fresh}
      | Some _ ->
	invalid_arg "fresh"

  (** Check a property overall the elements of ['a ty] that were
      generated up to this point *)
  let counter_example ty f =
    try Some (List.find (fun e -> not (f e)) ty.enum)
    with Not_found -> None
end

type 'a ty = 'a Ty.t

type (_,_) fn =
| Constant : 'a ty -> ('a,'a) fn
| Fun    : 'a ty * ('b, 'c) fn -> ('a -> 'b, 'c) fn;;

let (@->) ty fd = Fun (ty,fd)
let returning ty = Constant ty

let (>>=) li f = List.flatten (List.map f li)

let rec eval : type a b. (a,b) fn -> a -> b list =
  let open Ty in
  fun fd f ->
    match fd with
    | Constant ty -> [f]
    | Fun (ty,fd) -> ty.enum >>= fun e -> eval fd (f e)

let rec codom : type a b. (a,b) fn -> b ty =
  function
    | Fun (_,fd) -> codom fd
    | Constant ty -> ty

let blows_after_n exn n =
  let count = ref 0 in
  fun () ->
    incr count;
    if !count > n then raise exn

let use fd f =
  let prod = eval fd f in
  let ty = codom fd in
  let tick = blows_after_n Exit 1000 in
  (* [Gabriel] I had to use this for ncheck to terminate in finite
     time on large signatures *)
  try List.iter (fun x -> tick (); Ty.add x ty) prod;
  with Exit -> ()

let populate n ty =
  let open Ty in
  match ty.fresh with
    | None -> invalid_arg "populate"
    | Some fresh ->
      for i = 0 to n - 1 do
        Ty.add (fresh ty.enum) ty
      done

module Sig = struct
  type elem = Elem : ('a,'b) fn * 'a -> elem

  type ident = string
  type t = (ident * elem) list

  let val_ id fd f = (id, Elem (fd, f))
end

let ncheck n (s: Sig.t) =
  for i = 1 to n do
    List.iter (fun (_id, Sig.Elem (fd, f)) -> use fd f) s;
  done

(* Example: Sorted integer lists *)
module SIList = struct
  type t = int list

  let empty = []

  let rec add x = function
    | [] -> [x]
    | t::q -> if t < x then t :: add x q else x::t::q
end

let si_t : SIList.t ty = Ty.(declare (=))
let int_t : int ty = Ty.(declare (=) & (fun _ -> Random.int 1000))
let () = populate 10 int_t

let silist_sig = Sig.([
  val_ "empty" (returning si_t) SIList.empty;
  val_ "add" (int_t @-> si_t @-> returning si_t) SIList.add;
])

let () =  ncheck 5 silist_sig

let () =
  let prop s = List.sort Pervasives.compare s = s in
  assert (Ty.counter_example si_t prop = None);
  ()


module type RBT = sig
  (* private types to enforce abstraction
     but keep pretty-printing in the toplevel *)
  type color = private R | B
  type 'a t = private
  | Empty
  | T of color * 'a t * 'a * 'a t

  val empty : 'a t
  val insert : 'a -> 'a t -> 'a t
  val elements : 'a t -> 'a list
  val is_balanced : 'a t -> bool

  (* public type, part of the user interface for the 'move' function *)
  type direction = Left | Right
  type 'a zipper
  type 'a pointer = 'a t * 'a zipper

  val zip_open : 'a t -> 'a pointer
  val zip_close : 'a pointer -> 'a t

  val move_up : 'a pointer -> 'a pointer option
  val move : direction -> 'a pointer -> 'a pointer option
end

module RBT : RBT  = struct
  type color = R | B
  type 'a t =
  | Empty
  | T of color * 'a t * 'a * 'a t

  let empty = Empty
  let rec mem x = function
    | Empty -> false
    | T (_col,l,v,r) ->
      begin
	match compare x v with
	| -1 -> mem x l
	| 0 -> true
	| _ -> mem x r
      end

  let blacken = function
    | T (R, l,v,r) -> T (B, l,v,r)
    | (Empty | T (B, _, _, _)) as n -> n

  let balance = function
    | T (B, (T (R, T (R, a, x, b), y, c       )
                 | T (R, a, x, T (R, b, y, c))), z, d)
    | T (B, a, x, (T (R, T (R, b, y, c), z, d)
                 | T (R, b, y, T (R, c, z, d))))
      -> T (R, T (B, a, x, b), y, T (B, c, z, d))
    | n -> n

  let insert x n =
    let rec insert x = function
      | Empty -> T (R, Empty, x, Empty)
      | T (col, l,v,r) ->
        let l, r =
          if x <= v
          then insert x l, r
          else l, insert x r in
        balance (T (col, l, v, r))
    in blacken (insert x n)

  let rec elements = function
    | Empty -> []
    | T (_col,l,v,r) -> elements l @ (v::elements r)

  let is_black = function
    | T (R, _, _, _) -> false
    | Empty | T (B, _, _, _) -> true

(* http://en.wikipedia.org/wiki/Red-black_tree, simplified:

  In addition to the requirements imposed on a binary search tree the
  following must be satisfied by a red–black tree:

  - The root is black.
  - Every red node must have two black child nodes.
  - Every path from a given node to any of its descendant leaves
    contains the same number of black nodes.
*)
  let is_balanced t =
      let rec check_black_height = function
        | Empty -> 0
        | T (col, l, _, r) ->
          let bhl = check_black_height l in
          let bhr = check_black_height r in
          if bhl <> bhr then raise Exit;
          bhl + (match col with B -> 1 | R -> 0)
      in
    try
      ignore (check_black_height t);
      is_black t
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
      | {dir = Left; col; v; sibling} -> T (col, t, v, sibling)
      | {dir = Right; col; v; sibling} -> T (col, sibling, v, t) in
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
    | T (col, l, v, r) ->
      match dir with
        | Left -> Some (l, {dir; col; v; sibling = r})
        | Right -> Some (r, {dir; col; v; sibling = l})

  let move dir (t, zip) =
    match move_frame dir t with
      | None -> None
      | Some (t, frame) -> Some (t, frame::zip)
end

let rbt_t : int RBT.t ty = Ty.(declare (=))
let int_t : int ty = Ty.(declare (=) & (fun _ -> Random.int 10))
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

let dir_t : RBT.direction ty = Ty.finite (=) RBT.([Left; Right])
let rbtopt_t : int RBT.t option ty = Ty.(declare (=))
let ptropt_t : int RBT.pointer option ty = Ty.(declare (=))

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

  val_ "read" (ptropt_t @-> returning rbtopt_t)
    (function None -> None | Some (t, _zip) -> Some t);

  val_ "write" (ptropt_t @-> rbtopt_t @-> returning ptropt_t)
    (fun ptr t -> match ptr, t with
      | None, _ | _, None -> None
      | Some (_, zip), Some t -> Some (t, zip));
]))

let () = ncheck 1 zip_sig

let () =
  let prop = function
    | None -> true
    | Some v -> RBT.is_balanced v in
  assert (Ty.counter_example rbtopt_t prop = None)
