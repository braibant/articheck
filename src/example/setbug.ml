module Set : sig
  type t
  val check : t -> bool
  val add: int -> t -> t
  val union: t -> t -> t
  val empty : t
end
  = struct

    type elt = int
    type t = Empty
	     | Node of t * elt * t * int

(* Sets are represented by balanced binary trees (the heights of the
   children differ by at most 2 *)

    let height = function
    Empty -> 0
      | Node(_, _, _, h) -> h

(* Creates a new node with left son l, value x and right son r.
   l and r must be balanced and | height l - height r | <= 2.
   Inline expansion of height for better speed. *)

    let create l x r =
      let hl = match l with Empty -> 0 | Node(_,_,_,h) -> h in
      let hr = match r with Empty -> 0 | Node(_,_,_,h) -> h in
      Node(l, x, r, (if hl >= hr then hl + 1 else hr + 1))

(* Same as create, but performs one step of rebalancing if necessary.
   Assumes l and r balanced.
   Inline expansion of create for better speed in the most frequent case
   where no rebalancing is required. *)

    let bal l x r =
      let hl = match l with Empty -> 0 | Node(_,_,_,h) -> h in
      let hr = match r with Empty -> 0 | Node(_,_,_,h) -> h in
      if hl > hr + 2 then begin
	match l with
            Empty -> invalid_arg "Set.bal"
	  | Node(ll, lv, lr, _) ->
            if height ll >= height lr then
              create ll lv (create lr x r)
            else begin
              match lr with
		  Empty -> invalid_arg "Set.bal"
		| Node(lrl, lrv, lrr, _)->
		  create (create ll lv lrl) lrv (create lrr x r)
            end
      end else if hr > hl + 2 then begin
	match r with
            Empty -> invalid_arg "Set.bal"
	  | Node(rl, rv, rr, _) ->
            if height rr >= height rl then
              create (create l x rl) rv rr
            else begin
              match rl with
		  Empty -> invalid_arg "Set.bal"
		| Node(rll, rlv, rlr, _) ->
		  create (create l x rll) rlv (create rlr rv rr)
            end
      end else
	  Node(l, x, r, (if hl >= hr then hl + 1 else hr + 1))

(* Same as bal, but repeat rebalancing until the final result is
   balanced. *)

    let rec join l x r =
      match bal l x r with
	  Empty -> invalid_arg "Set.join"
	| Node(l', x', r', _) as t' ->
	  let d = height l' - height r' in
	  if d < -2 || d > 2 then join l' x' r' else t'

(* Splitting *)

    let rec split x = function
    Empty ->
      (Empty, None, Empty)
      | Node(l, v, r, _) ->
	let c = compare x v in
	if c = 0 then (l, Some v, r)
	else if c < 0 then
	  let (ll, vl, rl) = split x l in (ll, vl, join rl v r)
	else
	  let (lr, vr, rr) = split x r in (join l v lr, vr, rr)

(* Implementation of the set operations *)

    let empty = Empty

    let rec add x = function
    Empty -> Node(Empty, x, Empty, 1)
      | Node(l, v, r, _) as t ->
	let c = compare x v in
	if c = 0 then t else
	  if c < 0 then bal (add x l) v r else bal l v (add x r)

    let rec union s1 s2 =
      match (s1, s2) with
	  (Empty, t2) -> t2
	| (t1, Empty) -> t1
	| (Node(l1, v1, r1, h1), Node(l2, v2, r2, h2)) ->
	  if h1 >= h2 then
            if h2 = 1 then add v2 s1 else begin
              let (l2, _, r2) = split v1 s2 in
              join (union l1 l2) v1 (union r1 r2)
            end
	  else
            if h1 = 1 then add v1 s2 else begin
              let (l1, _, r1) = split v2 s1 in
              join (union l1 l2) v2 (union r1 r2)
            end

    (* ---------------------------------------------------------------------- *)
    (* check for AVL invariant *)
    let check s =
      let rec check_rec = function
	| Empty ->
	  0
	| Node (l, _, r, h) ->
	  let hl = check_rec l in
	  let hr = check_rec r in
	  assert (h = max hl hr + 1);
	  assert (abs (hl - hr) <= 2);
	  h
      in
      try ignore (check_rec s); true
      with _ -> false
  end

open Arti

let set_t = atom (Ty.declare ~size:1500 () : Set.t ty)
let int_t =
  let ty : int ty = Ty.declare ~fresh:(fun _ -> Random.int 100000) () in
  Ty.populate 1000 ty;
  atom ty


let set_sig = Sig.([
  val_ "empty" (returning set_t) Set.empty;
  val_ "add" (int_t @-> set_t @-> returning set_t) Set.add;
  val_ "union" (set_t @-> set_t @-> returning set_t) Set.union;
])

let () = Sig.populate set_sig

let () =
  assert (counter_example "avl balanced" set_t Set.check = None)
