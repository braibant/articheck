open Arti

module AVL = struct
  type 'a t =
  | L
  | N of 'a t * 'a * 'a t * int

  let empty = L

  let rec real_height = function
    | L -> 0
    | N (l, _, r, _) -> 1 + max (real_height l) (real_height r)

  let height = function
    | L -> 0
    | N (_,_,_,h) as t ->
      assert (0 < h);
      assert (real_height t = h);
      h

  let mk_node l v r =
    N (l,v,r, 1 + max (height l) (height r))

  let rotate_left = function
    | N (a,p, N (b,q,c,_), _) ->
      mk_node (mk_node a p b) q c
    | _ -> assert false

  let rotate_right = function
    | N (N (a,p,b,_),q, c,_) ->
      mk_node a p (mk_node b q c)
    | _ -> assert false

  let balance_factor = function
    | N (l,_,r,_) -> height l - height r
    | L -> 0

  let balance l a r =
    assert (abs (height l - height r) <= 2);
    if abs (height l - height r) <= 1
    then  mk_node l a r
    else (* imbalance is two: we need to rebalance *)
      if height l - height r = 2
      then (* too many elements on the left subtree *)
        match l with
        | L -> assert false
        | N (ll,lv,lr,_) ->
            if balance_factor ll = (-1)
            then rotate_right (N (mk_node (rotate_left ll) lv lr,a,r,-1))
            else rotate_right (N (l,a,r,-1))
      else (* too many elements on the right subtree *)
        match r with
        | L -> assert false
        | N (rl,rv,rr,_) ->
          if balance_factor rr = 1
          then rotate_left (N (l,a,mk_node rl rv (rotate_left rr), -1))
          else rotate_left (N (l,a,r,-1))

  let rec insert x = function
    | L -> mk_node L x L
    | N (l,v,r,h) as t ->
      if x < v
      then balance (insert x l) v r
      else if x > v
      then balance l v (insert x r)
      else t

  let rec elements = function
    | L -> []
    | N (l,v,r,_) ->
        elements l @ (v::elements r)

  let rec pp = function
    | L -> "."
    | N (l,v,r,_) -> Printf.sprintf "(%s,%i,%s)" (pp l) v (pp r)

  let is_balanced t =
    let rec check_height = function
      | L -> 0
      | N (l,v,r,h) ->
        let hl = check_height l in
        let hr = check_height r in
        assert (h = 1 + max hl hr);
        assert (abs (hl - hr) <= 1);
        h
    in
    try ignore (check_height t); true
    with e ->
      Printf.eprintf "%s\n" (Printexc.to_string e);
      Printexc.print_backtrace stderr;
      Printf.eprintf "The exception above was raised by the following graph:\
        \n  %s\n" (pp t);
      false



end

let avl_t : int AVL.t ty = Ty.declare ()
let int_t : int ty = Ty.declare ~fresh:(fun _ -> Random.int 10) ()
let () = Ty.populate 5 int_t


let avl_sig = Sig.([
  val_ "empty" (returning avl_t) AVL.empty;
  val_ "insert" (int_t @-> avl_t @-> returning avl_t) AVL.insert;
])

let () = Sig.populate  avl_sig

let () =
  let prop s = let s = AVL.elements s in List.sort Pervasives.compare s = s in
  assert (Ty.counter_example "avl sorted" avl_t prop = None);
  assert (Ty.counter_example "avl balanced" avl_t AVL.is_balanced = None);
  ()
