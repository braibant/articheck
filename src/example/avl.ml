open Arti.Sample

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
            if balance_factor l = (-1)
            then (* Symmetrical of Case 2 *)
              match lr with
              | L -> assert false
              | N (lrl, lrv, lrr, _) ->
                  mk_node (mk_node ll lv lrl) lrv (mk_node lrr a r)
            else (* Symmetrical of Case 1 *)
              mk_node ll lv (mk_node lr a r)
      else (* too many elements on the right subtree *)
        match r with
        | L -> assert false
        | N (rl,rv,rr,_) ->
            if balance_factor r = 1
            then (* Case 2 of Knuth *)
              match rl with
              | L -> assert false
              | N (rll, rlv, rlr, _) ->
                  mk_node (mk_node l a rll) rlv (mk_node rlr rv rr)
            else (* Case 1 of Knuth *)
              mk_node (mk_node l a rl) rv rr


  let rec insert x = function
    | L -> mk_node L x L
    | N (l,v,r,_) as t ->
      if x < v
      then balance (insert x l) v r
      else if x > v
      then balance l v (insert x r)
      else t

  let rec find_min = function
    | L -> assert false
    | N (L, v, L, _) ->
        v
    | N (l, _, r, _) ->
        min (find_min l) (find_min r)

  let rec find_max = function
    | L -> assert false
    | N (L, v, L, _) ->
        v
    | N (l, _, r, _) ->
        max (find_max l) (find_max r)

  let rec remove k = function
    | L -> L
    | N (l, v, r, _) ->
        if k < v then
          balance (remove k l) v r
        else if k > v then
          balance l v (remove k r)
        else (* k = v *)
          match l, r with
          | L, L ->
              L
          | N _, _ ->
              let m = find_max l in
              balance (remove m l) m r
          | _, N _ ->
              let m = find_min l in
              balance l m (remove m r)

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
      | N (l,_,r,h) ->
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

let avl_t = atom(Ty.declare () : int AVL.t ty)
let int_t =
  let ty : int ty = Ty.declare ~fresh:(fun _ -> Random.int 1000) () in
  Ty.populate 5 ty;
  atom ty

let avl_sig = Sig.([
  val_ "empty" (returning avl_t) AVL.empty;
  val_ "insert" (int_t @-> avl_t @-> returning avl_t) AVL.insert;
  val_ "remove" (int_t @-> avl_t @-> returning avl_t) AVL.insert;
])

let () = Sig.populate  avl_sig

let () =
  let prop s = let s = AVL.elements s in List.sort Pervasives.compare s = s in
  assert (counter_example "avl sorted" avl_t prop = None);
  assert (counter_example "avl balanced" avl_t AVL.is_balanced = None);
  ()
