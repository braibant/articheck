open Arti

(** {3 Red-black trees } *)

module RBT : sig
  type 'a t
  val prop_no_red_red : 'a t -> bool
  val prop_balanced : 'a t -> bool
  val prop_ordered  : 'a t -> bool
  val prop_rb : 'a t -> bool

  val empty : 'a t
  val member : 'a -> 'a t -> bool
  val insert : 'a -> 'a t -> 'a t
  val delete : 'a -> 'a t -> 'a t
end
= struct

  type color = R | B | BB | NB

  type 'a t =
    | E                         (* black leaf *)
    | EE                        (* double black *)
    | T of color * 'a t * 'a * 'a t

  let rec prop_no_red_red = function
    | E -> true
    | EE -> assert false
    | T (R, T (R,_,_,_), _, _) -> false
    | T (R, _, _, T (R,_,_,_)) -> false
    | T (_, l, _, r) -> prop_no_red_red l && prop_no_red_red r

  let rec black_depth = function
    | E -> Some 1
    | EE -> assert false
    | T (R, l, _, r) ->
        begin match black_depth l, black_depth r with
          | Some n, Some m -> if n = m then Some n else None
          | _, _ -> None
        end
    | T (B, l, _, r) ->
        begin match black_depth l, black_depth r with
          | Some n, Some m -> if n = m then Some (succ n) else None
          | _, _ -> None
        end
    | T ((BB|NB),_,_,_) -> assert false

  let prop_balanced t = match black_depth t with
    | None -> false
    | Some _ -> true

  let rec prop_ordered_list = function
    | [] -> true
    | [_] -> true
    | x::y::tl -> x < y && prop_ordered_list (y::tl)

  let rec to_list acc = function
    | E -> acc
    | EE -> assert false
    | T (_, l, x, r) -> to_list (x::(to_list acc r)) l

  let to_list t = to_list [] t

  let prop_ordered t = prop_ordered_list (to_list t)

  let prop_rb t =
    prop_no_red_red t
    && prop_balanced t
    && prop_ordered t

  let redden = function
    | E -> invalid_arg "cannot redden empty tree"
    | EE -> invalid_arg "cannot redden empty tree"
    | T (_,a,x,b) -> T (R, a, x, b)

  let blacken = function
    | E -> E
    | EE -> E
    | T (_,a,x,b) -> T (B, a, x, b)

  let isBB = function
    | EE -> true
    | T (BB, _, _, _) -> true
    | _ -> false

  let blacker = function
    | NB -> R
    | R -> B
    | B -> BB
    | BB -> invalid_arg "too black"

  let redder = function
    | NB -> invalid_arg "not black enough"
    | R -> NB
    | B -> R
    | BB -> B

  (* let blacker' = function *)
  (*     E -> EE *)
  (*   | EE -> assert false *)
  (*   | T (c, l, x, r) -> T (blacker c, l, x, r) *)

  let redder' = function
    | EE -> E
    | E -> assert false
    | T (c, l, x, r) -> T (redder c, l, x, r)

  let rec balance color l x r =
    match color, l, x, r with
      (* Okasaki's cases *)
      | B,(T (R,(T (R,a,x,b)),y,c)),z,d -> T(R,(T (B,a,x,b)),y,(T (B,c,z,d)))
      | B,(T (R,a,x,(T (R,b,y,c)))),z,d -> T(R,(T (B,a,x,b)),y,(T (B,c,z,d)))
      | B,a,x,(T (R,(T (R,b,y,c)),z,d)) -> T(R,(T (B,a,x,b)),y,(T (B,c,z,d)))
      | B,a,x,(T (R,b,y,(T (R,c,z,d)))) -> T(R,(T (B,a,x,b)),y,(T (B,c,z,d)))

      (* 6 cases for deletion *)
      | BB,(T (R,(T (R,a,x,b)),y,c)),z,d -> T(B,(T (B,a,x,b)),y,(T (B,c,z,d)))
      | BB,(T (R,a,x,(T (R,b,y,c)))),z,d -> T(B,(T (B,a,x,b)),y,(T (B,c,z,d)))
      | BB,a,x,(T (R,(T (R,b,y,c)),z,d)) -> T(B,(T (B,a,x,b)),y,(T (B,c,z,d)))
      | BB,a,x,(T (R,b,y,(T (R,c,z,d)))) -> T(B,(T (B,a,x,b)),y,(T (B,c,z,d)))

      | BB,a,x, (T (NB, T (B,b,y,c), z, (T (B,_,_,_) as d))) ->
          T (B, T (B, a,x,b), y, balance B c z (redden d))
      | BB, T (NB, (T (B,_,_,_) as a),x, (T (B,b,y,c))),z,d ->
          T (B, balance B (redden a) x b, y, (T (B, c, z, d)))

      | color,a,x,b -> T (color, a, x, b)
  ;;

  let bubble color l x r =
    if isBB l || isBB r then balance (blacker color) (redder' l) x (redder' r)
    else balance color l x r


  let empty = E

  let rec member x = function
    | E -> false
    | EE -> assert false
    | T (_, l, y, r) ->
        let cmp = Pervasives.compare x y in
        if cmp = 0 then true
        else if cmp < 0 then member x l else member x r

  let rec insert x t =
    match t with
      | E -> T (R,E,x,E)
      | EE -> assert false
      | T (color,a,y,b) ->
          let cmp = compare x y in
          if cmp < 0 then balance color (insert x a) y b
          else if cmp > 0 then balance color a y (insert x b)
          else t


  let insert x t =
    blacken (insert x t)

  let rec max = function
    |E -> failwith "no maximum"
    | EE -> assert false
    | T (_,_,x,E) -> x
    | T (_,_,_,r) -> max r

  let rec remove_max = function
      E -> failwith "no maximum to remove"
    | EE -> assert false
    | T (_,_,_,E) as s -> remove s
    | T (color,l,x,r) -> bubble color l x (remove_max r)

  and remove = function
    | E -> E
    | EE -> assert false
    | T (R,E,_,E) -> E
    | T (B,E,_,E) -> EE
    | T (B, E, _, (T (R,a,x,b))) -> T (B, a, x, b)
    | T (B, T (R,a,x,b), _, E)   -> T (B, a, x, b)

    (* | T (color, (T (R,a,x,b) as l) , y, r)   -> *)
    (*     let mx = max l in *)
    (*     let l' = remove_max l in *)
    (*     bubble color l' mx r *)

    | T (color, l, _, r) ->
        let mx = max l in
        let l' = remove_max l in
        bubble color l' mx r

  let rec delete x s =
    match s with
      | E -> E
      | EE -> assert false
      | T (c,a,y,b) ->
          if x < y then bubble c (delete x a) y b
          else if x > y then bubble c a y (delete x b)
          else remove s

  let delete x s =
    blacken (delete x s)


end

let rbt_t = atom (Ty.declare ~ident:"rbt" () : int RBT.t ty)

let int_t =
  let ty : int ty = Ty.declare ~ident:"int" ~fresh:(fun _ -> Random.int 1000) () in
  Ty.populate 5 ty;
  atom ty

let rbt_sig = Sig.([
  val_ "empty" (returning rbt_t) RBT.empty;
  val_ "insert" (int_t @-> rbt_t @-> returning rbt_t) RBT.insert;
  val_ "delete" (int_t @-> rbt_t @-> returning rbt_t) RBT.delete;
])

let () = Sig.populate  rbt_sig

let () =
  assert (counter_example "rbt sorted" rbt_t RBT.prop_no_red_red = None);
  assert (counter_example "rbt balanced" rbt_t RBT.prop_balanced = None);
  assert (counter_example "rbt ordered" rbt_t RBT.prop_ordered  = None);
  assert (counter_example "rbt red-black" rbt_t RBT.prop_rb  = None);
  ()
