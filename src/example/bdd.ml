module BDD : sig
  type t
  type var = int
  val zero:t
  val one:t
  val mk_and : t -> t -> t
  val mk_or  : t -> t -> t
  val mk_not : t -> t
  val mk_xor : t -> t -> t
  val mk_var: var -> t

  val compare : t -> t -> int
  val equal   : t -> t -> bool
  (* invariant on the data-structure *)
  val robdd  : t -> bool
end = struct

  type var = int

  type uid = int

  type expr =
    | Zero
    | One
    | Node of var * expr * expr * uid

  type t = expr

  let zero = Zero
  let one = One

  let uid = function
    | Zero -> 0
    | One  -> 1
    | Node (_,_,_,uid) -> uid


  module T = struct
    (* In this module, we do not have maximal sharing yet. *)
    type t = expr

    let hash = function
      | Zero -> 0
      | One  -> 1
      | Node (v,l,h,_) ->
	(v + uid l * 3 + uid h * 5) land max_int

    let equal x y =
      match x, y with
	| One, One | Zero, Zero -> true
	| Node (v1,l1,h1,_), Node (v2,l2,h2,_) ->
	  v1 = v2
	  && uid l1 == uid l2
	  && uid h1 == uid h2
	| _,_ -> false
  end

  module WHT = Weak.Make(T)

  let table = WHT.create 1337
  let counter = ref 2

  let rec pp = function
    | One -> "1"
    | Zero -> "0"
    | Node (v,l,h,id) -> Printf.sprintf "(%i ? %s : %s)@[%i]" v (pp l) (pp h) id

  let _ = ignore (pp)

  (* all nodes must be constructed using this function, which will enforce the maximal sharing property *)
  let mk_node v ~low ~high =
    if low == high
    then low
    else
      begin
      	let o1 = Node (v,low,high,!counter) in
      	let o2 = WHT.merge table o1 in
      	if o1 == o2
      	then (incr counter; o1)
      	else o2
      end

  let equal x y = x == y
  let compare x y = Pervasives.compare (uid x) (uid y)
  let hash = uid

  module H1 = Hashtbl.Make(
    struct
      type t = expr
      let equal = equal
      let hash = hash
    end)

  (* The cache is created once for each top-level call of [memo_rec1 f] *)
  let memo_rec1 f =
    let h = H1.create 513 in
    let rec g x =
      try H1.find h x
      with Not_found -> f g x
    in
    fun x ->  g x

  module H2 = Hashtbl.Make(struct
    type t = expr * expr
    let equal x y = fst x == fst y && snd x == snd y
    let hash x = Hashtbl.hash (uid (fst x), uid (snd x))
  end)

  (* The cache is created once for each top-level call of [memo_rec2 f] *)
  let memo_rec2 f =
    let h = H2.create 513 in
    let rec g x =
      try H2.find h x
      with Not_found -> f g x
    in
    fun x y -> g (x,y)

  let mk_and =
    let mk_and (mk_and: (expr * expr) -> expr) (x,y) =
      match x, y with
	| One, e | e, One -> e
	| Zero, _ | _, Zero -> Zero
	| (Node (v1,l1,h1,_) as n1) , (Node (v2,l2,h2,_) as n2) ->
	  if v1 = v2 then mk_node v1 ~low:(mk_and (l1,l2)) ~high:(mk_and (h1,h2))
	  else if v1 < v2 then mk_node v1 ~low:(mk_and (l1,n2)) ~high:(mk_and (h1,n2))
	  else mk_node v2 ~low:(mk_and (n1,l2)) ~high:(mk_and (n1,h2))
    in
    memo_rec2 mk_and;;

  let mk_or =
    let mk_or (mk_or: (expr * expr) -> expr) (x,y) =
      match x, y with
	| One, _ | _, One -> One
	| Zero, e | e, Zero -> e
	| (Node (v1,l1,h1,_) as n1) , (Node (v2,l2,h2,_) as n2) ->
	  if v1 = v2 then mk_node v1 ~low:(mk_or (l1,l2)) ~high:(mk_or (h1,h2))
	  else if v1 < v2 then mk_node v1 ~low:(mk_or (l1,n2)) ~high:(mk_or (h1,n2))
	  else mk_node v2 ~low:(mk_or (n1,l2)) ~high:(mk_or (n1,h2))
    in
    memo_rec2 mk_or;;

  let mk_not =
    let mk_not mk_not x =
      match x with
	| One -> Zero
	| Zero -> One
	| Node (v,l,h,_) ->
	  mk_node v (mk_not l) (mk_not h)
    in
    memo_rec1 mk_not

  let mk_xor =
    let mk_xor (mk_xor: (expr * expr) -> expr) (x,y) =
      match x, y with
	| One, e | e, One -> mk_not e
	| Zero, e | e, Zero -> e
	| (Node (v1,l1,h1,_) as n1) , (Node (v2,l2,h2,_) as n2) ->
	  if v1 = v2 then mk_node v1 ~low:(mk_xor (l1,l2)) ~high:(mk_xor (h1,h2))
	  else if v1 < v2 then mk_node v1 ~low:(mk_xor (l1,n2)) ~high:(mk_xor (h1,n2))
	  else mk_node v2 ~low:(mk_xor (n1,l2)) ~high:(mk_xor (n1,h2))
    in
    memo_rec2 mk_xor;;


  let mk_var v = mk_node v ~low:Zero ~high:One

  (* invariants *)
  let var = function
    | Node (v,_,_,_) -> v
    | _ -> max_int


  let ordered x =
    let ordered ordered =function
      | Node (v,l,h,_) -> v < var l && v < var h && ordered l && ordered h
      | _ -> true
    in
    memo_rec1 ordered x

  let reduced x =
    let reduced reduced = function
      | Node (_,l,h,_) -> not (l == h) && reduced l && reduced h
      | _ -> true
    in
    memo_rec1 reduced x

  let robdd x = reduced x && ordered x
end

open Arti

let bdd_t : BDD.t ty = Ty.declare ~cmp:(BDD.compare) ~ident:"bdd" ()
let var_t : int ty   = Ty.declare ~ident:"var" ~fresh:(fun _ -> Random.int 10) ()
let () = Ty.populate 10 var_t

let bdd_sig = Sig.([
  val_ "zero" (returning bdd_t) BDD.zero;
  val_ "one" (returning bdd_t) BDD.one;
  val_ "mk_or" (bdd_t @-> bdd_t @-> returning bdd_t) BDD.mk_or;
  val_ "mk_and" (bdd_t @-> bdd_t @-> returning bdd_t) BDD.mk_and;
  val_ "mk_not" (bdd_t @-> returning bdd_t) BDD.mk_not;
  val_ "mk_xor" (bdd_t @-> bdd_t @-> returning bdd_t) BDD.mk_xor;
  val_ "mk_var" (var_t @-> returning bdd_t) BDD.mk_var
])

let () =
  Printf.eprintf "populating sig\n%!";
  Sig.populate bdd_sig;
  Printf.eprintf "populated sig\n%!"

let () = assert (Ty.counter_example "bdd reduced-ordered" bdd_t BDD.robdd = None)
