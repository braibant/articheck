module E = struct
  type t = int
  let compare = Pervasives.compare
  let hash = Hashtbl.hash
end

module ES = Set.Make(E)
module ESS = Set.Make(ES)

module Zdd = struct

  type uid = int
  type var = E.t
  type expr =
    | Bot 				(* {} *)
    | Top 				(* {{}} *)
    | Node of uid * expr * expr * var

  let uid = function
    | Bot -> 0
    | Top -> 1
    | Node (uid,_,_,_) -> uid

  module H = struct
    type t = expr

      (** The hash-function on ZDD nodes must return in O(1)
	  time. Therefore, it is not recursive. *)
    let hash = function
      | Top -> 0
      | Bot -> 1
      | Node (_,l,r,v) ->
	let (+) x y = x lsl 8 lxor y in
	(uid l + uid r + E.hash v) land max_int

      (** The equality function on ZDD nodes is not recursive
	  either. It relies on the fact that sub-nodes are hash-consed,
	  and thus, we have the maximal sharing property: [==] holds iff
	  [=] holds. *)
    let equal x y = match x,y with
      | Top, Top | Bot, Bot -> true
      | Node (_,l1,r1,v1), Node (_,l2,r2,v2) -> l1 == l2 && r1 == r2 && E.compare v1 v2 = 0
      | _,_ -> false
  end

    (** WHS implements weak hash-sets for H *)
  module WHS = Weak.Make(H)

    (** Use a global counter for the generation of unique identifiers.   *)
  let counter = ref 2;;

    (** Use a global hash-consing table  *)
  let table = WHS.create 1337;;

  let top = Top
  let bot = Bot

    (** [node l r v] is a smart node-constructor. It enforces the
	maximal sharing property, and the fact that the right child of a
	node is never Bot *)
  let node l r v =
    if r = Bot then l
    else
      let o1 = Node (!counter,l,r,v) in
      let o2 = WHS.merge table o1 in
      if o1 == o2 then (incr counter);
      o2

    (** Since all expressions are endowed with the maximal sharing
	property, we can use physical equality rather for semantic
	equality.  *)
  let equal (x: expr) (y: expr) = x == y

    (** We can also equip expressions with a O(1) comparison function,
	based on uids.  *)
  let compare x y = Pervasives.compare (uid x) (uid y)


    (** Now, we turn to memoizing constructs. We build the module [H1]
	(resp. [H2]) as instances of hash-tables that are used to tabulate
	the recursive calls of operations on ZDDs.  *)
  module N1 = struct
    type t = expr
    let hash x = uid x
    let equal x y = x == y
  end

  module H1 = Hashtbl.Make(N1)

  module N2 = struct
    type t = expr * expr
    let hash (x,y) = ((uid x lsl 8) lxor uid y) land max_int

    let equal (x1,y1) (x2,y2) = equal x1 x2 && equal y1 y2
  end

  module H2 = Hashtbl.Make(N2)

  (** The size of the initial hash-consing cache. Note that this
      value is not that important, because hash-tables are
      redimensionned as needed.  *)
  let cache_size = 1337

  (** Memoizing combinator for functions over one expression *)
  let memo_rec1 (f: (expr -> 'a) -> (expr -> 'a)): expr -> 'a =
    let h = H1.create cache_size in
    let rec g x =
      try H1.find h x
      with Not_found ->
	let r = f g x in
	H1.add h x r;
	r
    in
    g

    (** Memoizing combinator for functions over two expression   *)
  let memo_rec2 (f: ((expr * expr) -> 'a) -> ((expr * expr) -> 'a)) : expr * expr -> 'a  =
    let h = H2.create cache_size in
    let rec g x =
      try H2.find h x
      with Not_found ->
	let r = f g x in
	H2.add h x r;
	r
    in
    g


    (** [denote x] builds the [ESS.t] that corresponds to one ZDD expression *)
  let denote (x: expr) : ESS.t =
    let denote denote = function
      | Top -> ESS.singleton ES.empty
      | Bot -> ESS.empty
      | Node (_,l,r,v) ->
	ESS.union (denote l) (ESS.fold (fun s acc -> ESS.add (ES.add v s) acc) (denote r) ESS.empty)
    in
    memo_rec1 denote x

  let singleton (s: ES.t) : expr =
    let l = ES.elements s in
    let rec aux = function
      | [] -> Top
      | h::t -> node Bot (aux t) h
    in aux l

  let union =
    let union union : expr * expr -> expr = function
      | Top, Top -> Top
      | Top, Node (_,l,r,v)
      | Node (_,l,r,v),Top -> node (union (l,Top)) r v
      | Bot, x | x, Bot -> x
      | (Node (_,l1,r1,v1) as n1) , (Node (_,l2,r2,v2) as n2) ->
	match E.compare v1 v2 with
	  | 0 ->
	    node (union (l1,l2)) (union (r1,r2)) v1
	  | -1 ->  			(* v1 < v2 *)
	    node (union (l1,n2)) r1 v1
	  | _ ->
	    node (union (n1,l2)) r2 v2
    in
    fun x y -> memo_rec2 union (x,y)

  let inter =
    let inter inter : expr * expr -> expr = function
      | Bot, _ | _, Bot -> Bot
      | Top, Top -> Top
      | Node (_,l,_,_), Top | Top, Node (_,l,_,_) -> inter (l,Top)
      | (Node (_,l1,r1,v1) as n1) , (Node (_,l2,r2,v2) as n2) ->
	match E.compare v1 v2 with
	  | 0 ->
	    node (inter (l1,l2)) (inter (r1,r2)) v1
	  | -1 ->  			(* v1 < v2 *)
	    inter (n2,l1)
	  | _ ->
	    inter (n1,l2)
    in
    fun x y -> memo_rec2 inter (x,y)

  let xor =
    let xor xor : expr * expr -> expr = function
      | Bot, Bot | Top, Top -> Bot
      | Bot, x | x, Bot -> x
      | Node (_,l,r,v), Top | Top, Node (_,l,r,v) -> node (xor (l,Top)) r  v
      | (Node (_,l1,r1,v1) as n1) , (Node (_,l2,r2,v2) as n2) ->
	match E.compare v1 v2 with
	  | 0 ->
	    node (xor (l1,l2)) (xor (r1,r2)) v1
	  | -1 ->  			(* v1 < v2 *)
	    node (xor (l1,n2)) r1 v1
	  | _ ->
	    node (xor (n1,l1)) r2 v2
    in
    fun x y -> memo_rec2 xor (x,y)


  let fold (f: ES.t -> 'a -> 'a) (zdd: expr) (acc: 'a) : 'a =
    let rec aux s acc = function
      | Bot -> acc
      | Top -> f s acc
      | Node (_,l,r,v) ->
	aux (ES.add v s) (aux s acc l) r
    in
    aux ES.empty acc zdd

    (** [subset x y] holds if all elements of [x] are included in [y]  *)
  let subset =
    let subset subset = function
      | Bot, _ -> true
      | Top, Bot -> false
      | Top, _ -> (* the rightmost leaf of y cannot be [Bot] *)
	true
      | (Node (_,l1,r1,v1) as n1), Node (_,l2,r2,v2) ->
	begin match E.compare v1 v2 with
	  | 0 ->
	    subset (l1,l2) && subset (r1,r2)
	  | -1 -> false
	  | _ -> subset (n1,l2)
	end
      | Node (_,_,_,_), Top
      |  Node (_,_,_,_), Bot -> false
    in
    fun x y -> memo_rec2 subset (x,y)

  let is_empty = function Bot -> true | _ -> false

  let mem (e: ES.t) (zdd: expr) =
    let rec aux e zdd =
      match e, zdd with
	| [], Bot -> false
	| [], Top -> true
	| [], Node (_,l,_,_) -> aux [] l
	| (t::q as e), Node (_,l,r,v) ->
	  begin match E.compare t v with
	    | 0 -> aux q r
	    | -1 -> false
	    | _ -> aux e l
	  end
	| _, _ -> false
    in
    aux (ES.elements e) zdd


  let add e zdd =
    union (singleton e) zdd

  let empty =
    Bot
end
