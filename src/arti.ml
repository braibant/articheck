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
  let for_all ty f =
    List.for_all f ty.enum
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

let use fd f =
  let prod = eval fd f in
  let ty = codom fd in
  List.iter (fun x -> Ty.add x ty) prod;
  ()

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
  assert (Ty.for_all si_t prop);
  ()


module RBT = struct

  type key = int 
  type t = | Red of t * key * t 
	   | Black of t * key  * t
	   | Empty

	       
  let empty = Empty
  let rec mem x = function
    | Empty -> false
    | Black (l,v,r) | Red (l,v,r) -> 
      begin
	match compare x v with
	| -1 -> mem x l 
	| 0 -> true
	| _ -> mem x r
      end

  let black = function 
    | Red (l,v,r) -> Black (l,v,r) 
    | n -> n

  let balance = function
    | Black (Red (Red (t1,x1,t2), x2, t3), x3, t4) ->
      Red (Black (t1, x1, t2) , x2, Black (t3, x3, t4))
    | Black (Red (t1,x1, Red (t2,x2,t3)), x3, t4) ->
      Red( Black (t1, x1, t2), x2, Black(t3, x3, t4))
    | Black (t1, x1, Red (t2, x2, Red (t3, x3, t4))) ->
      Red (Black (t1,x1,t2),x2, Black (t3,x3,t4))
    | Black (t1, x1, Red (Red (t2,x2,t3), x3, t4)) ->
      Red (Black (t1,x1, t2), x2, Black (t3,x3,t4)) 
    | n -> n

  let rec insert x = function 
    | Empty -> Red (Empty, x, Empty)
    | Red (l,v,r) -> 
      if x <= v 
      then (Red (insert x l, v, r))
      else (Red (l, v, insert x r))
    | Black (l,v,r) -> 
      if x <= v 
      then balance (Black (insert x l, v, r))
      else balance (Black (l, v, insert x r))
    
  let insert x n = black (insert x n) 
  
  let rec elements = function 
    | Empty -> []
    | Black (l,v,r) -> elements l @ (v::elements r)
    | Red (l,v,r) -> elements l @ (v::elements r)      

  let is_black = function
    | Red _ -> false
    | Empty | Black _ -> true


(* http://en.wikipedia.org/wiki/Red-black_tree, simplified:

  In addition to the requirements imposed on a binary search tree the
  following must be satisfied by a red–black tree:

  - The root is black.
  - Every red node must have two black child nodes.
  - Every path from a given node to any of its descendant leaves
    contains the same number of black nodes.
*)
  let is_balanced t =
      let rec black_height = function
        | Empty -> 0
        | Black (l, _, r) ->
          let bhl = black_height l in
          let bhr = black_height r in
          if bhl <> bhr then raise Exit;
          bhl + 1
        | Red (l, _, r) ->
          if not (is_black l && is_black r) then raise Exit;
          let bhl = black_height l in
          let bhr = black_height r in
          if bhl <> bhr then raise Exit;
          bhl
      in
    try
      if not (is_black t) then raise Exit;
      ignore (black_height t);
      true
    with Exit -> false
end



let rbt_t : RBT.t ty = Ty.(declare (=))
let int_t : int ty = Ty.(declare (=) & (fun _ -> Random.int 10))
let () = populate 5 int_t

let rbt_sig = Sig.([
  val_ "empty" (returning rbt_t) RBT.empty;
  val_ "insert" (int_t @-> rbt_t @-> returning rbt_t) RBT.insert;
])

let () =  ncheck 5 rbt_sig

let () =
  let prop s = let s = RBT.elements s in List.sort Pervasives.compare s = s in
  assert (Ty.for_all rbt_t prop);
  assert (Ty.for_all rbt_t RBT.is_balanced);
  ()
