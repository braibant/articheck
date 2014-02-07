module Ty = struct
  type 'a t = {
    eq: 'a -> 'a -> bool;
    mutable enum : 'a list;
    fresh : ('a list -> 'a) option;
    invar : ('a -> bool) option;
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
    invar = None;
    uid = gensym ()
  }

  (* generate a fresh type descriptor *)
  (* maybe we could remember what is the base type, so that if we run
     out of elements for the new type, we could generate new instances of
     the old one, and select the one that fulfill the invariant. *)
  let (/) ty invar =     
    match ty.invar with 
      | None -> 
	let invar = Some invar in 
	{ty with uid = gensym (); invar}
      | Some old -> 
	let invar = Some (fun x -> invar x && old x) in 
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
        ty.enum <- fresh ty.enum :: ty.enum
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
  assert (Ty.for_all si_t prop)
