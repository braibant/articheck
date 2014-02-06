module Ty = struct
    
  type 'a t =
    {
      eq: 'a -> 'a -> bool;
      mutable enum : 'a list;
      fresh : ('a list -> 'a) option; 
      uid : int;
    }
      
  let mem x s =
    List.exists (fun y -> y = x) s.enum

  let add x s = 
    if mem x s then () else s.enum <- x::s.enum

  let elements s = s.enum

end

type 'a ty = 'a Ty.t    

type (_,_) fn = 
| Constant : 'a ty -> ('a,'a) fn
| Fun    : 'a ty * ('b, 'c) fn -> ('a -> 'b, 'c) fn;;

let rec eval : type a b. (a,b) fn -> a -> b list = 
		 let open Ty in 
  fun fd f ->
    match fd with
    | Constant ty -> [f]
    | Fun (ty,fd) -> 
      List.flatten (List.map (fun e -> eval fd (f e)) (ty.enum))
;;  

let rec codom : type a b. (a,b) fn -> b ty = 
		  function Fun (_,fd) -> codom fd
		  | Constant ty -> ty

let use fd f = 
  let prod = eval fd f in 
  let ty = codom fd in 
  List.iter (fun x -> Ty.add x ty) prod;
  ()

let declare_type () =
  let id = ref 0 in 
  fun ?fresh eq -> 
    incr id; Ty.({ eq ; fresh; enum = []; uid = !id})

let populate n ty = 
  let open Ty in 
  match ty.fresh with
  | None -> invalid_arg "populate"
  | Some fresh -> 
  for i = 0 to n - 1 do
    ty.enum <- fresh (ty.enum) :: ty.enum
  done
;;

let (@->) ty fd = Fun (ty,fd)
let returning ty = Constant ty

module Sig = struct
  type elem = Elem : ('a,'b) fn * 'a -> elem
    
  type t = (string * elem) list 

  let empty = []

  let add s id fd f =
    (id, Elem (fd,f))::s

  type iteratee = {inhab : 'a 'b. string -> ('a,'b) fn -> 'a -> unit } 

  let iter (g:iteratee ) s =
    List.iter (fun (id,d) ->
      match d with
	Elem (fd,f) -> g.inhab id fd f
      
    ) s

  let for_all ty f =
    List.for_all f ty.Ty.enum
end

let rec ncheck n (s: Sig.t) = 
  if n = 0 
  then ()
  else 
    begin 
      Sig.iter {Sig.inhab = fun id fd f -> use fd f} s;
      ncheck (pred n) s
    end


(* Example *)
module SIList = struct

  type t = int list

  let empty = []

  let rec add x = function 
    | [] -> [x]
    | t::q -> if t < x then t :: add x q else x::t::q

end
 

let si_t : SIList.t ty = declare_type () (=)  
let int_t : int ty = declare_type () ~fresh:(fun _ -> Random.int 1000)(=)
let _ = populate 10 int_t


let s = Sig.empty 
let s = Sig.add s "empty" (returning si_t) SIList.empty
let s = Sig.add s "add" (int_t @-> si_t @-> returning si_t) SIList.add

let _ =  ncheck  5 s;;

let _ = Sig.prop si_t (fun s -> List.sort Pervasives.compare s = s);;  




