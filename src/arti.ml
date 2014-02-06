module PSet = struct
  type 'a t = 
    {
      eq: 'a -> 'a -> bool;
      enum : 'a list
    } 

  let mem x s =
    List.exists (fun y -> y = x) s.enum

  let add x s = 
    if mem x s then s else {s with enum = x::s.enum}

  let elements s = s.enum

end
    
type 'a ty =
  {
    mutable set : 'a PSet.t;
    uid : int;
  }

type (_,_) fn = 
| Return : 'a ty -> ('a,'a) fn
| Fun    : 'a ty * ('b, 'c) fn -> ('a -> 'b, 'c) fn;;

let rec eval : type a b. (a,b) fn -> a -> b list = 
  fun fd f ->
    match fd with
    | Return ty -> [f]
    | Fun (ty,fd) -> 
      List.flatten (List.map (fun e -> eval fd (f e)) (PSet.elements ty.set))
;;  

let rec codom : type a b. (a,b) fn -> b ty = 
		  function Fun (_,fd) -> codom fd
		  | Return ty -> ty

let use fd f = 
  let prod = eval fd f in 
  let ty = codom fd in 
  ty.set <- List.fold_right (PSet.add) prod ty.set;
  ()

module Sig = struct
  type dyn = Dyn : ('a,'b) fn * 'a -> dyn
    
  type t = (string * dyn) list 

  let add s id fd f =
    (id, Dyn (fd,f))::s

  type iteratee = {inhab : 'a 'b. string -> ('a,'b) fn -> 'a -> unit } 

  let iter (g:iteratee ) s =
    List.iter (fun (id,d) ->
      match d with
	Dyn (fd,f) -> g.inhab id fd f
      
    ) s
      
end

let rec ncheck n (s: Sig.t) = 
  if n = 0 
  then ()
  else 
    begin 
      Sig.iter {Sig.inhab = fun id fd f -> use fd f} s;
      ncheck (pred n) s
    end


  
  



