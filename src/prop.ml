(* this file is independent from the rest of the Articheck source
   code, it was only a vehicle for experimentation on
   property-description languages -- see

     https://github.com/braibant/articheck/issues/24

   The current state has a description language for the "relaxed
   restricted language" (nested implications and forall), but is
   simplistic and doesn't handle two important points:

   - it consider finite lists of value are available, and does not
   explore the search space in any interesting way; in particular it
   does not handle the "fairness" issue that arise from the nesting of
   preconditions and quantifiers

   - the "eval" function does not count successful and discarded
   tests, so it provides no useful statistics to the user

   It would also be nice if it had a principled way to handle and
   report exceptions raised by the user-provided code.
*)
type ('a, 'b) sum = L of 'a | R of 'b
let comp f g = fun x -> f (g x)

type 'a ty = 'a list

type _ prop =
| Bool : bool -> unit prop
| Forall : 'a ty * ('a -> 'b prop) -> ('a * 'b) prop
| Impl : bool * (unit -> 'b prop) -> 'b prop
| Map : 'a prop * ('a -> 'b) -> 'b prop

let test b = Bool b
let map f prop = Map (prop, f)

let all ty p = Forall (ty, p)
let all2 ty1 ty2 p =
  all ty1 (comp (all ty2) p)
  |> map (fun (x,(y,env)) -> (x,y),env)
let all3 ty1 ty2 ty3 p =
  all ty1 (comp (all2 ty2 ty3) p)
  |> map (fun (x,((y,z),env)) -> (x,y,z),env)

let (==>) a b = Impl (a, b)

let rec eval : type a . a prop -> a option = function
  | Bool true -> None
  | Bool false -> Some ()
  | Forall (elems, prop) ->
    let add result elem = match result, lazy (eval (prop elem)) with
      | Some _, _ -> result
      | None, lazy (Some trace) -> Some (elem, trace)
      | None, lazy None -> None
    in List.fold_left add None elems
  | Impl (false, _pb) -> None
  | Impl (true, pb) -> eval (pb ())
  | Map (prop, f) ->
    begin match eval prop with
      | None -> None
      | Some trace -> Some (f trace)
    end

(* Examples *)
let int = [1;2;3;4;5;6]
let list =[ []; [(1,2)]; [(1,2); (3,4)]; [(1,2); (1,3)] ]

let add_assoc k v li = (k,v)::li

let _ = eval begin
  all3 list int int @@ fun li k v ->
    test (List.assoc k (add_assoc k v li) = v)
end

let _ = eval begin
  all2 list int @@ fun li k ->
    test (not (List.mem_assoc k (List.remove_assoc k li)))
end

let _ = eval begin
  all2 list int @@ fun li k ->
    List.mem_assoc k li ==> fun () ->
      let v0 = List.assoc k li in
      all int @@ fun v ->
        test (v0 =
          (add_assoc k v li
           |> List.remove_assoc k
           |> List.assoc k)
        )
end
