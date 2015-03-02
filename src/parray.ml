
type 'a t = 'a data ref
and 'a data =
  | Array of 'a array
  | Diff of int * 'a * 'a t


let make n v = ref (Array (Array.make n v))

let rec rerootk t k = match !t with
  | Array _ -> k ()
  | Diff (i, v, t') ->
    rerootk t' (fun () -> begin match !t' with
        | Array a as n ->
          let v' = a.(i) in
          a.(i) <- v;
          t := n;
          t' := Diff (i, v', t)
        | Diff _ -> assert false end; k())

let reroot t = rerootk t (fun () -> ())

let length v =
  reroot v;
  match !v with
    Diff _ -> assert false
  | Array v -> Array.length v

let set t i v =
  reroot t;
  match !t with
  | Array a as n ->
    let old = a.(i) in
    if old == v then
      t
    else begin
      a.(i) <- v;
      let res = ref n in
      t := Diff (i, old, res);
      res
      end
  | Diff _ ->
    assert false

let get t i =
  reroot t;
  match !t with
  | Diff _ -> assert false
  | Array a -> a.(i)

(* wrappers to apply an impure function from Array to a persistent
     array *)
let impure f t =
  reroot t;
  match !t with Array a -> f a | Diff _ -> assert false

let fold f t init  = impure (Array.fold_right f) t init
