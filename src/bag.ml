module type S =
sig
  type 'a t
  val insert : 'a -> 'a t -> 'a t
  val iter : ('a -> unit) -> 'a t -> unit
  val cardinal : 'a t -> int
  val create : ('a -> 'a -> int) -> int -> 'a t
end

(* ------------------------------------------------------------------------ *)

(** {2 Bags implemented using a sampling mechanism } *)

module Parray : sig
  type 'a t
  val create : int -> 'a -> 'a t
  val set : 'a t -> int -> 'a -> 'a t
  val iter : ('a -> unit) -> 'a t -> unit
end = struct
  type 'a t = 'a data ref
  and 'a data =
  | Array of 'a array
  | Diff of int * 'a * 'a t


  let create n v = ref (Array (Array.create n v))

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

  (* wrappers to apply an impure function from Array to a persistent
     array *)
  let impure f t =
    reroot t;
    match !t with Array a -> f a | Diff _ -> assert false


  let iter f t = impure (Array.iter f) t

end

module Sample : S = struct

  type 'a t =
    {
      elements: 'a Parray.t option;
      size  : int;
      count : int;
    }

  let create _ size = {elements = None; count = 0; size}

  let insert e v =
    match v.elements with
    | None -> {v with elements = Some (Parray.create v.size e); count = 1}
    | Some elements ->
      if v.count < v.size
      then                                (* fill the reservoir *)
        let elements = Some (Parray.set elements v.count e) in
        {elements; count = v.count + 1; size = v.size}
      else
        let j = Random.int (v.count) in  (* between 0 and v.count - 1 *)
        if j < v.size
        then
          let elements = Some (Parray.set elements j e) in
          {elements; count = v.count + 1; size = v.size}
        else {v with count = v.count + 1}

  let iter f v = match v.elements with
    | None -> ()
    | Some elements -> Parray.iter f elements

  let cardinal v = min (v.size) (v.count)
end


(* ------------------------------------------------------------------------ *)

(** {2 Bags implemented as polymorphic sets } *)
module PSet : S = struct


  (* This code is different from the other implementation of RBT
     below, by intension*)
  module RBT = struct
    type 'a t =
    | Empty
    | Red of 'a t * 'a * 'a t
    | Black of 'a t * 'a * 'a t

    let empty = Empty

    let blacken = function
      | Red (l,v,r) -> Black (l,v,r)
      | (Empty | Black _) as n -> n

    let balance = function
      | Black ((Red (Red (a, x, b), y, c)
                   | Red (a, x, Red (b, y, c))), z, d)
      | Black (a, x, (Red (Red (b, y, c), z, d)
                         | Red (b, y, Red (c, z, d))))
        -> Red (Black (a, x, b), y, Black (c, z, d))
      | n -> n

    let insert compare x n =
      let rec insert x t = match t with
        | Empty -> Red (Empty, x, Empty)
        | Red (l,v,r) ->
          begin match compare x v with
          | -1 -> Red (insert x l,v,r)
          | 0 -> Red (l,v,r)
          | _ -> Red (l,v,insert x r)
          end
        | Black (l,v,r) ->
          begin match compare x v with
          | -1 -> balance (Black (insert x l,v,r))
          | 0 -> Black (l,v,r)
          | _ -> balance (Black (l,v,insert x r))
          end
      in blacken (insert x n)

    let rec iter f = function
      | Empty -> ()
      | Red (l,v,r) | Black (l,v,r) ->
        iter f l;
        f v;
        iter f r


    let rec cardinal = function
      | Empty -> 0
      | Red (l,_,r) | Black (l,_,r) -> cardinal l + cardinal r + 1
  end

  (** {2 Wrapping the set with the associated comparison function.}  *)
  type 'a t =
    {
      set: 'a RBT.t;
      compare: 'a -> 'a -> int;
    }

  let create compare _ = {set= RBT.empty; compare}
  let insert x s = {s with set = RBT.insert s.compare x s.set}
  let cardinal s = RBT.cardinal s.set
  let iter f s = RBT.iter f s.set
end
