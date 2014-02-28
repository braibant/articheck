module type S =
sig
  type 'a t
  val insert : 'a -> 'a t -> 'a t
  val fold : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val cardinal : 'a t -> int
end

(* ------------------------------------------------------------------------ *)

(** {2 Bags implemented using a sampling mechanism } *)

module Parray : sig
  type 'a t
  val create : int -> 'a -> 'a t
  val length : 'a t -> int
  val set : 'a t -> int -> 'a -> 'a t
  val get : 'a t -> int -> 'a
  val fold : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
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
end

module Sample : sig
  include S
  val create : size:int -> 'a t
end = struct

  (* We need three values here:
     - the size of the sample that we keep.
     - the number of elements generated so far.
     - the maximal number of elements to generate
  *)
  type 'a t =
    {
      elements: 'a Parray.t option;
      size  : int;
      generated : int;
    }

  let create ~size  = {elements = None; generated = 0; size}

  let insert e v =
    match v.elements with
    | None -> {v with elements = Some (Parray.create v.size e); generated = 1}
    | Some elements ->
      if v.generated < v.size
      then                                (* fill the reservoir *)
        let elements = Some (Parray.set elements v.generated e) in
        {v with elements; generated = v.generated + 1}
      else
        let j = Random.int (v.generated) in  (* between 0 and v.generated - 1 *)
        if j < v.size
        then
          let elements = Some (Parray.set elements j e) in
          {v with elements; generated = v.generated + 1}
        else {v with generated = v.generated + 1}

  let fold f v init = match v.elements with
    | None -> init
    | Some elements -> Parray.fold f elements init

  let cardinal v = v.generated
end


(* ------------------------------------------------------------------------ *)

module HashSet : sig
  include S
  val create: int -> ('a -> int) -> 'a t
end
=
struct
  (* module Bucket = struct *)
  (*   let size = 5 *)

  (*   type 'a bucket = *)
  (* 	{ elements: 'a Parray.t; *)
  (* 	  head: int *)
  (* 	} *)
  (*   and 'a t = 'a bucket option *)

  (*   let add e = function *)
  (*     | None -> Some {elements = Parray.create size e; head = 0} *)
  (*     | Some v -> *)
  (* 	Some { *)
  (* 	  elements = Parray.set v.elements v.head e; *)
  (* 	  head = (v.head + 1) mod size *)
  (* 	} *)

  (*   let fold f t acc = match t with *)
  (*     | None -> acc *)
  (*     | Some v ->  Parray.fold f v.elements acc *)

  (*   let empty : 'a t = None *)
  (* end *)

  module Bucket = struct
    type 'a t = 'a option

    let add e _ = Some e

    let fold f t acc = match t with | None -> acc | Some e -> f e acc

    let empty = None
  end
  type 'a t =
      {
	elements: 'a Bucket.t Parray.t;
	hash: 'a -> int;
	produced: int
      }

  let insert e t =
    let length = Parray.length t.elements in
    let n = (t.hash e land max_int) mod length in
    let bucket = Parray.get t.elements n  in
    let bucket = Bucket.add e bucket in
    {t with elements = Parray.set t.elements n bucket; produced = t.produced + 1}

  let fold f t acc =
    Parray.fold (fun bucket acc -> Bucket.fold f bucket acc) t.elements acc

  let cardinal t = t.produced

  let create size hash =
    {
      elements = Parray.create size Bucket.empty;
      hash;
      produced = 0
    }
end

(* ------------------------------------------------------------------------ *)

(** {2 Bags implemented as polymorphic sets } *)
module PSet : sig
  include S
  val create : ('a -> 'a -> int) -> 'a t
end = struct
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

    let rec fold f t state = match t with
      | Empty -> state
      | Red (l,v,r) | Black (l,v,r) ->
        let state = fold f l state in
        let state = f v state in
        let state = fold f r state in
        state

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

  let create compare = {set= RBT.empty; compare}
  let insert x s = {s with set = RBT.insert s.compare x s.set}
  let cardinal s = RBT.cardinal s.set
  let fold f s init = RBT.fold f s.set init
end

type 'a t = {
  insert : 'a -> 'a t;
  fold : 'b . ('a -> 'b -> 'b) -> 'b -> 'b;
  cardinal : unit -> int;
}

module Pack (Impl : S) = struct
  let rec pack (bag : 'a Impl.t) : 'a t = {
    insert = (fun x -> pack (Impl.insert x bag));
    fold = (fun f init -> Impl.fold f bag init);
    cardinal = (fun () -> Impl.cardinal bag);
  }
end

let sample ~size  =
  let module P = Pack(Sample) in
  P.pack (Sample.create ~size)

let pset cmp =
  let module P = Pack(PSet) in
  P.pack (PSet.create cmp)

let hashset ~size ~hash =
  let module P = Pack(HashSet) in
  P.pack (HashSet.create size hash)
