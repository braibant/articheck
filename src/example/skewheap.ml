module H : sig
  type 'a t
  val top : 'a t -> 'a option
  val pop : 'a t -> 'a t option
  val add : 'a -> 'a t -> 'a t

  (** invariant over heaps' structure *)
  val invariant : 'a t -> bool
  (** invariant about the cost of the insertion:  amortized log *)
  val prop_cost_add : 'a -> 'a t -> bool
end
= struct
  type 'a t =
      Null
    | Fork of 'a * 'a t * 'a t

  let empty = Null

  let top = function
    | Null -> None
    | Fork (x,_,_) -> Some x

  let rec add x = function
    | Null -> Fork (x,empty,empty)
    | Fork (y,l,r) ->
      if x <= y
      then Fork (x,r, add y l)
      else Fork (y,r,add x l)

  let rec merge h1 h2 =
    match h1, h2 with
      | e, Null | Null, e -> e
      | Fork (x,l,r), h when top h1 <= top h2 ->
	Fork (x,r,merge l h)
      | h, Fork (x,l,r) ->
	Fork (x,r,merge l h)

  let pop = function
    | Null -> None
    | Fork (_,l,r) -> Some (merge l r)

  (* -------------------------------------------------------------------------------- *)

  (** {2 Invariants about the data-structure }  *)

  (** {3 First, the minimum is located at the top of the heap} *)

  let rec invariant = function
    | Null -> true
    | Fork (x,l,r) -> smaller x l && smaller x r
  and smaller x = function
    | Null -> true
    | Fork (y,l,r) as n -> x <= y && invariant n


  (** {3 Second, insertion can be done in amortized log time } *)
  let rec weight = function
    | Null -> 0
    | Fork (_,l,r) -> 1 + weight l + weight r

  let good = function
    | Null -> true
    | Fork (_,l,r) -> weight l <= weight r

  let rec credits = function
    | Null -> 0
    | Fork (_,l,r) as n -> credits l + credits r + if good n then 0 else 1

  let rec cost_add = function
    | Null -> 0
    | Fork (_,l,_) -> 1 + cost_add l

  let rec log2 n =
    if n <= 0
    then 0			(* invalid_arg "" *)
    else if n = 1
    then 1 else
      1 + log2 (n / 2)

  let prop_cost_add n h =
    cost_add h + credits (add n h)
    <= 2 * log2 (weight h) + 1 + credits h

end
