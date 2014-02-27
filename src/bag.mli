(** a signature for bags, which retain set of randomly-generated
    elements *)
type 'a t = {
  insert : 'a -> 'a t;
  iter : ('a -> unit) -> unit;
  cardinal : unit -> int;
}

val pset : ('a -> 'a -> int) -> 'a t
(** Exhaustive bags, that store all the added elements in a (balanced)
    set, removing duplicates. *)

val sample : int -> 'a t
(** Sampling bags, which only retains a bounded number of elements,
    passed as parameter at bag creation time. At any point in time,
    each of the element added to the bag has equal probability to have
    been retained in the sample. *)
