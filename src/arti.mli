type ('a, 'b) sum =
| L of 'a
| R of 'b

type ident = string

(** The definition of a type descriptor for elements of the type ['a]*)
type 'a ty

type ('a, 'b) negative and 'a positive

(* -------------------------------------------------------------------------- *)

(** {2 The core module of our type descriptors } *)

module Ty :
  sig
    val cardinal : 'a ty -> int
    val add : 'a -> 'a ty -> unit
    val declare :
      ?initial:'a list ->
      ?ident:string ->
      ?fresh:('a Bag.t -> 'a) ->
      ?required:int ->
      ?bag:'a Bag.t ->
      unit -> 'a ty
    val populate : int -> 'a ty -> unit
  end

(* -------------------------------------------------------------------------- *)

(** {2 Constructing type representations} *)

val atom : 'a ty -> 'a positive
val returning : 'a positive -> ('a, 'a) negative
val ( @-> ) : 'a positive -> ('b, 'c) negative -> ('a -> 'b, 'c) negative
val ( +@ ) : 'a positive -> 'b positive -> ('a, 'b) sum positive
val ( *@ ) : 'a positive -> 'b positive -> ('a * 'b) positive

type ('a, 'b) bijection = ('a -> 'b) * ('b -> 'a)
val bij : 'a positive -> ('a, 'b) bijection -> 'b positive

(** derived type representations *)
val unit : unit positive
val option : 'a positive -> 'a option positive

(** Testing types *)
val counter_example : string -> 'a positive -> ('a -> bool) -> 'a option


(* -------------------------------------------------------------------------- *)

(** {2 Describing signatures of modules that we wish to test } *)

module Sig :
  sig
    type value
    val val_ : ident -> ('a, 'b) negative -> 'a -> value
    val populate : value list -> unit
  end
