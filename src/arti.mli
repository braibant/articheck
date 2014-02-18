type ('a, 'b) sum =
| L of 'a
| R of 'b

(** {2 Polymorphic sets, implemented as RBT}  *)

module PSet :
  sig
    type 'a t
    val create : ('a -> 'a -> int) -> 'a t
    val insert : 'a -> 'a t -> 'a t
    val mem : 'a -> 'a t -> bool
    val cardinal : 'a t -> int
    val elements : 'a t -> 'a list
  end

type ident = string

(** The definition of a type descriptor for elements of the type ['a]*)
type 'a ty

type ('a, 'b) negative
and 'a positive

type elem
type atom

(* -------------------------------------------------------------------------- *)

(** {2 The core module of our type descriptors } *)

module Ty :
  sig
    val mem : 'a -> 'a ty -> bool
    val cardinal : 'a ty -> int
    val add : 'a -> 'a ty -> unit
    val elements : 'a ty -> 'a list
    val declare :
      ?cmp:('a -> 'a -> int) ->
      ?initial:'a list ->
      ?ident:string ->
      ?fresh:('a PSet.t -> 'a) -> unit -> 'a ty
    val populate : int -> 'a ty -> unit
    val counter_example : string -> 'a ty -> ('a -> bool) -> 'a option
  end

(* -------------------------------------------------------------------------- *)

(** {2 Main routines for dealing with our GADT } *)

val returning : 'a ty -> ('a, 'a) negative
val ( @-> ) : 'a ty -> ('b, 'c) negative -> ('a -> 'b, 'c) negative
val ( +@ ) : 'a positive -> 'b positive -> ('a, 'b) sum positive
val ( *@ ) : 'a positive -> 'b positive -> ('a * 'b) positive

(* -------------------------------------------------------------------------- *)

(** {2 Describing signatures of modules that we wish to test } *)

module Sig :
  sig
    type value
    val val_ : ident -> ('a, 'b) negative -> 'a -> value
    val populate : value list -> unit
  end
