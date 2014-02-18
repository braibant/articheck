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

type (_, _) fn =
    Constant : 'a ty -> ('a, 'a) fn
  | Fun : 'a ty * ('b, 'c) fn -> ('a -> 'b, 'c) fn

(* -------------------------------------------------------------------------- *)

(** {2 The core module of our type descriptors } *)

module Ty :
  sig
    val mem : 'a -> 'a ty -> bool
    val cardinal : 'a ty -> int
    val add : 'a -> 'a ty -> unit
    val elements : 'a ty -> 'a list
    val merge : 'a ty -> 'a list -> bool
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

val ( @-> ) : 'a ty -> ('b, 'c) fn -> ('a -> 'b, 'c) fn
val returning : 'a ty -> ('a, 'a) fn

(** Recursively find the descriptor that corresponds to the codomain of a
 * function. *)
val codom : ('a, 'b) fn -> 'b ty

(* -------------------------------------------------------------------------- *)

(** {2 Describing signatures of modules that we wish to test } *)

module Sig :
  sig
    type value
    val val_ : ident -> ('a, 'b) fn -> 'a -> value
    val populate : value list -> unit
  end
