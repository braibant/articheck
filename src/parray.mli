type 'a t
val make : int -> 'a -> 'a t
val length : 'a t -> int
val set : 'a t -> int -> 'a -> 'a t
val get : 'a t -> int -> 'a
val fold : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
