(** OCaml has built-in syntax for product types (tuples), but not for
    sum types. *)
type ('a, 'b) sum =
| L of 'a
| R of 'b

(** Implementing polymorphic identifiers with extensible types *)

type (_, _) equal =
  | Equal: ('a, 'a) equal
  | Different: ('a, 'b) equal

module Pid : sig
  type 'a t
  val fresh : unit -> 'a t
  val equal : 'a t -> 'b t -> ('a,'b) equal
  val to_int : 'a t -> int
end
= struct

  type 'a key = ..

  module type S = sig
    type t
    type 'a key += T : t key
  end

  type 'a t = (module S with type t = 'a)

  let fresh (type a) () =
    let module M = struct
    type t = a
    type 'a key += T : t key
  end in
  (module M : S with type t = a)

  let equal (type a) (type b)
      (module A : S with type t = a)
      (module B : S with type t = b)
    : (a, b) equal =
    match A.T with
    | B.T -> Equal
    | _   -> Different

  let to_int : 'a t -> int = Hashtbl.hash
end

module Pidm = struct
  module type S =
  sig
    type 'a key
    type 'a value
    type binding = Binding: 'a key * 'a value -> binding
    type t
    val empty: t
    val add: t -> 'a key -> 'a value -> t
    val remove: t -> 'a key -> t
    val find: t -> 'a key -> 'a value
    val mem: t -> 'a key -> bool
    val length: t -> int
    val iter: (binding -> unit) -> t -> unit
    val fold: (binding -> 'a -> 'a) -> t -> 'a -> 'a
  end

  module Make
      (Key:sig
         type 'a t
         val compare : 'a t -> 'b t -> int
         val equal : 'a t -> 'b t -> ('a,'b) equal
       end)
      (Value:sig
         type 'a t
       end
      ): S with type 'a key = 'a Key.t and type 'a value = 'a Value.t =
  struct
    type 'a key = 'a Key.t
    type 'a value = 'a Value.t
    type binding = Binding: 'a key * 'a value -> binding
    module KeyPack = struct
      type t =  Key: 'a key -> t
      let compare (Key a) (Key b) = Key.compare a b
    end

    module M = Map.Make(KeyPack)

    type t = binding M.t
    let empty : t = M.empty
    let add t key value = M.add (KeyPack.Key key) (Binding (key, value)) t
    let remove t key = M.remove (KeyPack.Key key) t
    let find (type a) t (key: a key) : a value =
      match M.find (KeyPack.Key key) t with
      | Binding (key', value) ->
        begin match Key.equal key key' with
          | Equal -> value
          | Different -> assert false
        end
    let mem t key = M.mem (KeyPack.Key key) t
    let length = M.cardinal
    let iter f t = M.iter (fun _ binding -> f binding) t
    let fold f t acc = M.fold (fun _ binding acc -> f binding acc) t acc
  end
end

module Type = struct

  (** Internally, a type descriptor is made up of:
      - a unique identifier
      - a comparison function;
      - a hash function
  *)
  type 'a t =
    {
      uid: 'a Pid.t;
      tag: string option;
      compare: 'a -> 'a -> int;
      hash: 'a -> int;
    }

  let declare ?tag ?(compare=Pervasives.compare) ?(hash = Hashtbl.hash) () =
    {
      uid = Pid.fresh ();
      tag;
      compare;
      hash;
    }

  let equal a b = Pid.equal a.uid b.uid
  let compare a b = Pervasives.compare (Pid.to_int a.uid) (Pid.to_int b.uid)
end

type 'a ty = 'a Type.t

type ('a, 'b) bijection = ('a -> 'b) * ('b -> 'a)

(** The GADT [('arrow, 'domain, 'codomain) negative] describes
    currified functions of type ['arrow] whose return datatype is a
    positive type ['codomain]. The words "negative" (for functions)
    and "positive" (for products and sums) comes from focusing, a
    point of view that is surprisingly adapted here.

    - the [Fun] constructor models function types [P -> N], where [P] is
    a positive type and [N] is negative (functions returned by functions
    corresponds to currification). The return type of [P -> N], as
    a currified function, is the return type of [N].

    - the [Ret] constructor corresponds to the final end of
    a multi-arrow function type, or to 0-ary functions. It takes
    a positive datatype (in focusing terms, it is the "shift" that
    embeds positives into negatives).  *)

type ('arrow,'domain,'codomain) negative =
  | Fun: 'a positive * ('arrow, 'domain, 'codomain) negative
    -> ('a -> 'arrow, 'a * 'domain, 'codomain) negative
  | Ret: 'a positive -> ('a, 'unit, 'a) negative
and _ positive =
  | Ty: 'a ty -> 'a positive
  | Sum : 'a positive * 'b positive -> ('a, 'b) sum positive
  | Prod : 'a positive  * 'b positive -> ('a * 'b) positive
  | Bij : 'a positive * ('a, 'b) bijection -> 'b positive

  | Option: 'a positive -> 'a option positive
  | List: 'a positive -> 'a list positive

(**  The type of functions that may appear in an interface *)
type value =
  | Value:
      string
      * ('arrow, 'domain, 'codomain) negative
      * 'arrow -> value

(** A pair of a type and a set of inhabitants  *)
type inhabitants =
  | InhabitantList : 'a ty * 'a list -> inhabitants


module type ENV = sig
  type env
  val start: inhabitants list -> env
  val stop: env -> inhabitants list
end

module type STRATEGY = sig
  include ENV
  val apply : value list -> env -> env
end

module Sample (X: sig val size: int end): STRATEGY =
struct

  module Sample = struct

    open Type
    type 'a bucket = Empty | Full of 'a
    type 'a t = 'a ty * 'a bucket Parray.t

    (* keep the new additions *)
    let add (ty, table) value : 'a t=
      let hash = ty.hash value in
      let index = hash mod (Parray.length table) in
      ty, Parray.set table index (Full value)

    let init ty = (ty, Parray.make X.size Empty)
  end

  module M = Pidm.Make(Type)(Sample)

  type env = M.t

  let addl env ty values : env =
    let sample =
      try M.find env ty
      with Not_found -> Sample.init ty
    in
    let sample = List.fold_left (Sample.add) sample values in
    M.add env ty sample

  (* let add env ty value = addl env ty [value] *)

  let start inhabs =
    List.fold_left (fun env (InhabitantList (ty, l)) -> addl env ty l) M.empty inhabs

  let stop env = assert false
  let apply = assert false
end
