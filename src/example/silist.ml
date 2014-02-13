open Arti

module SIList = struct
  type t = int list

  let empty = []

  let rec add x = function
    | [] -> [x]
    | t::q -> if t < x then t :: add x q else x::t::q

  let pp l = Printf.sprintf "[%s]" (String.concat ";" (List.map string_of_int l))

end

(** The description of the type of sorted integer lists. Elements of this type
 * can be compared using the polymorphic, structural comparison operator (=). *)
let si_t : SIList.t ty = Ty.declare ()

(** Conversely, [int] is a ground type that can not only be compared with (=),
 * but also admits a generator. *)
let int_t : int ty = Ty.declare ~fresh:(fun _ -> Random.int 10) ()

(** Populate the descriptor of the built-in type [int]. *)
let () =
  Ty.populate 10 int_t

(** Use module [Sig] to build a description of the signature of [SIList]. *)
let silist_sig = Sig.([
  val_ "empty" (returning si_t) SIList.empty;
  val_ "add" (int_t @-> si_t @-> returning si_t) SIList.add;
])

(** Generate instances of [SIList.t]. *)
let () =
  Sig.populate silist_sig

(** The property that we wish to test for is that the lists are well-sorted. We
 * define a predicate for that purpose and assert that no counter-example can be
 * found. *)
let () =
  let prop s = List.sort Pervasives.compare s = s in
  assert (Ty.counter_example "sorted lists" si_t prop = None);
  ()
