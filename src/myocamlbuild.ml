open Ocamlbuild_plugin;;
open Command;;

let _ =
  dispatch (fun event ->
    match event with
    | After_rules ->
        flag ["ocaml"; "compile"; "my_warnings"]
          (S[A "-w"; A "@1..3@8..12@14..21@23..40-41@43"]);
    | _ -> ()
  );
;;
