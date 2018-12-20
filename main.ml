open Arg
open Compile
open Runner
open Printf
open Lexing
open Types

let check_types = ref false
let verbose = ref false
let name = ref ""

let main =
  begin
    let speclist = [
      ("--check-types", Arg.Set check_types, "Enables static type-checking");
      ("--verbose", Arg.Set verbose, "Enables printing of intermediate ASTs");
    ] in
    let usage = "./main [--check-types] [--verbose] <input-file>" in
    Arg.parse speclist (fun n -> name := n) usage;
    let input_file = open_in !name in
    match compile_file_to_string !name input_file !check_types !verbose with
    | Left errs ->
       printf "Errors:\n%s\n" (ExtString.String.join "\n" (print_errors errs))
    | Right program -> printf "%s\n" program
  end

let () = main;;
