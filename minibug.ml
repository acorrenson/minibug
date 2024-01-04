open Parser
open Solver

module BF = Core.BugFinder(Solver)

let () =
  let (assume, prog) = parse_file (Sys.argv.(1)) in
  match BF.find_bugs 100000 prog assume with
  | Timeout ->
    Printf.eprintf "bug finding timed out!\n"
  | Found (SureBug m) ->
    Printf.eprintf "Found a sure bug!\n";
    Solver.print_model m
  | Found (UnsureBug _) ->
    Printf.eprintf "Found a (un)sure bug!\n"
  | NotFound ->
    Printf.eprintf "☑️ No bugs found\n"