open Z3
open Z3.Solver
open Z3.Arithmetic
open Core

let hard_fail msg =
  Printf.eprintf "[internal error] %s\n" msg;
  exit 1

module Solver = struct
  let ctx = mk_context []

  let decl_to_int model decl =
    let e = Model.get_const_interp model decl in
    Expr.(simplify (Option.get e) None |> to_string |> int_of_string)

  let decl_to_ident decl =
    FuncDecl.get_name decl
    |> Symbol.to_string
    |> Opal.explode

  let extract_model (m : Model.model) : (Core.ident * int) list =
    List.map (fun decl ->
      (decl_to_ident decl, decl_to_int m decl)
    ) (Model.get_const_decls m)

  let rec mk_expr (e : Core.aexpr) =
    match e with
    | Var n -> Integer.mk_const ctx (Symbol.mk_string ctx (Opal.implode n))
    | Cst c -> Integer.mk_numeral_i ctx c
    | Add (e1, e2) -> mk_add ctx [mk_expr e1; mk_expr e2]
    | Sub (e1, e2) -> mk_sub ctx [mk_expr e1; mk_expr e2]

  let rec mk_form (e : Core.bexpr) =
    match e with
    | Bcst true -> Boolean.mk_true ctx
    | Bcst false -> Boolean.mk_false ctx
    | Band (l, r) -> Boolean.mk_and ctx [mk_form l; mk_form r]
    | Ble (e1, e2) -> mk_le ctx (mk_expr e1) (mk_expr e2)
    | Beq (e1, e2) -> Boolean.mk_eq ctx (mk_expr e1) (mk_expr e2)
    | Bnot f -> Boolean.mk_not ctx (mk_form f)

  let check_sat (f : Core.bexpr) =
    let slv = mk_simple_solver ctx in
    let pro = mk_form f in
    add slv [pro];
    match check slv [] with
    | SATISFIABLE ->
      begin match get_model slv with
      | None ->
        hard_fail "model extraction failed"
      | Some m ->
        SAT (extract_model m)
      end
    | UNSATISFIABLE -> UNSAT
    | UNKNOWN -> TIMEOUT

  let print_model (m : Core.partial_store) =
    List.iter (fun (x, vx) ->
      Printf.printf "%s := %d\n" (Opal.implode x) vx
    ) m
end