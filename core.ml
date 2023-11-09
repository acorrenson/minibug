
(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val eqb : char list -> char list -> bool **)

let rec eqb s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' -> (match s2 with
                | [] -> false
                | c2::s2' -> if (=) c1 c2 then eqb s1' s2' else false)

type ident = char list

type aexpr =
| Var of ident
| Cst of int
| Add of aexpr * aexpr
| Sub of aexpr * aexpr

type bexpr =
| Bcst of bool
| Ble of aexpr * aexpr
| Beq of aexpr * aexpr
| Bnot of bexpr
| Band of bexpr * bexpr

type prog =
| Skip
| Ite of bexpr * prog * prog
| Seq of prog * prog
| Asg of char list * aexpr
| Err
| Loop of bexpr * prog

module Oracle =
 struct
  (** val next_is_error : prog -> bool **)

  let rec next_is_error = function
  | Seq (p0, _) -> next_is_error p0
  | Err -> true
  | _ -> false
 end

module Symb =
 struct
  type store = ident -> aexpr

  type state = (bexpr * store) * prog

  (** val id : store **)

  let id x =
    Var x

  (** val init : prog -> state **)

  let init p =
    (((Bcst true), id), p)

  (** val path : state -> bexpr **)

  let path = function
  | (p, _) -> let (path0, _) = p in path0

  (** val update : store -> ident -> aexpr -> store **)

  let update s x e y =
    if eqb y x then e else s y

  (** val aeval : store -> aexpr -> aexpr **)

  let rec aeval s e = match e with
  | Var x -> s x
  | Cst _ -> e
  | Add (e1, e2) -> Add ((aeval s e1), (aeval s e2))
  | Sub (e1, e2) -> Sub ((aeval s e1), (aeval s e2))

  (** val beval : store -> bexpr -> bexpr **)

  let rec beval s e = match e with
  | Bcst _ -> e
  | Ble (e1, e2) -> Ble ((aeval s e1), (aeval s e2))
  | Beq (e1, e2) -> Beq ((aeval s e1), (aeval s e2))
  | Bnot e0 -> Bnot (beval s e0)
  | Band (e1, e2) -> Band ((beval s e1), (beval s e2))

  (** val is_error : state -> bool **)

  let is_error = function
  | (_, prog0) -> Oracle.next_is_error prog0
 end

type 'a stream = 'a __stream Lazy.t
and 'a __stream =
| Snil
| Scons of 'a * 'a stream

type 'a result =
| Timeout
| Found of 'a
| NotFound

(** val search_opt : int -> ('a1 -> 'a2 option) -> 'a1 stream -> 'a2 result **)

let rec search_opt fuel p s =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match Lazy.force
              s with
              | Snil -> NotFound
              | Scons (_, _) -> Timeout)
    (fun fuel0 ->
    match Lazy.force
    s with
    | Snil -> NotFound
    | Scons (x, s0) -> (match p x with
                        | Some x0 -> Found x0
                        | None -> search_opt fuel0 p s0))
    fuel

(** val search : int -> ('a1 -> bool) -> 'a1 stream -> 'a1 result **)

let rec search fuel p s =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match Lazy.force
              s with
              | Snil -> NotFound
              | Scons (_, _) -> Timeout)
    (fun fuel0 ->
    match Lazy.force
    s with
    | Snil -> NotFound
    | Scons (x, s0) -> if p x then Found x else search fuel0 p s0)
    fuel

type skip_case =
| Is_skip
| Is_not_skip

(** val skip_dec : prog -> skip_case **)

let skip_dec = function
| Skip -> Is_skip
| _ -> Is_not_skip

(** val expand : bexpr -> Symb.store -> prog -> Symb.state list **)

let rec expand path0 env = function
| Ite (b, p1, p2) ->
  (((Band (path0, (Symb.beval env b))), env), p1) :: ((((Band (path0, (Bnot
    (Symb.beval env b)))), env), p2) :: [])
| Seq (p1, p2) ->
  (match skip_dec p1 with
   | Is_skip -> ((path0, env), p2) :: []
   | Is_not_skip ->
     map (fun pat -> let (y, p) = pat in (y, (Seq (p, p2)))) (expand path0 env p1))
| Asg (x, e) -> ((path0, (Symb.update env x (Symb.aeval env e))), Skip) :: []
| Loop (b, p) ->
  (((Band (path0, (Symb.beval env b))), env), (Seq (p, (Loop (b, p))))) :: ((((Band (path0,
    (Bnot (Symb.beval env b)))), env), Skip) :: [])
| _ -> []

(** val reachable : Symb.state list -> Symb.state stream **)

let rec reachable = function
| [] -> lazy Snil
| s :: l0 ->
  let (p0, p) = s in
  let (path0, senv) = p0 in lazy (Scons (s, (reachable (app l0 (expand path0 senv p)))))

module NaiveBugFinder =
 struct
  module Spec =
   struct
   end

  (** val find_bugs : int -> prog -> Symb.state result **)

  let find_bugs fuel p =
    search fuel Symb.is_error (reachable ((Symb.init p) :: []))
 end

type partial_store = (ident * int) list

type solver_result =
| SAT of partial_store
| UNSAT
| TIMEOUT

module type SOLVER =
 sig
  val check_sat : bexpr -> solver_result
 end

module BugFinder =
 functor (Solver:SOLVER) ->
 struct
  module Spec =
   struct
   end

  type bug =
  | SureBug of partial_store
  | UnsureBug of bexpr

  (** val bug_rect : (partial_store -> 'a1) -> (bexpr -> 'a1) -> bug -> 'a1 **)

  let bug_rect f f0 = function
  | SureBug wit -> f wit
  | UnsureBug path0 -> f0 path0

  (** val bug_rec : (partial_store -> 'a1) -> (bexpr -> 'a1) -> bug -> 'a1 **)

  let bug_rec f f0 = function
  | SureBug wit -> f wit
  | UnsureBug path0 -> f0 path0

  (** val is_error : Symb.state -> bug option **)

  let is_error s =
    if Symb.is_error s
    then (match Solver.check_sat (Symb.path s) with
          | SAT sol -> Some (SureBug sol)
          | UNSAT -> None
          | TIMEOUT -> Some (UnsureBug (Symb.path s)))
    else None

  (** val find_bugs : int -> prog -> bexpr -> bug result **)

  let find_bugs fuel p ass =
    search_opt fuel is_error (reachable (((ass, (fun x -> Var x)), p) :: []))
 end
