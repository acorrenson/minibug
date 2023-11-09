
type nat =
| O
| S of nat

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
  | c1::s1' ->
    (match s2 with
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

(** val search : nat -> ('a1 -> bool) -> 'a1 stream -> 'a1 result **)

let rec search fuel p s =
  match fuel with
  | O -> (match Lazy.force
          s with
          | Snil -> NotFound
          | Scons (_, _) -> Timeout)
  | S fuel0 ->
    (match Lazy.force
     s with
     | Snil -> NotFound
     | Scons (x, s0) -> if p x then Found x else search fuel0 p s0)

type skip_case =
| Is_skip
| Is_not_skip

(** val skip_dec : prog -> skip_case **)

let skip_dec = function
| Skip -> Is_skip
| _ -> Is_not_skip

(** val expand : bexpr -> Symb.store -> prog -> Symb.state list **)

let rec expand path env = function
| Ite (b, p1, p2) ->
  (((Band (path, (Symb.beval env b))), env), p1) :: ((((Band (path, (Bnot
    (Symb.beval env b)))), env), p2) :: [])
| Seq (p1, p2) ->
  (match skip_dec p1 with
   | Is_skip -> ((path, env), p2) :: []
   | Is_not_skip ->
     map (fun pat -> let (y, p) = pat in (y, (Seq (p, p2))))
       (expand path env p1))
| Asg (x, e) -> ((path, (Symb.update env x (Symb.aeval env e))), Skip) :: []
| Loop (b, p) ->
  (((Band (path, (Symb.beval env b))), env), (Seq (p, (Loop (b,
    p))))) :: ((((Band (path, (Bnot (Symb.beval env b)))), env), Skip) :: [])
| _ -> []

(** val reachable : Symb.state list -> Symb.state stream **)

let rec reachable = function
| [] -> lazy Snil
| s :: l0 ->
  let (p0, p) = s in
  let (path, senv) = p0 in
  lazy (Scons (s, (reachable (app l0 (expand path senv p)))))

(** val find_bugs : nat -> prog -> Symb.state result **)

let find_bugs fuel p =
  search fuel Symb.is_error (reachable ((Symb.init p) :: []))
