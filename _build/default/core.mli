
type nat =
| O
| S of nat

val app : 'a1 list -> 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val eqb : char list -> char list -> bool

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

module Oracle :
 sig
  val next_is_error : prog -> bool
 end

module Symb :
 sig
  type store = ident -> aexpr

  type state = (bexpr * store) * prog

  val id : store

  val init : prog -> state

  val update : store -> ident -> aexpr -> store

  val aeval : store -> aexpr -> aexpr

  val beval : store -> bexpr -> bexpr

  val is_error : state -> bool
 end

type 'a stream = 'a __stream Lazy.t
and 'a __stream =
| Snil
| Scons of 'a * 'a stream

type 'a result =
| Timeout
| Found of 'a
| NotFound

val search : nat -> ('a1 -> bool) -> 'a1 stream -> 'a1 result

type skip_case =
| Is_skip
| Is_not_skip

val skip_dec : prog -> skip_case

val expand : bexpr -> Symb.store -> prog -> Symb.state list

val reachable : Symb.state list -> Symb.state stream

val find_bugs : nat -> prog -> Symb.state result
