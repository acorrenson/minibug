
val negb : bool -> bool

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val eqb : z -> z -> bool
 end

type ident = char list

type aexpr =
| Var of ident
| Cst of z
| Add of aexpr * aexpr
| Sub of aexpr * aexpr

type bexpr =
| Bcst of bool
| Ble of aexpr * aexpr
| Beq of aexpr * aexpr
| Bnot of bexpr
| Band of bexpr * bexpr

module Concr :
 sig
  type store = ident -> z

  val aeval : store -> aexpr -> z

  val beval : store -> bexpr -> bool
 end
