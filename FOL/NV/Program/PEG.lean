/-
  https://bford.info/pub/lang/peg.pdf

  https://github.com/jayhardee9/peg-formalization/blob/master/peg.v
-/

import Std
import Mathlib.Util.CompileInductive

import Mathlib.Data.Finset.Basic


set_option autoImplicit false


/--
  The definition of parsing expressions.

  V_N is a finite set of nonterminal symbols.
  V_T is a finite set of terminal symbols.
-/
inductive PE (V_N V_T : Type) : Type
  | empty : PE V_N V_T
  | any : PE V_N V_T
  | terminal : V_T → PE V_N V_T
  | nonTerminal : V_N → PE V_N V_T
  | seq : PE V_N V_T → PE V_N V_T → PE V_N V_T
  | prior : PE V_N V_T → PE V_N V_T → PE V_N V_T
  | star : PE V_N V_T → PE V_N V_T
  | notP : PE V_N V_T → PE V_N V_T
  deriving Inhabited, DecidableEq

compile_inductive% PE

open PE


structure G
  (V_N V_T : Type)
  [Finite V_N]
  [Finite V_T] : Type :=
  (R : V_N → PE V_N V_T)
  (e_S : PE V_N V_T)


inductive Interpretation
  (V_N V_T : Type)
  (R : V_N → PE V_N V_T) :
  (PE V_N V_T × List V_T) → (Nat × Option (List V_T)) → Prop

  | empty
    (xs : List V_T) :
    Interpretation V_N V_T R (empty, xs) (1, Option.some [])

  | terminal_success
    (a : V_T)
    (xs : List V_T) :
    Interpretation V_N V_T R (terminal a, a :: xs) (1, Option.some [a])

  | terminal_failure_1
    (a b : V_T)
    (xs : List V_T) :
    ¬ a = b →
    Interpretation V_N V_T R (terminal a, b :: xs) (1, Option.none)

  | terminal_failure_2
    (a b : V_T)
    (xs : List V_T) :
    Interpretation V_N V_T R (terminal a, []) (1, Option.none)

  | nonTerminal
    (A : V_N)
    (xs : List V_T)
    (n : Nat)
    (o : Option (List V_T)) :
    Interpretation V_N V_T R (R A, xs) (n, o) →
    Interpretation V_N V_T R (nonTerminal A, xs) ((n + 1), o)

  | seq_success
    (e1 e2 : PE V_N V_T)
    (xs_1 xs_2 ys : List V_T)
    (n1 n2 : Nat) :
    Interpretation V_N V_T R (e1, xs_1 ++ xs_2 ++ ys) (n1, Option.some xs_1) →
    Interpretation V_N V_T R (e2, xs_2 ++ ys) (n2, Option.some xs_2) →
    Interpretation V_N V_T R (seq e1 e2, xs_1 ++ xs_2 ++ ys) (n1 + n2 + 1, Option.some (xs_1 ++ xs_2))

  | seq_failure_1
    (e1 e2 : PE V_N V_T)
    (xs : List V_T)
    (n1 : Nat) :
    Interpretation V_N V_T R (e1, xs) (n1, Option.none) →
    Interpretation V_N V_T R (seq e1 e2, xs) (n1 + 1, Option.none)

  | seq_failure_2
    (e1 e2 : PE V_N V_T)
    (xs_1 ys : List V_T)
    (n1 n2 : Nat) :
    Interpretation V_N V_T R (e1, xs_1 ++ ys) (n1, Option.some xs_1) →
    Interpretation V_N V_T R (e2, ys) (n2, Option.none) →
    Interpretation V_N V_T R (seq e1 e2, xs_1 ++ ys) (n1 + n2 + 1, Option.none)

  | prior_1
    (e1 e2 : PE V_N V_T)
    (xs ys : List V_T)
    (n1 n2 : Nat) :
    Interpretation V_N V_T R (e1, xs ++ ys) (n1, Option.some xs) →
    Interpretation V_N V_T R (prior e1 e2, xs ++ ys) (n1 + 1, Option.some xs)

  | prior_2
    (e1 e2 : PE V_N V_T)
    (xs : List V_T)
    (n1 n2 : Nat)
    (o : Option (List V_T)) :
    Interpretation V_N V_T R (e1, xs) (n1, Option.none) →
    Interpretation V_N V_T R (e2, xs) (n2, o) →
    Interpretation V_N V_T R (prior e1 e2, xs) (n1 + n2 + 1, o)

  | star_repetition
    (e : PE V_N V_T)
    (xs_1 xs_2 ys : List V_T)
    (n1 n2 : Nat) :
    Interpretation V_N V_T R (e, xs_1 ++ xs_2 ++ ys) (n1, Option.some xs_1) →
    Interpretation V_N V_T R (star e, xs_2 ++ ys) (n2, Option.some xs_2) →
    Interpretation V_N V_T R (star e, xs_1 ++ xs_2 ++ ys) (n1 + n2 + 1, Option.some (xs_1 ++ xs_2))

  | star_termination
    (e : PE V_N V_T)
    (xs : List V_T)
    (n1 : Nat) :
    Interpretation V_N V_T R (e, xs) (n1, Option.none) →
    Interpretation V_N V_T R (star e, xs) (n1 + 1, Option.some [])

  | notP_1
    (e : PE V_N V_T)
    (xs ys : List V_T)
    (n : Nat) :
    Interpretation V_N V_T R (e, xs ++ ys) (n, Option.some xs) →
    Interpretation V_N V_T R (notP e, xs ++ ys) (n + 1, Option.none)

  | notP_2
    (e : PE V_N V_T)
    (xs : List V_T)
    (n : Nat) :
    Interpretation V_N V_T R (e, xs) (n, Option.none) →
    Interpretation V_N V_T R (notP e, xs) (n + 1, Option.some [])
