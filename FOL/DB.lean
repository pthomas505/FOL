import Lean.Data.RBMap
import Mathlib.Util.CompileInductive

set_option autoImplicit false


notation "ℕ" => Nat


namespace NV

inductive Formula : Type
  | Var : String → Formula
  | App : Formula → Formula → Formula
  | Abs : String → Formula → Formula
  deriving Inhabited, DecidableEq

  compile_inductive% Formula

end NV


namespace DB

inductive Formula : Type
  | Var : Int → Formula
  | App : Formula → Formula → Formula
  | Abs : Formula → Formula
  deriving Inhabited, DecidableEq

  compile_inductive% Formula

open Formula

-- The d place shift of a term t above a cutoff c.
def shiftAux (c : Int) (d : Int) : Formula → Formula
  | Var k => if k < c then Var k else Var (k + d)
  | App t1 t2 => App (shiftAux c d t1) (shiftAux c d t2)
  | Abs t => Abs (shiftAux (c + 1) d t)

-- The d place shift of every free variable in the term t.
def shift (d : Int) (t : Formula) : Formula := shiftAux 0 d t

-- sub j s t := [j -> s] t
def sub (j : Int) (s : Formula) : Formula → Formula
  | Var k => if k = j then s else Var k
  | App t1 t2 => App (sub j s t1) (sub j s t2)
  | Abs t1 => Abs (sub (j + 1) (shift 1 s) t1)


-- beta reduction
-- [x -> v](λ x. t)
def reduce (t : Formula) (v : Formula) :=
  shift (-1) (sub 0 (shift 1 v) t)


end DB


namespace LN

inductive Term
| F : String → Term
| B : Int → Term
  deriving Inhabited, DecidableEq

open Term

inductive Formula : Type
  | Var : Term → Formula
  | App : Formula → Formula → Formula
  | Abs : Formula → Formula
  deriving Inhabited, DecidableEq

  compile_inductive% Formula

open Formula


def betaReduceAux (outer : Int) (t : Formula) : Formula → Formula
  | Var (F name) => Var (F name)
  | Var (B index) => if index = outer then t else Var (B index)
  | App t1 t2 => App (betaReduceAux outer t t1) (betaReduceAux outer t t2)
  | Abs t1 => Abs (betaReduceAux (outer + 1) t t1)

-- (λ x . f) t -> f[x -> t]
def betaReduce (t : Formula) (F : Formula) : Formula :=
  betaReduceAux 0 t F

end LN

