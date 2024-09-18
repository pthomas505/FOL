import Batteries.Data.HashMap.Basic
import Batteries.Data.HashMap.WF
import Mathlib.Data.Option.Basic
import Mathlib.Util.CompileInductive


set_option autoImplicit false


namespace NV

inductive Formula : Type
  | Var : String → Formula
  | App : Formula → Formula → Formula
  | Abs : String → Formula → Formula
  deriving Inhabited, DecidableEq

compile_inductive% Formula

open Formula

def Formula.toString : Formula → String
  | Var x => x
  | App phi psi => s! "({phi.toString} {psi.toString})"
  | Abs x phi => s! "(λ {x}. {phi.toString})"

instance : ToString Formula :=
  { toString := fun F => F.toString }

instance : Repr Formula :=
  { reprPrec := fun F _ => F.toString.toFormat }

end NV


namespace LN

inductive Term
| F : String → Term
| B : ℕ → Term
  deriving Inhabited, DecidableEq

open Term

def Term.toString : Term → String
  | F x => x
  | B n => s! "{n}"

inductive Formula : Type
  | Var : Term → Formula
  | App : Formula → Formula → Formula
  | Abs : Formula → Formula
  deriving Inhabited, DecidableEq

compile_inductive% Formula

open Formula

def Formula.toString : Formula → String
  | Var x => x.toString
  | App phi psi => s! "({phi.toString} {psi.toString})"
  | Abs phi => s! "(λ {phi.toString})"

instance : ToString Formula :=
  { toString := fun F => F.toString }

instance : Repr Formula :=
  { reprPrec := fun F _ => F.toString.toFormat }

end LN


def NVToLNAux (env : Batteries.HashMap String ℕ) : NV.Formula → LN.Formula
| NV.Formula.Var x =>
    let opt := env.find? x
    if h : Option.isSome opt
    then
      let i := Option.get opt h
      LN.Formula.Var (LN.Term.B i)
    else LN.Formula.Var (LN.Term.F x)
| NV.Formula.App phi psi =>
    LN.Formula.App (NVToLNAux env phi) (NVToLNAux env psi)
| NV.Formula.Abs x phi =>
    let env' := (Batteries.HashMap.mapVal (fun _ val => val + 1) env).insert x 0
    LN.Formula.Abs (NVToLNAux env' phi)

def NVToLN (F : NV.Formula) : LN.Formula :=
  NVToLNAux Batteries.HashMap.empty F

#eval NVToLN (NV.Formula.Abs "x" (NV.Formula.Abs "x" (NV.Formula.Var "x")))
