import FOL.Program.LN.Formula
import FOL.Tactics

set_option autoImplicit false


namespace LN

open Formula


def Var.sub_Var (σ : Var → Var) : Var → Var
  | free_ x => σ (free_ x)
  | bound_ i => bound_ i


def Formula.sub_Var (σ : Var → Var) : Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.sub_Var σ))
  | not_ phi => not_ (phi.sub_Var σ)
  | imp_ phi psi => imp_ (phi.sub_Var σ) (psi.sub_Var σ)
  | forall_ x phi => forall_ x (phi.sub_Var σ)


--------------------------------------------------


def Var.sub_Str (σ : String → String) : Var → Var
  | free_ x => free_ (σ x)
  | bound_ i => bound_ i


def Formula.sub_Str (σ : String → String) : Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.sub_Str σ))
  | not_ phi => not_ (phi.sub_Str σ)
  | imp_ phi psi => imp_ (phi.sub_Str σ) (psi.sub_Str σ)
  | forall_ x phi => forall_ x (phi.sub_Str σ)
