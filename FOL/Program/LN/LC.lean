import FOL.Program.LN.Formula
import FOL.Tactics

set_option autoImplicit false


namespace LN

open Var Formula


/--
  Helper function for Formula.lc_at.
-/
def Var.lc_at
  (k : ℕ) :
  Var → Prop
  | free_ _ => True
  | bound_ i => i < k

instance
  (k : ℕ) (v : Var) :
  Decidable (Var.lc_at k v) :=
  by
  cases v
  all_goals
    simp only [lc_at]
    infer_instance


/--
  For k = 0 this is a recursive definition of locally closed.

  Formula.lc_at k F := True if and only if every bound variable in the formula F has an index less than the number of binders that it is under plus k. If this holds for k = 0 then this means that no bound variable in F is out of scope and hence that F is locally closed.
-/
def Formula.lc_at
  (k : ℕ) :
  Formula → Prop
  | pred_ _ vs => ∀ (v : Var), v ∈ vs → (v.lc_at k)
  | not_ phi => phi.lc_at k
  | imp_ phi psi => (phi.lc_at k) ∧ (psi.lc_at k)
  | forall_ _ phi => phi.lc_at (k + 1)

instance (k : ℕ) (F : Formula) : Decidable (Formula.lc_at k F) :=
  by
  induction F generalizing k
  all_goals
    unfold Formula.lc_at
    infer_instance


#eval Formula.lc_at 0 (pred_ "X" [free_ "x"])
#eval Formula.lc_at 0 (pred_ "X" [bound_ 0])
#eval Formula.lc_at 0 (forall_ "x" (pred_ "X" [bound_ 0]))
#eval Formula.lc_at 0 (forall_ "x" (pred_ "X" [bound_ 1]))


#lint
