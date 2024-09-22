-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/.E2.9C.94.20strict.20refl/near/471758229


import Lean.Elab.Tactic.Basic

open Lean Elab Tactic


elab "real_rfl" : tactic => do
  let some (_a, lhs, rhs) := (← getMainTarget).eq? | throwError "Not an equality goal"
  if lhs == rhs then
    evalTactic (← `(tactic| rfl))
  else
    logWarning "Not a 'real' equality"

/-- error: Not an equality goal -/
#guard_msgs in
example : True := by
  real_rfl

/--
warning: Not a 'real' equality
-/
#guard_msgs in
example : 2 = 1 + 1 := by
  real_rfl
  rfl

example : 2 = 2 := by
  real_rfl
