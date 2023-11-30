import FOL.NV.Formula
import FOL.NV.Binders


namespace FOL

namespace NV

open Formula


structure Definition : Type :=
(name : DefName)
(args : List VarName)
(q : Formula)
(nodup : args.Nodup)
(h1 : q.freeVarSet ⊆ args.toFinset)
(h2 : q.predVarSet = ∅)
deriving DecidableEq


abbrev Env : Type := List Definition

instance : Membership Definition Env :=
  inferInstanceAs (Membership Definition (List Definition))


def Formula.all_def_in_env (E : Env) : Formula → Prop
| pred_const_ _ _ => True
| pred_var_ _ _ => True
| eq_ _ _ => True
| true_ => True
| false_ => True
| not_ phi => phi.all_def_in_env E
| imp_ phi psi =>
    phi.all_def_in_env E ∧
    psi.all_def_in_env E
| and_ phi psi =>
    phi.all_def_in_env E ∧
    psi.all_def_in_env E
| or_ phi psi =>
    phi.all_def_in_env E ∧
    psi.all_def_in_env E
| iff_ phi psi =>
    phi.all_def_in_env E ∧
    psi.all_def_in_env E
| forall_ _ phi => phi.all_def_in_env E
| exists_ _ phi => phi.all_def_in_env E
| def_ X xs =>
  ∃ (d : Definition), d ∈ E ∧ X = d.name ∧ xs.length = d.args.length


instance (E : Env) (F : Formula) : Decidable (F.all_def_in_env E) :=
  by
  induction F
  all_goals
    unfold Formula.all_def_in_env
    infer_instance


def Env.nodup_ : Env → Prop :=
  List.Pairwise (fun (d1 d2 : Definition) => d1.name = d2.name → d1.args.length = d2.args.length → False)
