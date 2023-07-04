import FOL.Sub.All.Rec.SubAllRecAdmits
import FOL.Tactics


namespace FOL

open Formula


-- predicate substitution
-- single
-- https://math.stackexchange.com/a/1374989
/--
  The recursive simultaneous uniform substitution of a single predicate variable in a formula.
-/
def replacePred (P : PredName) (zs : List VarName) (H : Formula) : Formula → Formula
  | pred_const_ X xs => pred_const_ X xs
  | pred_var_ X xs =>
    if X = P ∧ xs.length = zs.length
    then fastReplaceFreeFun (Function.updateListIte id zs xs) H
    else pred_var_ X xs
  | eq_ x y => eq_ x y
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replacePred P zs H phi)
  | imp_ phi psi => imp_ (replacePred P zs H phi) (replacePred P zs H psi)
  | and_ phi psi => and_ (replacePred P zs H phi) (replacePred P zs H psi)
  | or_ phi psi => or_ (replacePred P zs H phi) (replacePred P zs H psi)
  | iff_ phi psi => iff_ (replacePred P zs H phi) (replacePred P zs H psi)
  | forall_ x phi => forall_ x (replacePred P zs H phi)
  | exists_ x phi => exists_ x (replacePred P zs H phi)


def admitsPredAux (P : PredName) (zs : List VarName) (H : Formula) : Finset VarName → Formula → Prop
  | _, pred_const_ _ _ => True
  | binders, pred_var_ X ts =>
    if X = P ∧ ts.length = zs.length
    then
      admitsFun (Function.updateListIte id zs ts) H ∧
          /-
            Suppose F is the formula that the predicate X ts occurs in.
            Ensures that the free variables in H that are not being replaced by a variable in ts do not become bound variables in F. The bound variables in F are in the 'binders' set.
            The zs are the free variables in H that are being replaced by the variables in ts.
           (is_free_in x H ∧ x ∉ zs) := x is a free variable in H that is not being replaced by a variable in ts.
          -/
        ∀ x : VarName, x ∈ binders → ¬(isFreeIn x H ∧ x ∉ zs)
    else True
  | _, eq_ _ _ => True
  | _, true_ => True
  | _, false_ => True
  | binders, not_ phi => admitsPredAux P zs H binders phi
  | binders, imp_ phi psi => admitsPredAux P zs H binders phi ∧ admitsPredAux P zs H binders psi
  | binders, and_ phi psi => admitsPredAux P zs H binders phi ∧ admitsPredAux P zs H binders psi
  | binders, or_ phi psi => admitsPredAux P zs H binders phi ∧ admitsPredAux P zs H binders psi
  | binders, iff_ phi psi => admitsPredAux P zs H binders phi ∧ admitsPredAux P zs H binders psi
  | binders, forall_ x phi => admitsPredAux P zs H (binders ∪ {x}) phi
  | binders, exists_ x phi => admitsPredAux P zs H (binders ∪ {x}) phi


theorem pred_sub_single_aux
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (F : Formula)
  (P : PredName)
  (zs : List VarName)
  (H : Formula)
  (binders : Finset VarName)
  (h1 : admitsPredAux P zs H binders F)
  (h2 : ∀ x : VarName, x ∉ binders → V x = V' x) :
  Holds D
    ⟨
      I.nonempty,
      I.pred_const_,
      fun (Q : PredName) (ds : List D) =>
        if Q = P ∧ ds.length = zs.length
        then Holds D I (Function.updateListIte V' zs ds) H
        else I.pred_var_ Q ds
    ⟩
    V F ↔ Holds D I V (replacePred P zs H F) :=
  by
  induction F generalizing binders V
  case pred_const_ X xs =>
    unfold replacePred
    simp only [Holds]
  case pred_var_ X xs =>
      unfold admitsPredAux at h1
      unfold replacePred
      simp only [Holds]
      --simp only [Interpretation.pred_var_]
      simp
      split_ifs at h1
      case inl c1 =>
        simp at h1
        cases h1
        case intro h1_left h1_right =>
          unfold admitsFun at h1_left

          obtain s1 := substitution_fun_theorem I V (Function.updateListIte id zs xs) H h1_left
          simp only [Function.updateListIte_comp] at s1
          simp only [Function.comp.right_id] at s1
          have s2 :
            Holds D I (Function.updateListIte V zs (List.map V xs)) H ↔
              Holds D I (Function.updateListIte V' zs (List.map V xs)) H :=
            by
            apply Holds_coincide_Var
            intro v a1
            by_cases c2 : v ∈ zs
            · specialize h2 v
              apply Function.updateListIte_mem_eq_len V V' v zs (List.map V xs) c2
              cases c1
              case pos.intro c1_left c1_right =>
                simp only [List.length_map]
                symm
                exact c1_right
            · by_cases c3 : v ∈ binders
              · specialize h1_right v c3 a1
                contradiction
              · specialize h2 v c3
                apply Function.updateListIte_mem'
                exact h2
          simp only [s2] at s1
          split_ifs
          exact s1
      case inr c1 =>
          split_ifs
          rfl
  case eq_ =>
    unfold replacePred
    simp only [Holds]
  case true_ | false_ =>
    unfold replacePred
    simp only [Holds]
  case not_ phi phi_ih =>
    unfold admitsPredAux at h1
    unfold replacePred
    simp only [Holds]
    apply not_congr
    exact phi_ih V binders h1 h2
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold admitsPredAux at h1
    cases h1
    case intro h1_left h1_right =>
    unfold replacePred
    simp only [Holds]
    congr! 1
    · exact phi_ih V binders h1_left h2
    · exact psi_ih V binders h1_right h2
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold admitsPredAux at h1
    unfold replacePred
    simp only [Holds]
    first | apply forall_congr' | apply exists_congr
    intro d
    apply phi_ih (Function.updateIte V x d) (binders ∪ {x}) h1
    intro v a1
    unfold Function.updateIte
    simp only [Finset.mem_union, Finset.mem_singleton] at a1
    push_neg at a1
    cases a1
    case h.intro a1_left a1_right =>
    simp only [if_neg a1_right]
    exact h2 v a1_left


theorem pred_sub_single_valid
  (phi : Formula)
  (P : PredName)
  (zs : List VarName)
  (H : Formula)
  (h1 : admitsPredAux P zs H ∅ phi)
  (h2 : phi.IsValid) : (replacePred P zs H phi).IsValid :=
  by
  unfold IsValid at h2
  unfold IsValid
  intro D I V
  obtain s1 := pred_sub_single_aux D I V V phi P zs H ∅ h1
  simp only [eq_self_iff_true, forall_const] at s1
  simp only [← s1]
  apply h2


--#lint

end FOL

