import FOL.NV.Sub.Var.All.Rec.Admits


set_option autoImplicit false


namespace FOL.NV.Sub.Pred.One.Rec

open Formula


-- predicate substitution
-- single
-- https://math.stackexchange.com/a/1374989
/--
  The recursive simultaneous uniform substitution of a single predicate variable in a formula.
-/
def replacePred
  (P : PredName)
  (zs : List VarName)
  (H : Formula) :
  Formula → Formula
  | pred_const_ X xs => pred_const_ X xs
  | pred_var_ X xs =>
      if X = P ∧ xs.length = zs.length
      then Sub.Var.All.Rec.fastReplaceFree (Function.updateListITE id zs xs) H
      else pred_var_ X xs
  | eq_ x y => eq_ x y
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replacePred P zs H phi)
  | imp_ phi psi =>
      imp_
      (replacePred P zs H phi)
      (replacePred P zs H psi)
  | and_ phi psi =>
      and_
      (replacePred P zs H phi)
      (replacePred P zs H psi)
  | or_ phi psi =>
      or_
      (replacePred P zs H phi)
      (replacePred P zs H psi)
  | iff_ phi psi =>
      iff_
      (replacePred P zs H phi)
      (replacePred P zs H psi)
  | forall_ x phi => forall_ x (replacePred P zs H phi)
  | exists_ x phi => exists_ x (replacePred P zs H phi)
  | def_ X xs => def_ X xs


def admitsPredAux
  (P : PredName)
  (zs : List VarName)
  (H : Formula) :
  Finset VarName → Formula → Prop
  | _, pred_const_ _ _ => True
  | binders, pred_var_ X ts =>
      if X = P ∧ ts.length = zs.length
      then
        Sub.Var.All.Rec.admits (Function.updateListITE id zs ts) H ∧
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
  | binders, imp_ phi psi =>
      admitsPredAux P zs H binders phi ∧
      admitsPredAux P zs H binders psi
  | binders, and_ phi psi =>
      admitsPredAux P zs H binders phi ∧
      admitsPredAux P zs H binders psi
  | binders, or_ phi psi =>
      admitsPredAux P zs H binders phi ∧
      admitsPredAux P zs H binders psi
  | binders, iff_ phi psi =>
      admitsPredAux P zs H binders phi ∧
      admitsPredAux P zs H binders psi
  | binders, forall_ x phi => admitsPredAux P zs H (binders ∪ {x}) phi
  | binders, exists_ x phi => admitsPredAux P zs H (binders ∪ {x}) phi
  | _, def_ _ _ => True


lemma replacePred_no_predVar
  (P : PredName)
  (zs : List VarName)
  (H : Formula)
  (F : Formula)
  (h1 : F.predVarSet = ∅) :
  replacePred P zs H F = F :=
  by
  induction F
  case pred_const_ X xs =>
    unfold replacePred
    rfl
  case pred_var_ X xs =>
    unfold predVarSet at h1

    simp at h1
  case eq_ x y =>
    unfold replacePred
    rfl
  case true_ | false_ =>
    unfold replacePred
    rfl
  case not_ phi phi_ih =>
    unfold predVarSet at h1

    unfold replacePred
    congr!
    exact phi_ih h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold predVarSet at h1
    simp only [Finset.union_eq_empty] at h1

    cases h1
    case intro h1_left h1_right =>
      unfold replacePred
      congr!
      · exact phi_ih h1_left
      · exact psi_ih h1_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold predVarSet at h1

    unfold replacePred
    congr!
    exact phi_ih h1
  case def_ X xs =>
    unfold replacePred
    rfl


theorem pred_sub_single_aux
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (E : Env)
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
        then Holds D I (Function.updateListITE V' zs ds) E H
        else I.pred_var_ Q ds
    ⟩
    V E F ↔ Holds D I V E (replacePred P zs H F) :=
  by
  set E_ref := E
  induction E generalizing F binders V
  all_goals
    induction F generalizing binders V
    case pred_const_ X xs =>
      unfold replacePred
      simp only [Holds]
    case pred_var_ X xs =>
        unfold admitsPredAux at h1

        unfold replacePred
        simp only [Holds]
        simp
        split_ifs at h1
        case pos c1 =>
          unfold Sub.Var.All.Rec.admits at h1
          simp at h1

          cases h1
          case intro h1_left h1_right =>
            have s1 :
              Holds D I (V ∘ Function.updateListITE id zs xs) E_ref H ↔
                Holds D I V E_ref (Sub.Var.All.Rec.fastReplaceFree (Function.updateListITE id zs xs) H) :=
              by
              exact Sub.Var.All.Rec.substitution_theorem D I V E_ref (Function.updateListITE id zs xs) H h1_left

            simp only [Function.updateListITE_comp] at s1
            simp at s1

            have s2 :
              Holds D I (Function.updateListITE V zs (List.map V xs)) E_ref H ↔ Holds D I (Function.updateListITE V' zs (List.map V xs)) E_ref H :=
              by
              apply Holds_coincide_Var
              intro v a1
              by_cases c2 : v ∈ zs
              · apply Function.updateListITE_mem_eq_len V V' v zs (List.map V xs) c2
                cases c1
                case pos.intro c1_left c1_right =>
                  simp
                  symm
                  exact c1_right
              · by_cases c3 : v ∈ binders
                · specialize h1_right v c3 a1
                  contradiction
                · apply Function.updateListITE_mem'
                  exact h2 v c3

            simp only [s2] at s1
            split_ifs
            case pos c2 =>
              exact s1
            case neg _ =>
              exact s1
        case neg c1 =>
          split_ifs
          case pos c2 =>
            contradiction
          case neg c2 =>
            simp only [Holds]
    case eq_ x y =>
      unfold replacePred
      simp only [Holds]
    case true_ | false_ =>
      unfold replacePred
      simp only [Holds]
    case not_ phi phi_ih =>
      unfold admitsPredAux at h1

      unfold replacePred
      simp only [Holds]
      congr! 1
      exact phi_ih V binders h1 h2
    case
        imp_ phi psi phi_ih psi_ih
      | and_ phi psi phi_ih psi_ih
      | or_ phi psi phi_ih psi_ih
      | iff_ phi psi phi_ih psi_ih =>
      unfold admitsPredAux at h1

      unfold replacePred
      simp only [Holds]
      cases h1
      case intro h1_left h1_right =>
        congr! 1
        · exact phi_ih V binders h1_left h2
        · exact psi_ih V binders h1_right h2
    case forall_ x phi phi_ih | exists_ x phi phi_ih =>
      unfold admitsPredAux at h1

      unfold replacePred
      simp only [Holds]
      first | apply forall_congr' | apply exists_congr
      intro d
      apply phi_ih (Function.updateITE V x d) (binders ∪ {x}) h1
      intro v a1
      unfold Function.updateITE
      simp at a1
      push_neg at a1
      cases a1
      case h.intro a1_left a1_right =>
        simp only [if_neg a1_right]
        exact h2 v a1_left

  case nil.def_ X xs =>
    unfold replacePred
    simp only [Holds]

  case cons.def_ hd tl ih X xs =>
    unfold replacePred
    simp only [Holds]
    split_ifs
    case _ c1 =>
      specialize ih (Function.updateListITE V hd.args (List.map V xs)) hd.q
      simp only [replacePred_no_predVar P zs H hd.q hd.h2] at ih
      apply Holds_coincide_PredVar
      · simp
      · simp only [predVarOccursIn_iff_mem_predVarSet]
        simp only [hd.h2]
        simp
    case _ c1 =>
      apply Holds_coincide_PredVar
      · simp
      · unfold predVarOccursIn
        simp


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
  intro D I V E
  obtain s1 := pred_sub_single_aux D I V V E phi P zs H ∅ h1
  simp at s1
  simp only [← s1]
  apply h2


--#lint
