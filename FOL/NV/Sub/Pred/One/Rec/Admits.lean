import FOL.NV.Sub.Pred.One.Rec.Replace
import FOL.NV.Sub.Var.All.Rec.Admits


set_option autoImplicit false


namespace FOL.NV.Sub.Pred.One.Rec

open Formula_


/--
  Helper function for `admits_pred_one_rec`.
-/
def admits_pred_one_rec_aux
  (P : PredName_)
  (zs : List VarName_)
  (H : Formula_)
  (binders : Finset VarName_) : Formula_ → Prop
  | pred_const_ _ _ => True
  | pred_var_ X ts =>
      if X = P ∧ ts.length = zs.length
      then
        Sub.Var.All.Rec.admits_var_all_rec (Function.updateListITE id zs ts) H ∧
            /-
              Suppose `F` is the formula that the predicate `X ts` occurs in.
              Ensures that the free variables in `H` that are not being replaced by a variable in `ts` do not become bound variables in `F`. The bound variables in `F` are in the `binders` set.
              The `zs` are the free variables in `H` that are being replaced by the variables in `ts`.
              `is_free_in x H ∧ x ∉ zs` := `x` is a free variable in `H` that is not being replaced by a variable in `ts`.
            -/
          ∀ x : VarName_, x ∈ binders → ¬(var_is_free_in x H ∧ x ∉ zs)
      else True
  | eq_ _ _ => True
  | true_ => True
  | false_ => True
  | not_ phi => admits_pred_one_rec_aux P zs H binders phi
  | imp_ phi psi =>
      admits_pred_one_rec_aux P zs H binders phi ∧
      admits_pred_one_rec_aux P zs H binders psi
  | and_ phi psi =>
      admits_pred_one_rec_aux P zs H binders phi ∧
      admits_pred_one_rec_aux P zs H binders psi
  | or_ phi psi =>
      admits_pred_one_rec_aux P zs H binders phi ∧
      admits_pred_one_rec_aux P zs H binders psi
  | iff_ phi psi =>
      admits_pred_one_rec_aux P zs H binders phi ∧
      admits_pred_one_rec_aux P zs H binders psi
  | forall_ x phi => admits_pred_one_rec_aux P zs H (binders ∪ {x}) phi
  | exists_ x phi => admits_pred_one_rec_aux P zs H (binders ∪ {x}) phi
  | def_ _ _ => True


/--
  `admits_pred_one_rec P zs H F` := True if and only if there is no variable in `H.free_var_set \ zs` that becomes a bound occurrence in the formula `replace_pred_one_rec P zs H F`.
-/
def admits_pred_one_rec
  (P : PredName_)
  (zs : List VarName_)
  (H : Formula_)
  (F : Formula_) :
  Prop :=
  admits_pred_one_rec_aux P zs H ∅ F


lemma replace_pred_one_rec_pred_var_set_is_empty
  (P : PredName_)
  (zs : List VarName_)
  (H : Formula_)
  (F : Formula_)
  (h1 : F.pred_var_set = ∅) :
  replace_pred_one_rec P zs H F = F :=
  by
  induction F
  case pred_const_ X xs =>
    simp only [replace_pred_one_rec]
  case pred_var_ X xs =>
    simp only [pred_var_set] at h1
    simp at h1
  case eq_ x y =>
    simp only [replace_pred_one_rec]
  case true_ | false_ =>
    simp only [replace_pred_one_rec]
  case not_ phi phi_ih =>
    simp only [pred_var_set] at h1

    simp only [replace_pred_one_rec]
    congr!
    exact phi_ih h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [pred_var_set] at h1
    simp only [Finset.union_eq_empty] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    simp only [replace_pred_one_rec]
    congr!
    · exact phi_ih h1_left
    · exact psi_ih h1_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [pred_var_set] at h1

    simp only [replace_pred_one_rec]
    congr!
    exact phi_ih h1
  case def_ X xs =>
    simp only [replace_pred_one_rec]


/--
  Helper function for `I'`.
-/
def Interpretation_.using_pred
  (D : Type)
  (I : Interpretation_ D)
  (pred_ : PredName_ → List D → Prop) :
  Interpretation_ D := {
    nonempty := I.nonempty
    pred_const_ := I.pred_const_
    pred_var_ := pred_ }


/--
  Helper function for the substitution theorem.
-/
def I'
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (P : PredName_)
  (zs : List VarName_)
  (H : Formula_) :
  Interpretation_ D :=
  (Interpretation_.using_pred D I (
    fun (Q : PredName_) (ds : List D) =>
      if Q = P ∧ ds.length = zs.length
      then holds D I (Function.updateListITE V zs ds) E H
      else I.pred_var_ Q ds
  ))


theorem substitution_theorem_admits_pred_one_rec_aux
  (D : Type)
  (I : Interpretation_ D)
  (V V' : Valuation_ D)
  (E : Env_)
  (F : Formula_)
  (P : PredName_)
  (zs : List VarName_)
  (H : Formula_)
  (binders : Finset VarName_)
  (h1 : admits_pred_one_rec_aux P zs H binders F)
  (h2 : ∀ x : VarName_, x ∉ binders → V x = V' x) :
  holds D (I' D I V' E P zs H) V E F ↔
    holds D I V E (replace_pred_one_rec P zs H F) :=
  by
  set E_ref := E
  induction E generalizing F binders V
  all_goals
    induction F generalizing binders V
    case pred_const_ X xs =>
      simp only [replace_pred_one_rec]
      simp only [holds]
      simp only [I']
      simp only [Interpretation_.using_pred]
    case pred_var_ X xs =>
      simp only [admits_pred_one_rec_aux] at h1

      simp only [replace_pred_one_rec]
      simp only [holds]
      simp only [I']
      simp only [Interpretation_.using_pred]
      simp
      split_ifs at h1
      case pos c1 =>
        simp only [Sub.Var.All.Rec.admits_var_all_rec] at h1
        simp at h1
        obtain ⟨h1_left, h1_right⟩ := h1

        have s1 :
          holds D I (V ∘ Function.updateListITE id zs xs) E_ref H ↔
            holds D I V E_ref (Sub.Var.All.Rec.fast_replace_free_var_all_rec (Function.updateListITE id zs xs) H) := Sub.Var.All.Rec.substitution_theorem_admits_var_all_rec D I V E_ref (Function.updateListITE id zs xs) H h1_left

        simp only [Function.updateListITE_comp] at s1
        simp at s1

        have s2 :
          holds D I (Function.updateListITE V zs (List.map V xs)) E_ref H ↔ holds D I (Function.updateListITE V' zs (List.map V xs)) E_ref H :=
        by
          apply holds_coincide_var
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
        exact s1
      case neg c1 =>
        split_ifs
        simp only [holds]
    case eq_ x y =>
      simp only [replace_pred_one_rec]
      simp only [holds]
    case true_ | false_ =>
      simp only [replace_pred_one_rec]
      simp only [holds]
    case not_ phi phi_ih =>
      simp only [admits_pred_one_rec_aux] at h1

      simp only [replace_pred_one_rec]
      simp only [holds]
      congr! 1
      exact phi_ih V binders h1 h2
    case
        imp_ phi psi phi_ih psi_ih
      | and_ phi psi phi_ih psi_ih
      | or_ phi psi phi_ih psi_ih
      | iff_ phi psi phi_ih psi_ih =>
      simp only [admits_pred_one_rec_aux] at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      simp only [replace_pred_one_rec]
      simp only [holds]
      congr! 1
      · exact phi_ih V binders h1_left h2
      · exact psi_ih V binders h1_right h2
    case forall_ x phi phi_ih | exists_ x phi phi_ih =>
      simp only [admits_pred_one_rec_aux] at h1

      simp only [replace_pred_one_rec]
      simp only [holds]
      first | apply forall_congr' | apply exists_congr
      intro d
      apply phi_ih (Function.updateITE V x d) (binders ∪ {x}) h1
      intro v a1
      simp only [Function.updateITE]
      simp at a1
      obtain ⟨a1_left, a1_right⟩ := a1
      simp only [if_neg a1_right]
      exact h2 v a1_left

  case nil.def_ X xs =>
    simp only [replace_pred_one_rec]
    simp only [E_ref]
    simp only [holds]

  case cons.def_ hd tl ih X xs =>
    simp only [replace_pred_one_rec]
    simp only [E_ref]
    simp only [holds]
    split_ifs
    case _ c1 =>
      specialize ih (Function.updateListITE V hd.args (List.map V xs)) hd.q
      simp only [replace_pred_one_rec_pred_var_set_is_empty P zs H hd.q hd.h2] at ih
      apply holds_coincide_pred_var
      · simp only [I']
        simp only [Interpretation_.using_pred]
      · simp only [pred_var_occurs_in_iff_mem_pred_var_set]
        simp only [hd.h2]
        simp
    case _ c1 =>
      apply holds_coincide_pred_var
      · simp only [I']
        simp only [Interpretation_.using_pred]
      · simp only [pred_var_occurs_in]
        simp


theorem substitution_theorem_admits_pred_one_rec
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (F : Formula_)
  (P : PredName_)
  (zs : List VarName_)
  (H : Formula_)
  (h1 : admits_pred_one_rec P zs H F) :
  holds D (I' D I V E P zs H) V E F ↔
    holds D I V E (replace_pred_one_rec P zs H F) :=
  by
  apply substitution_theorem_admits_pred_one_rec_aux D I V V E F P zs H ∅
  · exact h1
  · simp


theorem substitution_is_valid_admits_pred_one_rec
  (F : Formula_)
  (P : PredName_)
  (zs : List VarName_)
  (H : Formula_)
  (h1 : admits_pred_one_rec P zs H F)
  (h2 : F.is_valid) :
  (replace_pred_one_rec P zs H F).is_valid :=
  by
  simp only [is_valid] at h2

  simp only [is_valid]
  intro D I V E
  simp only [← substitution_theorem_admits_pred_one_rec D I V E F P zs H h1]
  apply h2


#lint
