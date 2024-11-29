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
def replace
  (P : PredName_)
  (zs : List VarName_)
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
  | not_ phi => not_ (replace P zs H phi)
  | imp_ phi psi =>
      imp_
      (replace P zs H phi)
      (replace P zs H psi)
  | and_ phi psi =>
      and_
      (replace P zs H phi)
      (replace P zs H psi)
  | or_ phi psi =>
      or_
      (replace P zs H phi)
      (replace P zs H psi)
  | iff_ phi psi =>
      iff_
      (replace P zs H phi)
      (replace P zs H psi)
  | forall_ x phi => forall_ x (replace P zs H phi)
  | exists_ x phi => exists_ x (replace P zs H phi)
  | def_ X xs => def_ X xs


/--
  Helper function for admits.
-/
def admitsAux
  (P : PredName_)
  (zs : List VarName_)
  (H : Formula)
  (binders : Finset VarName_) : Formula → Prop
  | pred_const_ _ _ => True
  | pred_var_ X ts =>
      if X = P ∧ ts.length = zs.length
      then
        Sub.Var.All.Rec.admits (Function.updateListITE id zs ts) H ∧
            /-
              Suppose F is the formula that the predicate X ts occurs in.
              Ensures that the free variables in H that are not being replaced by a variable in ts do not become bound variables in F. The bound variables in F are in the 'binders' set.
              The zs are the free variables in H that are being replaced by the variables in ts.
            (is_free_in x H ∧ x ∉ zs) := x is a free variable in H that is not being replaced by a variable in ts.
            -/
          ∀ x : VarName_, x ∈ binders → ¬(var_is_free_in x H ∧ x ∉ zs)
      else True
  | eq_ _ _ => True
  | true_ => True
  | false_ => True
  | not_ phi => admitsAux P zs H binders phi
  | imp_ phi psi =>
      admitsAux P zs H binders phi ∧
      admitsAux P zs H binders psi
  | and_ phi psi =>
      admitsAux P zs H binders phi ∧
      admitsAux P zs H binders psi
  | or_ phi psi =>
      admitsAux P zs H binders phi ∧
      admitsAux P zs H binders psi
  | iff_ phi psi =>
      admitsAux P zs H binders phi ∧
      admitsAux P zs H binders psi
  | forall_ x phi => admitsAux P zs H (binders ∪ {x}) phi
  | exists_ x phi => admitsAux P zs H (binders ∪ {x}) phi
  | def_ _ _ => True


/--
  admits P zs H F := True if and only if there is no variable in (H.free_var_set \ zs) that becomes a bound occurrence in the formula (replace P zs H F).
-/
def admits
  (P : PredName_)
  (zs : List VarName_)
  (H : Formula)
  (F : Formula) :
  Prop :=
  admitsAux P zs H ∅ F


lemma replace_no_predVar
  (P : PredName_)
  (zs : List VarName_)
  (H : Formula)
  (F : Formula)
  (h1 : F.pred_var_set = ∅) :
  replace P zs H F = F :=
  by
  induction F
  case pred_const_ X xs =>
    simp only [replace]
  case pred_var_ X xs =>
    simp only [predVarSet] at h1
    simp at h1
  case eq_ x y =>
    simp only [replace]
  case true_ | false_ =>
    simp only [replace]
  case not_ phi phi_ih =>
    simp only [predVarSet] at h1

    simp only [replace]
    congr!
    exact phi_ih h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [predVarSet] at h1
    simp only [Finset.union_eq_empty] at h1

    cases h1
    case intro h1_left h1_right =>
      simp only [replace]
      congr!
      · exact phi_ih h1_left
      · exact psi_ih h1_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [predVarSet] at h1

    simp only [replace]
    congr!
    exact phi_ih h1
  case def_ X xs =>
    simp only [replace]


/--
  Helper function for I'.
-/
def Interpretation_.usingPred
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
  (E : Env)
  (P : PredName_)
  (zs : List VarName_)
  (H : Formula) :
  Interpretation_ D :=
  (Interpretation_.usingPred D I (
    fun (Q : PredName_) (ds : List D) =>
      if Q = P ∧ ds.length = zs.length
      then holds D I (Function.updateListITE V zs ds) E H
      else I.pred_var_ Q ds
  ))


theorem substitution_theorem_aux
  (D : Type)
  (I : Interpretation_ D)
  (V V' : Valuation_ D)
  (E : Env)
  (F : Formula)
  (P : PredName_)
  (zs : List VarName_)
  (H : Formula)
  (binders : Finset VarName_)
  (h1 : admitsAux P zs H binders F)
  (h2 : ∀ x : VarName_, x ∉ binders → V x = V' x) :
  holds D (I' D I V' E P zs H) V E F ↔
    holds D I V E (replace P zs H F) :=
  by
  set E_ref := E
  induction E generalizing F binders V
  all_goals
    induction F generalizing binders V
    case pred_const_ X xs =>
      simp only [replace]
      simp only [holds]
      simp only [I']
      simp only [Interpretation_.usingPred]
    case pred_var_ X xs =>
        simp only [admitsAux] at h1

        simp only [replace]
        simp only [holds]
        simp only [I']
        simp only [Interpretation_.usingPred]
        simp
        split_ifs at h1
        case pos c1 =>
          simp only [Sub.Var.All.Rec.admits] at h1
          simp at h1

          cases h1
          case intro h1_left h1_right =>
            have s1 :
              holds D I (V ∘ Function.updateListITE id zs xs) E_ref H ↔
                holds D I V E_ref (Sub.Var.All.Rec.fastReplaceFree (Function.updateListITE id zs xs) H) :=
              by
              exact Sub.Var.All.Rec.substitution_theorem D I V E_ref (Function.updateListITE id zs xs) H h1_left

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
      simp only [replace]
      simp only [holds]
    case true_ | false_ =>
      simp only [replace]
      simp only [holds]
    case not_ phi phi_ih =>
      simp only [admitsAux] at h1

      simp only [replace]
      simp only [holds]
      congr! 1
      exact phi_ih V binders h1 h2
    case
        imp_ phi psi phi_ih psi_ih
      | and_ phi psi phi_ih psi_ih
      | or_ phi psi phi_ih psi_ih
      | iff_ phi psi phi_ih psi_ih =>
      simp only [admitsAux] at h1

      simp only [replace]
      simp only [holds]
      cases h1
      case intro h1_left h1_right =>
        congr! 1
        · exact phi_ih V binders h1_left h2
        · exact psi_ih V binders h1_right h2
    case forall_ x phi phi_ih | exists_ x phi phi_ih =>
      simp only [admitsAux] at h1

      simp only [replace]
      simp only [holds]
      first | apply forall_congr' | apply exists_congr
      intro d
      apply phi_ih (Function.updateITE V x d) (binders ∪ {x}) h1
      intro v a1
      simp only [Function.updateITE]
      simp at a1
      push_neg at a1
      cases a1
      case h.intro a1_left a1_right =>
        simp only [if_neg a1_right]
        exact h2 v a1_left

  case nil.def_ X xs =>
    simp only [replace]
    simp only [E_ref]
    simp only [holds]

  case cons.def_ hd tl ih X xs =>
    simp only [replace]
    simp only [E_ref]
    simp only [holds]
    split_ifs
    case _ c1 =>
      specialize ih (Function.updateListITE V hd.args (List.map V xs)) hd.q
      simp only [replace_no_predVar P zs H hd.q hd.h2] at ih
      apply Holds_coincide_PredVar
      · simp only [I']
        simp only [Interpretation_.usingPred]
      · simp only [pred_var_occurs_in_iff_mem_pred_var_set]
        simp only [hd.h2]
        simp
    case _ c1 =>
      apply Holds_coincide_PredVar
      · simp only [I']
        simp only [Interpretation_.usingPred]
      · simp only [pred_var_occurs_in]
        simp


theorem substitution_theorem
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env)
  (F : Formula)
  (P : PredName_)
  (zs : List VarName_)
  (H : Formula)
  (h1 : admits P zs H F) :
  holds D (I' D I V E P zs H) V E F ↔
    holds D I V E (replace P zs H F) :=
  by
  apply substitution_theorem_aux D I V V E F P zs H ∅
  · exact h1
  · simp


theorem substitution_is_valid
  (F : Formula)
  (P : PredName_)
  (zs : List VarName_)
  (H : Formula)
  (h1 : admits P zs H F)
  (h2 : F.is_valid) :
  (replace P zs H F).is_valid :=
  by
  simp only [is_valid] at h2

  simp only [is_valid]
  intro D I V E
  simp only [← substitution_theorem D I V E F P zs H h1]
  apply h2


#lint
