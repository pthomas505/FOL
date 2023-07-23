import FOL.Binders
import FOL.Definition
import FOL.FunctionUpdateIte
import FOL.Tactics


namespace FOL

open Formula


/--
  The interpretation of a first order language. The assignment of a denotation to each non-logical symbol.

  D is the domain of discourse.
-/
structure Interpretation (D : Type) : Type :=
  /--
    The domain of discourse is not empty.
  -/
  (nonempty : Nonempty D)

  /--
    The assignment to each predicate symbol of a function mapping lists of elements of the domain of discourse to {T, F}.
  -/
  (pred_const_ : PredName → (List D → Prop))

  /--
    The assignment to each predicate symbol of a function mapping lists of elements of the domain of discourse to {T, F}.
  -/
  (pred_var_ : PredName → (List D → Prop))

instance (D : Type) [Inhabited D] : Inhabited (Interpretation D) :=
  Inhabited.mk {
    nonempty := by infer_instance
    pred_const_ := fun _ _ => False
    pred_var_ := fun _ _ => False
  }

/--
  The assignment of an element of the domain of discourse to each variable.
-/
def VarAssignment (D : Type) : Type := VarName → D

instance (D : Type) [Inhabited D] : Inhabited (VarAssignment D) :=
  by
  unfold VarAssignment
  exact inferInstance


/--
  The evaluation of formulas to truth values.
-/
def Holds
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D) : Env → Formula → Prop
  | _, pred_const_ X xs => I.pred_const_ X (xs.map V)
  | _, pred_var_ X xs => I.pred_var_ X (xs.map V)
  | _, eq_ x y => V x = V y
  | _, true_ => True
  | _, false_ => False
  | E, not_ phi => ¬ Holds D I V E phi
  | E, imp_ phi psi =>
    have : sizeOf psi < sizeOf (imp_ phi psi) := by simp
    Holds D I V E phi → Holds D I V E psi
  | E, and_ phi psi =>
    have : sizeOf psi < sizeOf (and_ phi psi) := by simp
    Holds D I V E phi ∧ Holds D I V E psi
  | E, or_ phi psi =>
    have : sizeOf psi < sizeOf (or_ phi psi) := by simp
    Holds D I V E phi ∨ Holds D I V E psi
  | E, iff_ phi psi =>
    have : sizeOf psi < sizeOf (iff_ phi psi) := by simp
    Holds D I V E phi ↔ Holds D I V E psi
  | E, forall_ x phi =>
    have : sizeOf phi < sizeOf (forall_ x phi) := by simp
    ∀ d : D, Holds D I (Function.updateIte V x d) E phi
  | E, exists_ x phi =>
    have : sizeOf phi < sizeOf (exists_ x phi) := by simp
    ∃ d : D, Holds D I (Function.updateIte V x d) E phi
  | ([] : Env), def_ _ _ => False
  | d :: E, def_ name args =>
    if name = d.name ∧ args.length = d.args.length
    then Holds D I (Function.updateListIte V d.args (List.map V args)) E d.q
    else Holds D I V E (def_ name args)
termination_by _ E phi => (E.length, phi)


/--
  The definition of valid formulas.

  Formula.isValid F := True if and only if F evaluates to True in every combination of domain of discourse, interpretation and variable assignment.
-/
def Formula.IsValid (F : Formula) : Prop :=
  ∀ (D : Type) (I : Interpretation D) (V : VarAssignment D) (E : Env), Holds D I V E F


theorem Holds_coincide_Var
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (E : Env)
  (F : Formula)
  (h1 : ∀ v : VarName, isFreeIn v F → V v = V' v) :
  Holds D I V E F ↔ Holds D I V' E F :=
  by
  induction E generalizing F V V'
  all_goals
    induction F generalizing V V'
    case pred_const_ X xs | pred_var_ X xs =>
      unfold isFreeIn at h1

      simp only [Holds]
      congr! 1
      simp only [List.map_eq_map_iff]
      exact h1
    case eq_ x y =>
      unfold isFreeIn at h1
      simp at h1

      simp only [Holds]
      cases h1
      case intro h1_left h1_right =>
        simp only [h1_left, h1_right]
    case true_ | false_ =>
      simp only [Holds]
    case not_ phi phi_ih =>
      simp only [Holds]
      congr! 1
      exact phi_ih V V' h1
    case
        imp_ phi psi phi_ih psi_ih
      | and_ phi psi phi_ih psi_ih
      | or_ phi psi phi_ih psi_ih
      | iff_ phi psi phi_ih psi_ih =>
      unfold isFreeIn at h1

      simp only [Holds]
      congr! 1
      · apply phi_ih V V'
        intro v a1
        apply h1
        left
        exact a1
      · apply psi_ih V V'
        intro v a1
        apply h1
        right
        exact a1
    case forall_ x phi phi_ih | exists_ x phi phi_ih =>
      unfold isFreeIn at h1
      simp at h1

      simp only [Holds]
      first | apply forall_congr' | apply exists_congr
      intro d
      apply phi_ih
      intro v a1
      simp only [Function.updateIte]
      split_ifs
      case _ c1 =>
        rfl
      case _ c1 =>
        exact h1 v c1 a1

  case nil.def_ X xs =>
    unfold Holds
    rfl

  case cons.def_ hd tl ih X xs =>
    unfold isFreeIn at h1

    simp only [Holds]
    split_ifs
    case inl c1 =>
      apply ih
      intro v a1
      simp only [isFreeIn_iff_mem_freeVarSet v hd.q] at a1
      
      have s2 : v ∈ List.toFinset hd.args
      apply Finset.mem_of_subset hd.h1 a1

      apply Function.updateListIte_fun_coincide_mem_eq_len V V' hd.args xs v h1
      · simp only [List.mem_toFinset] at s2
        exact s2
      · cases c1
        case _ c1_left c1_right =>
          simp only [eq_comm]
          exact c1_right
    case inr c1 =>
      apply ih
      unfold isFreeIn
      exact h1


theorem Holds_coincide_PredVar
  (D : Type)
  (I I' : Interpretation D)
  (V : VarAssignment D)
  (E : Env)
  (F : Formula)
  (h1 : I.pred_const_ = I'.pred_const_)
  (h2 : ∀ (P : PredName) (ds : List D),
    predVarOccursIn P ds.length F →
      (I.pred_var_ P ds ↔ I'.pred_var_ P ds)) :
  Holds D I V E F ↔ Holds D I' V E F :=
  by
  induction E generalizing F V
  all_goals
    induction F generalizing V
    case pred_const_ X xs =>
      unfold Holds
      simp only [h1]
    case pred_var_ X xs =>
      unfold predVarOccursIn at h2
      simp at h2

      unfold Holds
      apply h2
      · rfl
      · simp
    case eq_ x y =>
      unfold Holds
      rfl
    case true_ | false_ =>
      unfold Holds
      rfl
    case not_ phi phi_ih =>
      unfold predVarOccursIn at h2

      unfold Holds
      congr! 1
      exact phi_ih V h2
    case
        imp_ phi psi phi_ih psi_ih
      | and_ phi psi phi_ih psi_ih
      | or_ phi psi phi_ih psi_ih
      | iff_ phi psi phi_ih psi_ih =>
      unfold predVarOccursIn at h2

      simp only [Holds]
      congr! 1
      · apply phi_ih
        intro P ds a1
        apply h2
        left
        exact a1
      · apply psi_ih
        intro P ds a1
        apply h2
        right
        exact a1
    case forall_ x phi phi_ih | exists_ x phi phi_ih =>
      unfold predVarOccursIn at h2

      unfold Holds
      first | apply forall_congr' | apply exists_congr
      intro d
      exact phi_ih (Function.updateIte V x d) h2

  case nil.def_ X xs =>
    simp only [Holds]

  case cons.def_ hd tl ih X xs =>
    simp only [Holds]
    split_ifs
    case inl c1 =>
      apply ih
      intro P ds a1
      simp only [predVarOccursIn_iff_mem_predVarSet P ds.length] at a1
      simp only [hd.h2] at a1
      simp at a1
    case inr c1 =>
      apply ih
      intro P ds a1
      unfold predVarOccursIn at a1
      contradiction


lemma Holds_coincide_Env
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (E E' : Env)
  (F : Formula)
  (h1 : ∃ (E1 : Env), E' = E1 ++ E)
  (h2 : F.all_def_in_env E)
  (h3 : E'.nodup_) :
  Holds D I V E' F ↔ Holds D I V E F :=
  by
  induction F generalizing V
  any_goals
    unfold all_def_in_env at h2

    simp only [Holds]
  case not_ phi phi_ih =>
    congr! 1
    exact phi_ih V h2
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    cases h2
    case intro h2_left h2_right =>
      congr! 1
      · exact phi_ih V h2_left
      · exact psi_ih V h2_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    first | apply forall_congr' | apply exists_congr
    intro d
    apply phi_ih
    exact h2
  case def_ X xs =>
    apply Exists.elim h1
    intro E1 h1_1
    clear h1

    unfold all_def_in_env at h2
    apply Exists.elim h2
    intro a h2_1
    clear h2

    unfold Env.nodup_ at h3

    subst h1_1

    induction E1
    case nil =>
      simp
    case cons E1_hd E1_tl E1_ih =>
      simp at h3

      cases h2_1
      case intro h2_1_left h2_1_right =>
        cases h2_1_right
        case intro h2_1_right_left h2_1_right_right =>
          cases h3
          case intro h3_left h3_right =>
            simp
            simp only [Holds]
            split_ifs
            case _ c1 =>
              cases c1
              case intro c1_left c1_right =>
                exfalso
                apply h3_left a
                · right
                  exact h2_1_left
                · subst c1_left
                  exact h2_1_right_left
                · trans List.length xs
                  · simp only [eq_comm]
                    exact c1_right
                  · exact h2_1_right_right
            case _ c1 =>
              exact E1_ih h3_right


--#lint

end FOL
