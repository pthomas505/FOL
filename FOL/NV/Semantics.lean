import MathlibExtra.FunctionUpdateITE

import FOL.NV.Definition


set_option autoImplicit false


open Formula_


/--
  The interpretation of a first order language. The assignment of a denotation to each non-logical symbol.

  `D` is the domain of discourse.
-/
structure Interpretation_ (D : Type) : Type where
  /--
    The domain of discourse is not empty.
  -/
  (nonempty : Nonempty D)

  /--
    The assignment to each predicate symbol of a function mapping lists of elements of the domain of discourse to {T, F}.
  -/
  (pred_const_ : PredName_ → (List D → Prop))

  /--
    The assignment to each predicate symbol of a function mapping lists of elements of the domain of discourse to {T, F}.
  -/
  (pred_var_ : PredName_ → (List D → Prop))

instance (D : Type) [Inhabited D] : Inhabited (Interpretation_ D) :=
  Inhabited.mk {
    nonempty := by infer_instance
    pred_const_ := fun _ _ => False
    pred_var_ := fun _ _ => False
  }


/--
  The assignment of an element of the domain of discourse to each variable.
-/
def Valuation_ (D : Type) : Type := VarName_ → D

instance (D : Type) [Inhabited D] : Inhabited (Valuation_ D) :=
  by
  simp only [Valuation_]
  infer_instance


/--
  The evaluation of formulas to truth values.
-/
def holds
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D) : Env_ → Formula_ → Prop
  | _, pred_const_ X xs => I.pred_const_ X (xs.map V)
  | _, pred_var_ X xs => I.pred_var_ X (xs.map V)
  | _, eq_ x y => V x = V y
  | _, true_ => True
  | _, false_ => False
  | E, not_ phi => ¬ holds D I V E phi
  | E, imp_ phi psi =>
    have : sizeOf psi < sizeOf (imp_ phi psi) := by simp
    holds D I V E phi → holds D I V E psi
  | E, and_ phi psi =>
    have : sizeOf psi < sizeOf (and_ phi psi) := by simp
    holds D I V E phi ∧ holds D I V E psi
  | E, or_ phi psi =>
    have : sizeOf psi < sizeOf (or_ phi psi) := by simp
    holds D I V E phi ∨ holds D I V E psi
  | E, iff_ phi psi =>
    have : sizeOf psi < sizeOf (iff_ phi psi) := by simp
    holds D I V E phi ↔ holds D I V E psi
  | E, forall_ x phi =>
    have : sizeOf phi < sizeOf (forall_ x phi) := by simp
    ∀ (d : D), holds D I (Function.updateITE V x d) E phi
  | E, exists_ (x : VarName_) (phi : Formula_) =>
    have : sizeOf phi < sizeOf (exists_ x phi) := by simp
    ∃ (d : D), holds D I (Function.updateITE V x d) E phi
  | ([] : Env_), def_ _ _ => False
  | d :: E, def_ name args =>
    if name = d.name ∧ args.length = d.args.length
    then holds D I (Function.updateListITE V d.args (List.map V args)) E d.q
    else holds D I V E (def_ name args)
  termination_by E phi => (E.length, phi)


/--
  The definition of valid formulas.

  `Formula_.is_valid F` := True if and only if `F` evaluates to `True` in every combination of domain of discourse, interpretation, valuation and environment.
-/
def Formula_.is_valid (F : Formula_) : Prop :=
  ∀ (D : Type) (I : Interpretation_ D) (V : Valuation_ D) (E : Env_), holds D I V E F


theorem holds_coincide_var
  (D : Type)
  (I : Interpretation_ D)
  (V V' : Valuation_ D)
  (E : Env_)
  (F : Formula_)
  (h1 : ∀ (v : VarName_), var_is_free_in v F → V v = V' v) :
  holds D I V E F ↔ holds D I V' E F :=
  by
  induction E generalizing F V V'
  all_goals
    induction F generalizing V V'
    all_goals
      simp only [var_is_free_in] at h1

      simp only [holds]
    case pred_const_ X xs | pred_var_ X xs =>
      congr! 1
      simp only [List.map_eq_map_iff]
      exact h1
    case eq_ x y =>
      simp at h1

      obtain ⟨h1_left, h1_right⟩ := h1
      congr! 1
    case not_ phi phi_ih =>
      congr! 1
      apply phi_ih
      exact h1
    case
        imp_ phi psi phi_ih psi_ih
      | and_ phi psi phi_ih psi_ih
      | or_ phi psi phi_ih psi_ih
      | iff_ phi psi phi_ih psi_ih =>
      congr! 1
      · apply phi_ih
        intro v a1
        apply h1
        left
        exact a1
      · apply psi_ih
        intro v a1
        apply h1
        right
        exact a1
    case forall_ x phi phi_ih | exists_ x phi phi_ih =>
      simp at h1

      first
        | apply forall_congr'
        | apply exists_congr
      intro d
      apply phi_ih
      intro v a1
      simp only [Function.updateITE]
      split_ifs <;> tauto

  case cons.def_ hd tl ih X xs =>
    split_ifs
    case pos c1 =>
      apply ih
      intro v a1
      simp only [var_is_free_in_iff_mem_free_var_set v hd.q] at a1

      apply Function.updateListITE_fun_coincide_mem_eq_len
      · exact h1
      · simp only [← List.mem_toFinset]
        exact Finset.mem_of_subset hd.h1 a1
      · tauto
    case neg c1 =>
      apply ih
      tauto


theorem holds_coincide_pred_var
  (D : Type)
  (I I' : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (F : Formula_)
  (h1 : I.pred_const_ = I'.pred_const_)
  (h2 : ∀ (P : PredName_) (ds : List D),
    pred_var_occurs_in P ds.length F →
      (I.pred_var_ P ds ↔ I'.pred_var_ P ds)) :
  holds D I V E F ↔ holds D I' V E F :=
  by
  induction E generalizing F V
  all_goals
    induction F generalizing V
    all_goals
      simp only [pred_var_occurs_in] at h2

      simp only [holds]
    case pred_const_ X xs =>
      rw [h1]
    case pred_var_ X xs =>
      simp at h2
      apply h2
      · rfl
      · apply List.length_map
    case not_ phi phi_ih =>
      congr! 1
      apply phi_ih
      exact h2
    case
        imp_ phi psi phi_ih psi_ih
      | and_ phi psi phi_ih psi_ih
      | or_ phi psi phi_ih psi_ih
      | iff_ phi psi phi_ih psi_ih =>
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
      first
        | apply forall_congr'
        | apply exists_congr
      intro d
      apply phi_ih
      exact h2

  case cons.def_ hd tl ih X xs =>
    split_ifs
    case pos c1 =>
      apply ih
      intro P ds a1
      simp only [pred_var_occurs_in_iff_mem_pred_var_set] at a1
      simp only [hd.h2] at a1
      simp at a1
    case neg c1 =>
      apply ih
      intro P ds a1
      simp only [pred_var_occurs_in] at a1


lemma holds_coincide_env
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E E' : Env_)
  (F : Formula_)
  (h1 : ∃ (E1 : Env_), E' = E1 ++ E)
  (h2 : all_def_in_env E F)
  (h3 : E'.nodup_) :
  holds D I V E' F ↔ holds D I V E F :=
  by
  induction F generalizing V
  any_goals
    simp only [all_def_in_env] at h2

    simp only [holds]
  case not_ phi phi_ih =>
    congr! 1
    apply phi_ih
    exact h2
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    obtain ⟨h2_left, h2_right⟩ := h2
    congr! 1
    · apply phi_ih
      exact h2_left
    · apply psi_ih
      exact h2_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    first
      | apply forall_congr'
      | apply exists_congr
    intro d
    apply phi_ih
    exact h2
  case def_ X xs =>
    simp only [Env_] at *

    obtain ⟨E1, h1⟩ := h1
    subst h1

    simp only [all_def_in_env] at h2
    obtain ⟨d, h2_left, ⟨h2_right_left, h2_right_right⟩⟩ := h2

    induction E1
    case nil =>
      simp
    case cons E1_hd E1_tl E1_ih =>
      simp only [Env_.nodup_] at h3
      simp only [List.cons_append, List.pairwise_cons, List.mem_append] at h3
      obtain ⟨h3_left, h3_right⟩ := h3

      simp
      simp only [holds]
      split_ifs
      case _ c1 =>
        obtain ⟨c1_left, c1_right⟩ := c1
        exfalso
        apply h3_left d
        · right
          exact h2_left
        · rw [← c1_left]
          exact h2_right_left
        · trans xs.length
          · rw [c1_right]
          · exact h2_right_right
      case _ c1 =>
        apply E1_ih
        exact h3_right


#lint
