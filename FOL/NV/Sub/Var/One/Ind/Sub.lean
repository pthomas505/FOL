import FOL.NV.Sub.Var.One.Rec.Admits


set_option autoImplicit false


namespace FOL.NV.Sub.Var.One.Ind

open Formula_


/--
  `is_sub_var_one_ind F v t F'` := True if and only if `F'` is the result of replacing in `F` each free occurrence of `v` by a free occurrence of `t`.
-/
inductive is_sub_var_one_ind : Formula_ → VarName_ → VarName_ → Formula_ → Prop

  | pred_const_
    (X : PredName_)
    (xs : List VarName_)
    (v t : VarName_) :
    is_sub_var_one_ind (pred_const_ X xs) v t (pred_const_ X (xs.map fun (x : VarName_) =>
      if v = x then t else x))

  | pred_var_
    (X : PredName_)
    (xs : List VarName_)
    (v t : VarName_) :
    is_sub_var_one_ind (pred_var_ X xs) v t (pred_var_ X (xs.map fun (x : VarName_) =>
      if v = x then t else x))

  | eq_
    (x y : VarName_)
    (v t : VarName_) :
    is_sub_var_one_ind (eq_ x y) v t (eq_ (if v = x then t else x) (if v = y then t else y))

  | true_
    (v t : VarName_) :
    is_sub_var_one_ind true_ v t true_

  | false_
    (v t : VarName_) :
    is_sub_var_one_ind false_ v t false_

  | not_
    (phi : Formula_)
    (v t : VarName_)
    (phi' : Formula_) :
    is_sub_var_one_ind phi v t phi' →
    is_sub_var_one_ind phi.not_ v t phi'.not_

  | imp_
    (phi psi : Formula_)
    (v t : VarName_)
    (phi' psi' : Formula_) :
    is_sub_var_one_ind phi v t phi' →
    is_sub_var_one_ind psi v t psi' →
    is_sub_var_one_ind (phi.imp_ psi) v t (phi'.imp_ psi')

  | and_
    (phi psi : Formula_)
    (v t : VarName_)
    (phi' psi' : Formula_) :
    is_sub_var_one_ind phi v t phi' →
    is_sub_var_one_ind psi v t psi' →
    is_sub_var_one_ind (phi.and_ psi) v t (phi'.and_ psi')

  | or_
    (phi psi : Formula_)
    (v t : VarName_)
    (phi' psi' : Formula_) :
    is_sub_var_one_ind phi v t phi' →
    is_sub_var_one_ind psi v t psi' →
    is_sub_var_one_ind (phi.or_ psi) v t (phi'.or_ psi')

  | iff_
    (phi psi : Formula_)
    (v t : VarName_)
    (phi' psi' : Formula_) :
    is_sub_var_one_ind phi v t phi' →
    is_sub_var_one_ind psi v t psi' →
    is_sub_var_one_ind (phi.iff_ psi) v t (phi'.iff_ psi')

  | forall_not_free_in
    (x : VarName_)
    (phi : Formula_)
    (v t : VarName_) :
    ¬ var_is_free_in v (forall_ x phi) →
    is_sub_var_one_ind (forall_ x phi) v t (forall_ x phi)

  | forall_free_in
    (x : VarName_)
    (phi : Formula_)
    (v t : VarName_)
    (phi' : Formula_) :
    var_is_free_in v (forall_ x phi) →
    ¬ x = t →
    is_sub_var_one_ind phi v t phi' →
    is_sub_var_one_ind (forall_ x phi) v t (forall_ x phi')

  | exists_not_free_in
    (x : VarName_)
    (phi : Formula_)
    (v t : VarName_) :
    ¬ var_is_free_in v (exists_ x phi) →
    is_sub_var_one_ind (exists_ x phi) v t (exists_ x phi)

  | exists_free_in
    (x : VarName_)
    (phi : Formula_)
    (v t : VarName_)
    (phi' : Formula_) :
    var_is_free_in v (exists_ x phi) →
    ¬ x = t →
    is_sub_var_one_ind phi v t phi' →
    is_sub_var_one_ind (exists_ x phi) v t (exists_ x phi')

  | def_
    (X : DefName_)
    (xs : List VarName_)
    (v t : VarName_) :
    is_sub_var_one_ind (def_ X xs) v t (def_ X (xs.map fun (x : VarName_) =>
      if v = x then t else x))


theorem fast_admits_var_one_rec_aux_and_fast_replace_free_var_one_rec_imp_is_sub_var_one_ind
  (F F' : Formula_)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : Rec.fast_admits_var_one_rec_aux v u binders F)
  (h2 : Rec.fast_replace_free_var_one_rec v u F = F') :
  is_sub_var_one_ind F v u F' :=
  by
  subst h2
  induction F generalizing binders
  all_goals
    simp only [Rec.fast_admits_var_one_rec_aux] at h1

    simp only [Rec.fast_replace_free_var_one_rec]
  case pred_const_ X xs | pred_var_ X xs =>
    first
      | apply is_sub_var_one_ind.pred_const_
      | apply is_sub_var_one_ind.pred_var_
  case eq_ x y =>
    apply is_sub_var_one_ind.eq_
  case true_ | false_ =>
    first
      | apply is_sub_var_one_ind.true_
      | apply is_sub_var_one_ind.false_
  case not_ phi phi_ih =>
    apply is_sub_var_one_ind.not_
    exact phi_ih binders h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    obtain ⟨h1_left, h1_right⟩ := h1
    first
      | apply is_sub_var_one_ind.imp_
      | apply is_sub_var_one_ind.and_
      | apply is_sub_var_one_ind.or_
      | apply is_sub_var_one_ind.iff_
    · exact phi_ih binders h1_left
    · exact psi_ih binders h1_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    cases h1
    case inl h1 =>
      split_ifs
      all_goals
        first
          | apply is_sub_var_one_ind.forall_not_free_in
          | apply is_sub_var_one_ind.exists_not_free_in
        subst h1
        simp only [var_is_free_in]
        simp
    case inr h1 =>
      split_ifs
      case pos c1 =>
        first
          | apply is_sub_var_one_ind.forall_not_free_in
          | apply is_sub_var_one_ind.exists_not_free_in
        simp only [var_is_free_in]
        tauto
      case neg c1 =>
        by_cases c2 : var_is_free_in v phi
        · first
            | apply is_sub_var_one_ind.forall_free_in
            | apply is_sub_var_one_ind.exists_free_in
          simp only [var_is_free_in]
          constructor
          · exact c1
          . exact c2
          . have s1 : ¬ u ∈ binders ∪ {x} := Rec.fast_admits_var_one_rec_aux_var_is_free_in phi v u (binders ∪ {x}) h1 c2

            simp at s1
            tauto
          · exact phi_ih (binders ∪ {x}) h1
        · have s1 : Rec.fast_replace_free_var_one_rec v u phi = phi :=
          by
            apply Rec.not_var_is_free_in_fast_replace_free_var_one_rec_self
            exact c2

          simp only [s1]
          first
            | apply is_sub_var_one_ind.forall_not_free_in
            | apply is_sub_var_one_ind.exists_not_free_in
          simp only [var_is_free_in]
          tauto
  case def_ X xs =>
    apply is_sub_var_one_ind.def_


theorem is_sub_var_one_ind_imp_fast_admits_var_one_rec_aux
  (F : Formula_)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : ∃ (F' : Formula_), is_sub_var_one_ind F v u F')
  (h2 : u ∉ binders) :
  Rec.fast_admits_var_one_rec_aux v u binders F :=
  by
  apply Exists.elim h1
  intro F' h1_1
  clear h1
  induction h1_1 generalizing binders
  all_goals
    simp only [Rec.fast_admits_var_one_rec_aux]
  case
      forall_not_free_in h1_1_x h1_1_phi h1_1_v h1_1_t h1_1_1
    | exists_not_free_in h1_1_x h1_1_phi h1_1_v h1_1_t h1_1_1 =>
    simp only [var_is_free_in] at h1_1_1
    simp at h1_1_1

    by_cases c1 : h1_1_v = h1_1_x
    · left
      exact c1
    · right
      apply Rec.not_var_is_free_in_imp_fast_admits_var_one_rec_aux
      exact h1_1_1 c1
  case
      forall_free_in h1_1_x h1_1_phi h1_1_v h1_1_t _ _ h1_1_2 _ h1_1_ih
    | exists_free_in h1_1_x h1_1_phi h1_1_v h1_1_t _ _ h1_1_2 _ h1_1_ih =>
    right
    apply h1_1_ih
    simp
    tauto
  all_goals
    tauto


theorem is_sub_var_one_ind_imp_fast_replace_free_var_one_rec
  (F F' : Formula_)
  (v u : VarName_)
  (h1 : is_sub_var_one_ind F v u F') :
  Rec.fast_replace_free_var_one_rec v u F = F' :=
  by
  induction h1
  all_goals
    simp only [Rec.fast_replace_free_var_one_rec]
  case not_ h1_phi h1_v h1_t h1_phi' h1_1 h1_ih =>
    tauto
  case
    imp_ h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' h1_1 h1_2 h1_ih_1 h1_ih_2
  | and_ h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' h1_1 h1_2 h1_ih_1 h1_ih_2
  | or_ h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' h1_1 h1_2 h1_ih_1 h1_ih_2
  | iff_ h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' h1_1 h1_2 h1_ih_1 h1_ih_2 =>
    subst h1_ih_1
    subst h1_ih_2
    rfl
  case
    forall_not_free_in h1_x h1_phi h1_v h1_t h1_1
  | exists_not_free_in h1_x h1_phi h1_v h1_t h1_1 =>
    simp only [var_is_free_in] at h1_1
    simp at h1_1

    split_ifs
    case pos c1 =>
      rfl
    case neg c1 =>
      congr!
      apply Rec.not_var_is_free_in_fast_replace_free_var_one_rec_self
      exact h1_1 c1
  case
    forall_free_in h1_x h1_phi h1_v h1_t h1_phi' h1_1 _ _ h1_ih
  | exists_free_in h1_x h1_phi h1_v h1_t h1_phi' h1_1 _ _ h1_ih =>
    simp only [var_is_free_in] at h1_1

    cases h1_1
    case intro h1_1_left h1_1_right =>
      simp only [if_neg h1_1_left]
      subst h1_ih
      rfl


example
  (F F' : Formula_)
  (v u : VarName_) :
  is_sub_var_one_ind F v u F' ↔
    Rec.fast_admits_var_one_rec v u F ∧ Rec.fast_replace_free_var_one_rec v u F = F' :=
  by
  simp only [Rec.fast_admits_var_one_rec]
  constructor
  · intro a1
    constructor
    · apply is_sub_var_one_ind_imp_fast_admits_var_one_rec_aux
      · exact ⟨F', a1⟩
      · simp
    · apply is_sub_var_one_ind_imp_fast_replace_free_var_one_rec
      exact a1
  · intro a1
    obtain ⟨a1_left, a1_right⟩ := a1
    exact fast_admits_var_one_rec_aux_and_fast_replace_free_var_one_rec_imp_is_sub_var_one_ind F F' v u ∅ a1_left a1_right


theorem substitution_theorem_is_sub_var_one_ind
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (v t : VarName_)
  (F F' : Formula_)
  (h1 : is_sub_var_one_ind F v t F') :
  holds D I (Function.updateITE V v (V t)) E F ↔
    holds D I V E F' :=
  by
  induction h1 generalizing V
  case pred_const_ h1_X h1_xs h1_v h1_t | pred_var_ h1_X h1_xs h1_v h1_t =>
    simp only [holds]
    congr! 1
    simp
    intro x _
    simp only [Function.updateITE]
    simp only [eq_comm]
    split_ifs
    case _ c1 =>
      simp
    case _ c1 =>
      simp
  case eq_ h1_x h1_y h1_v h1_t =>
    simp only [holds]
    simp only [Function.updateITE]
    simp only [eq_comm]
    congr! 1 <;> { split_ifs <;> rfl }
  case true_ _ _ | false_ _ _ =>
    simp only [holds]
  case not_ h1_phi h1_v h1_t h1_phi' _ h1_ih =>
    simp only [holds]
    congr! 1
    apply h1_ih
  case
    imp_ h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' _ _ h1_ih_1 h1_ih_2
  | and_ h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' _ _ h1_ih_1 h1_ih_2
  | or_ h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' _ _ h1_ih_1 h1_ih_2
  | iff_ h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' _ _ h1_ih_1 h1_ih_2 =>
    simp only [holds]
    congr! 1
    · apply h1_ih_1
    · apply h1_ih_2
  case
    forall_not_free_in h1_x h1_phi h1_v h1_t h1_1
  | exists_not_free_in h1_x h1_phi h1_v h1_t h1_1 =>
    simp only [var_is_free_in] at h1_1
    simp at h1_1

    simp only [holds]
    first
      | apply forall_congr'
      | apply exists_congr
    intro d
    apply holds_coincide_var
    intro x a1
    simp only [Function.updateITE]
    split_ifs
    case _ c1 =>
      rfl
    case _ c1 c2 =>
      subst c2
      tauto
    case _ c1 c2 =>
      rfl
  case
    forall_free_in h1_x h1_phi h1_v h1_t h1_phi' h1_1 h1_2 _ h1_ih
  | exists_free_in h1_x h1_phi h1_v h1_t h1_phi' h1_1 h1_2 _ h1_ih =>
    simp only [var_is_free_in] at h1_1

    simp only [holds]
    first
      | apply forall_congr'
      | apply exists_congr
    intro d
    specialize h1_ih (Function.updateITE V h1_x d)
    simp only [← h1_ih]
    apply holds_coincide_var
    intro x _
    simp only [Function.updateITE]
    simp only [eq_comm]
    split_ifs
    case _ c1 c2 c3 =>
      subst c2
      obtain ⟨h1_1_left, h1_1_right⟩ := h1_1
      contradiction
    case _ | _ | _ =>
      rfl
  case def_ h1_X h1_xs h1_v h1_t =>
    induction E
    case nil =>
      simp only [holds]
    case cons hd tl ih =>
      simp only [holds]
      split_ifs
      case _ c1 c2 =>
        simp
        apply holds_coincide_var
        intro v' a1
        have s1 : List.map (Function.updateITE V h1_v (V h1_t)) h1_xs = List.map (V ∘ fun (x : VarName_) => if h1_v = x then h1_t else x) h1_xs :=
        by
          simp only [List.map_eq_map_iff]
          intro x _
          simp only [Function.updateITE]
          simp only [eq_comm]
          simp
          split_ifs
          case _ c3 =>
            simp only [if_pos c3]
          case _ c3 =>
            simp only [if_neg c3]

        simp only [s1]
        apply Function.updateListITE_mem_eq_len
        · simp only [var_is_free_in_iff_mem_free_var_set] at a1
          simp only [← List.mem_toFinset]
          apply Finset.mem_of_subset hd.h1 a1
        · simp
          tauto
      case _ c1 c2 =>
        simp only [List.length_map] at c2
        contradiction
      case _ c1 c2 =>
        simp at c2
        contradiction
      case _ c1 c2 =>
        exact ih


theorem substitution_is_valid_is_sub_var_one_ind
  (v t : VarName_)
  (F F' : Formula_)
  (h1 : is_sub_var_one_ind F v t F')
  (h2 : F.is_valid) :
  F'.is_valid :=
  by
  simp only [is_valid] at h2

  simp only [is_valid]
  intro D I V E
  simp only [← substitution_theorem_is_sub_var_one_ind D I V E v t F F' h1]
  apply h2


#lint
