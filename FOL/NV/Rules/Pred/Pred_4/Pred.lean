import MathlibExtra.Fin
--import FOL.NV.Deduct
import FOL.NV.Rules.Prop.Prop_1.Prop
import FOL.NV.Rules.Pred.Pred_3.Pred
--import FOL.NV.Pred
import FOL.NV.Sub.Var.One.Rec.Admits
import FOL.NV.Sub.Var.All.Rec.Sub
import FOL.NV.Sub.Pred.All.Rec.Option.Sub


set_option autoImplicit false


open Formula_


def freshChar : Char := '+'


inductive is_deduct_v4 : List Formula_ → Formula_ → Prop
  | struct_1_
    (Δ : List Formula_)
    (H phi : Formula_) :
    is_deduct_v4 Δ phi →
    is_deduct_v4 (H :: Δ) phi

  | struct_2_
    (Δ : List Formula_)
    (H phi : Formula_) :
    is_deduct_v4 (H :: H :: Δ) phi →
    is_deduct_v4 (H :: Δ) phi

  | struct_3_
    (Δ_1 Δ_2 : List Formula_)
    (H_1 H_2 phi : Formula_) :
    is_deduct_v4 (Δ_1 ++ [H_1] ++ [H_2] ++ Δ_2) phi →
    is_deduct_v4 (Δ_1 ++ [H_2] ++ [H_1] ++ Δ_2) phi

  /-
    phi ⊢ phi
  -/
  | assume_
    (phi : Formula_) :
    is_deduct_v4 [phi] phi

  /-
    ⊢ ⊤
  -/
  | prop_0_ :
    is_deduct_v4 [] true_

  /-
    ⊢ phi → (psi → phi)
  -/
  | prop_1_
    (phi psi : Formula_) :
    is_deduct_v4 [] (phi.imp_ (psi.imp_ phi))

  /-
    ⊢ (phi → (psi → chi)) → ((phi → psi) → (phi → chi))
  -/
  | prop_2_
    (phi psi chi : Formula_) :
    is_deduct_v4 []
      ((phi.imp_ (psi.imp_ chi)).imp_
        ((phi.imp_ psi).imp_ (phi.imp_ chi)))

  /-
    ⊢ (¬ phi → ¬ psi) → (psi → phi)
  -/
  | prop_3_
    (phi psi : Formula_) :
    is_deduct_v4 []
      (((not_ phi).imp_ (not_ psi)).imp_
        (psi.imp_ phi))

  /-
    Δ ⊢ phi → psi ⇒
    Δ ⊢ phi ⇒
    Δ ⊢ psi
  -/
  | mp_
    (Δ : List Formula_)
    (phi psi : Formula_) :
    is_deduct_v4 Δ (phi.imp_ psi) →
    is_deduct_v4 Δ phi →
    is_deduct_v4 Δ psi

  /-
    H :: Δ ⊢ phi ⇒
    Δ ⊢ H → phi
  -/
  | dt_
    (Δ : List Formula_)
    (H : Formula_)
    (phi : Formula_) :
    is_deduct_v4 (H :: Δ) phi →
    is_deduct_v4 Δ (H.imp_ phi)

  /-
    ⊢ (∀ v (phi → psi)) → ((∀ v phi) → (∀ v psi))
  -/
  | pred_1_
    (v : VarName_)
    (phi psi : Formula_) :
    is_deduct_v4 [] ((forall_ v (phi.imp_ psi)).imp_ ((forall_ v phi).imp_ (forall_ v psi)))

  /-
    ⊢ (∀ v phi) → phi(t/v)  provided phi admits t for v
  -/
  | pred_2_
    (v t : VarName_)
    (phi : Formula_) :
    is_deduct_v4 [] ((forall_ v phi).imp_ (FOL.NV.Sub.Var.All.Rec.Fresh.sub_var_all_rec (Function.updateITE id v t) freshChar phi))

  /-
    ⊢ phi → (∀ v phi)  provided v is not free in phi
  -/
  | pred_3_
    (v : VarName_)
    (phi : Formula_) :
    ¬ var_is_free_in v phi →
    is_deduct_v4 [] (phi.imp_ (forall_ v phi))

  /-
    ⊢ phi ⇒ ⊢ ∀ v phi
  -/
  | gen_
    (v : VarName_)
    (phi : Formula_) :
    is_deduct_v4 [] phi →
    is_deduct_v4 [] (forall_ v phi)

  /-
    ⊢ v = v
  -/
  | eq_1_
    (v : VarName_) :
    is_deduct_v4 [] (eq_ v v)

  /-
    ⊢ ((x_0 = y_0) ∧ ... ∧ (x_n = y_n) ∧ ⊤) → (pred_var_ name [x_0 ... x_n] ↔ pred_var_ name [y_0 ... y_n])
  -/
  | eq_2_pred_var_
    (name : PredName_)
    (xs ys : List VarName_) :
    xs.length = ys.length →
    is_deduct_v4 [] ((List.foldr and_ true_ (List.zipWith eq_ xs ys)).imp_ ((pred_var_ name xs).iff_ (pred_var_ name ys)))

  /-
    ⊢ ((x_0 = y_0) ∧ (x_1 = y_1)) → ((eq_ x_0 x_1) ↔ (eq_ y_0 y_1))
  -/
  | eq_2_eq_
    (x_0 x_1 y_0 y_1 : VarName_) :
    is_deduct_v4 [] ((and_ (eq_ x_0 y_0) (eq_ x_1 y_1)).imp_ ((eq_ x_0 x_1).iff_ (eq_ y_0 y_1)))

  /-
    ⊢ ⊥ ↔ ¬ ⊤
  -/
  | def_false_ :
    is_deduct_v4 [] (false_.iff_ (not_ true_))

  /-
    ⊢ (phi ∧ psi) ↔ ¬ (phi → ¬ psi)
  -/
  | def_and_
    (phi psi : Formula_) :
    is_deduct_v4 [] ((phi.and_ psi).iff_ (not_ (phi.imp_ (not_ psi))))

  /-
    ⊢ (phi ∨ psi) ↔ ((¬ phi) → psi)
  -/
  | def_or_
    (phi psi : Formula_) :
    is_deduct_v4 [] ((phi.or_ psi).iff_ ((not_ phi).imp_ psi))

  /-
    ⊢ (phi ↔ psi) ↔ ((phi → psi) ∧ (psi → phi))
    ⊢ (phi ↔ psi) ↔ ¬ ((phi → psi) → ¬ (psi → phi))
    ⊢ ((phi ↔ psi) → (¬ ((phi → psi) → ¬ (psi → phi)))) ∧ (¬ ((phi → psi) → ¬ (psi → phi)) → (phi ↔ psi))
    ⊢ ¬ (((phi ↔ psi) → (¬ ((phi → psi) → ¬ (psi → phi)))) → ¬ (¬ ((phi → psi) → ¬ (psi → phi)) → (phi ↔ psi)))
  -/
  | def_iff_
    (phi psi : Formula_) :
    is_deduct_v4 [] (not_ (((phi.iff_ psi).imp_ (not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi))))).imp_ (not_ ((not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi)))).imp_ (phi.iff_ psi)))))

  /-
    ⊢ (∃ v phi) ↔ ¬ (∀ v ¬ phi)
  -/
  | def_exists_
    (v : VarName_)
    (phi : Formula_) :
    is_deduct_v4 [] ((exists_ v phi).iff_ (not_ (forall_ v (not_ phi))))

  | sub_
    (Δ : List Formula_)
    (phi : Formula_)
    (τ : PredName_ → ℕ → Option (List VarName_ × Formula_)) :
    is_deduct_v4 Δ phi →
    is_deduct_v4 (Δ.map (FOL.NV.Sub.Pred.All.Rec.Option.Fresh.sub_pred_all_rec_opt freshChar τ)) (FOL.NV.Sub.Pred.All.Rec.Option.Fresh.sub_pred_all_rec_opt freshChar τ phi)


-------------------------------------------------------------------------------


lemma is_deduct_v4_struct_1_list
  (Δ : List Formula_)
  (F : Formula_)
  (Γ : List Formula_)
  (h1 : is_deduct_v4 Δ F) :
  is_deduct_v4 (Γ ++ Δ) F :=
  by
  induction Γ
  case nil =>
    simp
    exact h1
  case cons hd tl ih =>
    apply is_deduct_v4.struct_1_
    exact ih


lemma is_deduct_v4_struct_3_singleton_list
  (Δ_1 Δ_2 : List Formula_)
  (Γ : List Formula_)
  (H : Formula_)
  (F : Formula_)
  (h1 : is_deduct_v4 (Δ_1 ++ [H] ++ Γ ++ Δ_2) F) :
  is_deduct_v4 (Δ_1 ++ Γ ++ [H] ++ Δ_2) F :=
  by
  induction Γ generalizing Δ_1 Δ_2
  case nil =>
    simp at h1
    simp
    exact h1
  case cons Γ_1_hd Γ_1_tl Γ_1_ih =>
    specialize Γ_1_ih (Δ_1 ++ [Γ_1_hd])
    simp at Γ_1_ih

    simp at h1

    simp
    apply Γ_1_ih
    obtain s1 := is_deduct_v4.struct_3_ Δ_1 (Γ_1_tl ++ Δ_2) H Γ_1_hd
    simp at s1
    apply s1
    exact h1


lemma is_deduct_v4_struct_3_list_list
  (Δ_1 Δ_2 : List Formula_)
  (Γ_1 Γ_2 : List Formula_)
  (F : Formula_)
  (h1 : is_deduct_v4 (Δ_1 ++ Γ_1 ++ Γ_2 ++ Δ_2) F) :
  is_deduct_v4 (Δ_1 ++ Γ_2 ++ Γ_1 ++ Δ_2) F :=
  by
  induction Γ_1 generalizing Γ_2 Δ_1 Δ_2
  case nil =>
    simp at h1
    simp
    exact h1
  case cons hd tl ih =>
    obtain s1 := is_deduct_v4_struct_3_singleton_list Δ_1 (tl ++ Δ_2) Γ_2 hd F
    simp at s1
    simp
    apply s1
    clear s1

    specialize ih (Δ_1 ++ [hd]) Δ_2 Γ_2
    simp at ih
    apply ih

    simp at h1
    exact h1


lemma is_deduct_v4_struct_3_list_list_mid
  (Δ_1 Δ_2 Δ_3 : List Formula_)
  (Γ_1 Γ_2 : List Formula_)
  (F : Formula_)
  (h1 : is_deduct_v4 (Δ_1 ++ Γ_1 ++ Δ_2 ++ Γ_2 ++ Δ_3) F) :
  is_deduct_v4 (Δ_1 ++ Γ_2 ++ Δ_2 ++ Γ_1 ++ Δ_3) F :=
  by
  obtain s1 := is_deduct_v4_struct_3_list_list (Δ_1 ++ Γ_2) Δ_3 Γ_1 Δ_2

  obtain s2 := is_deduct_v4_struct_3_list_list Δ_1 Δ_3 (Γ_1 ++ Δ_2) Γ_2 F

  simp at *
  apply s1
  apply s2
  exact h1


lemma is_deduct_v4_struct_rotate_to_first
  (Δ_1 Δ_2 : List Formula_)
  (F : Formula_)
  (H : Formula_)
  (h1 : is_deduct_v4 (Δ_1 ++ [H] ++ Δ_2) F) :
  is_deduct_v4 (H :: Δ_1 ++ Δ_2) F :=
  by
  obtain s1 := is_deduct_v4_struct_3_list_list [] Δ_2 Δ_1 [H]
  simp at s1
  simp
  apply s1
  simp at h1
  exact h1


lemma is_deduct_v4_struct_rotate_to_last
  (Δ_1 Δ_2 : List Formula_)
  (F : Formula_)
  (H : Formula_)
  (h1 : is_deduct_v4 (Δ_1 ++ [H] ++ Δ_2) F) :
  is_deduct_v4 (Δ_1 ++ Δ_2 ++ [H]) F :=
  by
  obtain s1 := is_deduct_v4_struct_3_list_list Δ_1 [] [H] Δ_2
  simp at s1
  simp
  apply s1
  simp at h1
  exact h1


-------------------------------------------------------------------------------


lemma is_deduct_v4_assume_mem
  (F : Formula_)
  (Δ : List Formula_)
  (h1 : F ∈ Δ) :
  is_deduct_v4 Δ F :=
  by
  induction Δ
  case nil =>
    simp at h1
  case cons hd tl ih =>
    simp at h1
    cases h1
    case inl h1 =>
      rw [h1]
      obtain s1 := is_deduct_v4_struct_rotate_to_first tl [] hd hd
      simp at s1
      apply s1
      apply is_deduct_v4_struct_1_list [hd] hd tl
      apply is_deduct_v4.assume_ hd
    case inr h1 =>
      apply is_deduct_v4.struct_1_
      apply ih
      exact h1


lemma is_prop_axiom_v1_imp_is_deduct_v4
  (F : Formula_)
  (h1 : is_prop_axiom_v1 F) :
  is_deduct_v4 [] F :=
  by
  induction h1
  case prop_true_ =>
    apply is_deduct_v4.prop_0_
  case prop_1_ phi psi =>
    apply is_deduct_v4.prop_1_
  case prop_2_ phi psi chi =>
    apply is_deduct_v4.prop_2_
  case prop_3_ phi psi =>
    apply is_deduct_v4.prop_3_
  case def_false_ =>
    apply is_deduct_v4.def_false_
  case def_and_ phi psi =>
    apply is_deduct_v4.def_and_
  case def_or_ phi psi =>
    apply is_deduct_v4.def_or_
  case def_iff_ phi psi =>
    apply is_deduct_v4.def_iff_


lemma is_prop_deduct_v1_imp_is_deduct_v4
  (Δ : Finset Formula_)
  (F : Formula_)
  (h1 : is_prop_deduct_v1 Δ F) :
  is_deduct_v4 Δ.toList F :=
  by
  induction h1
  case axiom_ phi ih =>
    obtain s1 := is_deduct_v4_struct_1_list [] phi Δ.toList
    simp at s1
    apply s1
    exact is_prop_axiom_v1_imp_is_deduct_v4 phi ih
  case assume_ phi ih =>
    apply is_deduct_v4_assume_mem
    simp
    exact ih
  case mp_ phi psi ih_1 ih_2 ih_3 ih_4 =>
    apply is_deduct_v4.mp_ Δ.toList phi
    · exact ih_3
    · exact ih_4


-------------------------------------------------------------------------------


example
  (F : Formula_)
  (Δ : List Formula_)
  (h1 : is_deduct_v4 Δ F) :
  is_deduct_v3 Δ.toFinset.toSet F :=
  by
  induction h1
  case struct_1_ h1_Δ h1_H h1_phi h1_ih_1 h1_ih_2 =>
    have s1 : (h1_H :: h1_Δ).toFinset.toSet = {h1_H} ∪ h1_Δ.toFinset.toSet :=
    by
      simp
    rw [s1]

    apply is_deduct_v3_weaken h1_phi h1_Δ.toFinset.toSet {h1_H}
    exact h1_ih_2
  case struct_2_ h1_Δ h1_H h1_phi h1_ih_1 h1_ih_2 =>
    simp at h1_ih_2
    simp
    exact h1_ih_2
  case struct_3_ h1_Δ_1 h1_Δ_2 h1_H_1 h1_H_2 h1_phi h1_ih_1 h1_ih_2 =>
    simp at h1_ih_2
    simp
    have s1 : insert h1_H_2 (insert h1_H_1 ({a | a ∈ h1_Δ_1} ∪ {a | a ∈ h1_Δ_2})) = insert h1_H_1 (insert h1_H_2 ({a | a ∈ h1_Δ_1} ∪ {a | a ∈ h1_Δ_2})) :=
    by
      simp only [Set.insert_comm]
    rw [s1]
    exact h1_ih_2
  case assume_ h1_phi =>
    apply is_deduct_v3.assume_
    simp
  case prop_0_ =>
    apply is_deduct_v3.axiom_
    apply is_axiom_v3.prop_true_
  case prop_1_ h1_phi h1_psi =>
    apply is_deduct_v3.axiom_
    apply is_axiom_v3.prop_1_
  case prop_2_ h1_phi h1_psi h1_chi =>
    apply is_deduct_v3.axiom_
    apply is_axiom_v3.prop_2_
  case prop_3_ h1_phi h1_psi =>
    apply is_deduct_v3.axiom_
    apply is_axiom_v3.prop_3_
  case mp_ h1_Δ h1_phi h1_psi h1_ih_1 h1_ih_2 h1_ih_3 h1_ih_4 =>
    apply is_deduct_v3.mp_ h1_phi
    · exact h1_ih_3
    · exact h1_ih_4
  case dt_ h1_Δ h1_H h1_phi h1_ih_1 h1_ih_2 =>
    simp at h1_ih_2
    apply is_deduct_v1_imp_is_deduct_v3
    apply deduction_theorem_pred_v1
    apply is_deduct_v3_imp_is_deduct_v1
    simp
    exact h1_ih_2
  case pred_1_ h1_v h1_phi h1_psi =>
    apply is_deduct_v3.axiom_
    apply is_axiom_v3.pred_1_
  case pred_2_ h1_v h1_t h1_phi =>
    simp
    induction h1_phi
    case
        pred_const_ X xs
      | pred_var_ X xs
      | def_ X xs =>
      simp only [FOL.NV.Sub.Var.All.Rec.Fresh.sub_var_all_rec]
      apply is_deduct_v3.axiom_
      apply is_axiom_v3.pred_2_ h1_v h1_t
      · apply
        FOL.NV.Sub.Var.One.Rec.not_var_is_bound_in_imp_fast_admits_var_one_rec
        unfold var_is_bound_in
        simp
      · simp only [FOL.NV.Sub.Var.One.Rec.fast_replace_free_var_one_rec]
        unfold Function.updateITE
        simp
        intro a a1
        refine if_ctx_congr ?_ (congrFun rfl) (congrFun rfl)
        exact eq_comm
    case eq_ x y =>
      simp only [FOL.NV.Sub.Var.All.Rec.Fresh.sub_var_all_rec]
      apply is_deduct_v3.axiom_
      apply is_axiom_v3.pred_2_ h1_v h1_t
      · apply
        FOL.NV.Sub.Var.One.Rec.not_var_is_bound_in_imp_fast_admits_var_one_rec
        unfold var_is_bound_in
        simp
      · simp only [FOL.NV.Sub.Var.One.Rec.fast_replace_free_var_one_rec]
        unfold Function.updateITE
        simp
        constructor
        · refine if_ctx_congr ?_ (congrFun rfl) (congrFun rfl)
          exact eq_comm
        · refine if_ctx_congr ?_ (congrFun rfl) (congrFun rfl)
          exact eq_comm
    case forall_ x phi ih =>
      sorry
    all_goals
      sorry
  case pred_3_ h1_v h1_phi h1_ih =>
    apply is_deduct_v3.axiom_
    apply is_axiom_v3.pred_3_
    exact h1_ih
  case gen_ h1_v h1_phi h1_ih_1 h1_ih_2 =>
    apply is_deduct_v1_imp_is_deduct_v3
    apply generalization
    · apply is_deduct_v3_imp_is_deduct_v1
      exact h1_ih_2
    · simp
  case eq_1_ h1_v =>
    apply is_deduct_v1_imp_is_deduct_v3
    apply spec_id h1_v
    apply is_deduct_v3_imp_is_deduct_v1
    apply is_deduct_v3.axiom_
    apply is_axiom_v3.eq_1_

  all_goals
    sorry


--#lint
