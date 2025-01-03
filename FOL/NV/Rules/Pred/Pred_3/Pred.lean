import MathlibExtra.Fin
import FOL.NV.Rules.Pred.Pred_1.Pred
import FOL.NV.Sub.Var.One.Rec.Admits
import FOL.NV.Sub.Var.All.Rec.Sub
import FOL.NV.Sub.Pred.All.Rec.Option.Sub


set_option autoImplicit false


open Formula_


/--
  `is_axiom_v3 F` := True if and only if `F` is an axiom of classical first order logic.
-/
inductive is_axiom_v3 : Formula_ → Prop
  -- `⊢ ⊤`
  | prop_true_ :
    is_axiom_v3 true_

  -- `⊢ phi → (psi → phi)`
  | prop_1_
    (phi psi : Formula_) :
    is_axiom_v3 (phi.imp_ (psi.imp_ phi))

  -- `⊢ (phi → (psi → chi)) → ((phi → psi) → (phi → chi))`
  | prop_2_
    (phi psi chi : Formula_) :
    is_axiom_v3 ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi)))

  -- `⊢ (¬ phi → ¬ psi) → (psi → phi)`
  | prop_3_
    (phi psi : Formula_) :
    is_axiom_v3 (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi))

  -- `⊢ (∀ v (phi → psi)) → ((∀ v phi) → (∀ v psi))`
  | pred_1_
    (v : VarName_)
    (phi psi : Formula_) :
    is_axiom_v3 ((forall_ v (phi.imp_ psi)).imp_ ((forall_ v phi).imp_ (forall_ v psi)))

  -- `⊢ (∀ v phi) → phi(t/v)` provided `phi` admits `t` for `v`
  | pred_2_
    (v t : VarName_)
    (phi phi' : Formula_) :
    FOL.NV.Sub.Var.One.Rec.fast_admits_var_one_rec v t phi →
    FOL.NV.Sub.Var.One.Rec.fast_replace_free_var_one_rec v t phi = phi' →
    is_axiom_v3 ((forall_ v phi).imp_ phi')

  -- `⊢ phi → (∀ v phi)` provided `v` is not free in `phi`
  | pred_3_
    (v : VarName_)
    (phi : Formula_) :
    ¬ var_is_free_in v phi →
    is_axiom_v3 (phi.imp_ (forall_ v phi))

  -- `⊢ ∀ v (v = v)`
  | eq_1_ (v : VarName_) :
    is_axiom_v3 (forall_ v (eq_ v v))

  /-
    `⊢ ∀ x_0 ... ∀ x_n ∀ y_0 ... y_n ((x_0 = y_0) ∧ ... ∧ (x_n = y_n) ∧ ⊤) →((pred_ name [x_0 ... x_n] ↔ pred_ name [y_0 ... y_n]))`
  -/
  | eq_2_pred_const_
    (name : PredName_)
    (xs ys : List VarName_) :
    xs.length = ys.length →
    is_axiom_v3
      (Forall_ xs
        (Forall_ ys
          ((And_ (List.zipWith eq_ xs ys)).imp_
            ((pred_const_ name xs).iff_ (pred_const_ name ys)))))

  /-
    `⊢ ∀ x_0 ∀ x_1 ∀ y_0 ∀ y_1 ((x_0 = y_0) ∧ (x_1 = y_1)) → ((eq_ x_0 x_1) ↔ (eq_ y_0 y_1))`
  -/
  | eq_2_eq_
    (x_0 x_1 y_0 y_1 : VarName_) :
    is_axiom_v3
      (forall_ x_0
        (forall_ x_1
          (forall_ y_0
            (forall_ y_1
              ((and_ (eq_ x_0 y_0) (eq_ x_1 y_1)).imp_
                ((eq_ x_0 x_1).iff_ (eq_ y_0 y_1)))))))

  -- `⊢ phi ⇒ ⊢ ∀ v phi`
  | gen_
    (v : VarName_)
    (phi : Formula_) :
    is_axiom_v3 phi →
    is_axiom_v3 (forall_ v phi)

  | def_false_ :
    is_axiom_v3 (false_.iff_ (not_ true_))

  | def_and_
    (phi psi : Formula_) :
    is_axiom_v3 ((phi.and_ psi).iff_ (not_ (phi.imp_ (not_ psi))))

  | def_or_
    (phi psi : Formula_) :
    is_axiom_v3 ((phi.or_ psi).iff_ ((not_ phi).imp_ psi))

  | def_iff_
    (phi psi : Formula_) :
    is_axiom_v3 (not_ (((phi.iff_ psi).imp_ (not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi))))).imp_ (not_ ((not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi)))).imp_ (phi.iff_ psi)))))

  | def_exists_
    (v : VarName_)
    (phi : Formula_) :
    is_axiom_v3 ((exists_ v phi).iff_ (not_ (forall_ v (not_ phi))))


/--
  `is_deduct_v3 Δ F` := True if and only if there is a deduction of `F` from `Δ` in classical first order logic.
-/
inductive is_deduct_v3 (Δ : Set Formula_) : Formula_ → Prop

  | axiom_
    (phi : Formula_) :
    is_axiom_v3 phi →
    is_deduct_v3 Δ phi

  | assume_
    (phi : Formula_) :
    phi ∈ Δ →
    is_deduct_v3 Δ phi

  | mp_
    (phi psi : Formula_) :
    is_deduct_v3 Δ (phi.imp_ psi) →
    is_deduct_v3 Δ phi →
    is_deduct_v3 Δ psi


/--
  `is_proof_v3 F` := True if and only if there is a proof of `F` in classical first order logic.
-/
def is_proof_v3 (F : Formula_) : Prop :=
  is_deduct_v3 ∅ F


lemma is_axiom_v1_imp_is_axiom_v3
  (F : Formula_)
  (h1 : is_axiom_v1 F) :
  is_axiom_v3 F :=
  by
  induction h1
  case prop_true_ =>
    exact is_axiom_v3.prop_true_
  case prop_1_ phi psi =>
    apply is_axiom_v3.prop_1_
  case prop_2_ phi psi chi =>
    apply is_axiom_v3.prop_2_
  case prop_3_ phi psi =>
    apply is_axiom_v3.prop_3_
  case pred_1_ v phi psi =>
    apply is_axiom_v3.pred_1_
  case pred_2_ v t phi phi' ih_1 ih_2 =>
    exact is_axiom_v3.pred_2_ v t phi phi' ih_1 ih_2
  case pred_3_ v phi ih =>
    apply is_axiom_v3.pred_3_
    exact ih
  case eq_1_ v =>
    apply is_axiom_v3.eq_1_
  case eq_2_pred_const_ name n xs ys =>
    obtain s1 := list_of_fn_fin_zip_with_eq_list_zip_with_list_of_fn eq_ n xs ys
    unfold Fin.zipWith at s1
    rw [s1]

    apply is_axiom_v3.eq_2_pred_const_
    simp
  case eq_2_eq_ x_0 x_1 y_0 y_1 =>
    apply is_axiom_v3.eq_2_eq_
  case gen_ v phi ih_1 ih_2 =>
    apply is_axiom_v3.gen_
    exact ih_2
  case def_false_ =>
    apply is_axiom_v3.def_false_
  case def_and_ phi psi =>
    apply is_axiom_v3.def_and_
  case def_or_ phi psi =>
    apply is_axiom_v3.def_or_
  case def_iff_ phi psi =>
    apply is_axiom_v3.def_iff_
  case def_exists_ v phi =>
    apply is_axiom_v3.def_exists_


lemma is_deduct_v1_imp_is_deduct_v3
  (Δ : Set Formula_)
  (F : Formula_)
  (h1 : is_deduct_v1 Δ F) :
  is_deduct_v3 Δ F :=
  by
  induction h1
  case axiom_ h1_phi h1_ih =>
    apply is_deduct_v3.axiom_
    apply is_axiom_v1_imp_is_axiom_v3
    exact h1_ih
  case assume_ h1_phi h1_ih =>
    apply is_deduct_v3.assume_
    exact h1_ih
  case mp_ h1_phi h1_psi h1_ih_1 h1_ih_2 h1_ih_3 h1_ih_4 =>
    apply is_deduct_v3.mp_ h1_phi
    · exact h1_ih_3
    · exact h1_ih_4


lemma is_axiom_v3_imp_is_axiom_v1
  (F : Formula_)
  (h1 : is_axiom_v3 F) :
  is_axiom_v1 F :=
  by
  induction h1
  case prop_true_ =>
    exact is_axiom_v1.prop_true_
  case prop_1_ phi psi =>
    apply is_axiom_v1.prop_1_
  case prop_2_ phi psi chi =>
    apply is_axiom_v1.prop_2_
  case prop_3_ phi psi =>
    apply is_axiom_v1.prop_3_
  case pred_1_ v phi psi =>
    apply is_axiom_v1.pred_1_
  case pred_2_ v t phi phi' ih_1 ih_2 =>
    exact is_axiom_v1.pred_2_ v t phi phi' ih_1 ih_2
  case pred_3_ v phi ih =>
    apply is_axiom_v1.pred_3_
    exact ih
  case eq_1_ v =>
    apply is_axiom_v1.eq_1_
  case eq_2_pred_const_ name xs ys ih =>
    obtain ⟨n, fn_xs, fn_ys, c1, c2, c3⟩ := exists_list_of_fn_fin_zip_with_eq_len_eq_list_zip_with_and_list_of_fn_eq_list eq_ xs ys ih
    rw [← c1]
    rw [← c2]
    rw [← c3]

    apply is_axiom_v1.eq_2_pred_const_
  case eq_2_eq_ x_0 x_1 y_0 y_1 =>
    apply is_axiom_v1.eq_2_eq_
  case gen_ v phi ih_1 ih_2 =>
    apply is_axiom_v1.gen_
    exact ih_2
  case def_false_ =>
    apply is_axiom_v1.def_false_
  case def_and_ phi psi =>
    apply is_axiom_v1.def_and_
  case def_or_ phi psi =>
    apply is_axiom_v1.def_or_
  case def_iff_ phi psi =>
    apply is_axiom_v1.def_iff_
  case def_exists_ v phi =>
    apply is_axiom_v1.def_exists_


lemma is_deduct_v3_imp_is_deduct_v1
  (Δ : Set Formula_)
  (F : Formula_)
  (h1 : is_deduct_v3 Δ F) :
  is_deduct_v1 Δ F :=
  by
  induction h1
  case axiom_ h1_phi h1_ih =>
    apply is_deduct_v1.axiom_
    apply is_axiom_v3_imp_is_axiom_v1
    exact h1_ih
  case assume_ h1_phi h1_ih =>
    apply is_deduct_v1.assume_
    exact h1_ih
  case mp_ h1_phi h1_psi h1_ih_1 h1_ih_2 h1_ih_3 h1_ih_4 =>
    apply is_deduct_v1.mp_ h1_phi
    · exact h1_ih_3
    · exact h1_ih_4


lemma is_deduct_v3_weaken
  (F : Formula_)
  (Δ : Set Formula_)
  (Γ : Set Formula_)
  (h1 : is_deduct_v3 Δ F) :
  is_deduct_v3 (Γ ∪ Δ) F :=
  by
  induction h1
  case axiom_ phi ih =>
    apply is_deduct_v3.axiom_
    exact ih
  case assume_ phi ih =>
    apply is_deduct_v3.assume_
    simp
    right
    exact ih
  case mp_ phi psi ih_1 ih_2 ih_3 ih_4 =>
    apply is_deduct_v3.mp_ phi
    · exact ih_3
    · exact ih_4
