import FOL.NV.Sub.Var.One.Rec.Admits


set_option autoImplicit false


open Formula_


/--
  `is_prop_axiom F` := True if and only if `F` is an axiom of classical propositional logic.
-/
inductive is_prop_axiom : Formula_ → Prop
  -- `⊢ ⊤`
  | prop_true_ :
    is_prop_axiom true_

  -- `⊢ phi → (psi → phi)`
  | prop_1_
    (phi psi : Formula_) :
    is_prop_axiom (phi.imp_ (psi.imp_ phi))

  -- `⊢ (phi → (psi → chi)) → ((phi → psi) → (phi → chi))`
  | prop_2_
    (phi psi chi : Formula_) :
    is_prop_axiom ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi)))

  -- `⊢ (¬ phi → ¬ psi) → (psi → phi)`
  | prop_3_
    (phi psi : Formula_) :
    is_prop_axiom (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi))

  | def_false_ :
    is_prop_axiom (false_.iff_ (not_ true_))

  | def_and_
    (phi psi : Formula_) :
    is_prop_axiom ((phi.and_ psi).iff_ (not_ (phi.imp_ (not_ psi))))

  | def_or_
    (phi psi : Formula_) :
    is_prop_axiom ((phi.or_ psi).iff_ ((not_ phi).imp_ psi))

  | def_iff_
    (phi psi : Formula_) :
    is_prop_axiom (not_ (((phi.iff_ psi).imp_ (not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi))))).imp_ (not_ ((not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi)))).imp_ (phi.iff_ psi)))))


/--
  `is_prop_deduct Δ F` := True if and only if there is a deduction of `F` from `Δ` in classical propositional logic.
-/
inductive is_prop_deduct (Δ : Set Formula_) : Formula_ → Prop
  | axiom_
    (phi : Formula_) :
    is_prop_axiom phi →
    is_prop_deduct Δ phi

  | assume_
    (phi : Formula_) :
    phi ∈ Δ →
    is_prop_deduct Δ phi

  | mp_
    (phi psi : Formula_) :
    is_prop_deduct Δ (phi.imp_ psi) →
    is_prop_deduct Δ phi →
    is_prop_deduct Δ psi


/--
  `is_prop_proof F` := True if and only if there is a proof of `F` in classical propositional logic.
-/
def is_prop_proof (phi : Formula_) : Prop :=
  is_prop_deduct ∅ phi


/--
  `is_axiom_v1 F` := True if and only if `F` is an axiom of classical first order logic.
-/
inductive is_axiom_v1 : Formula_ → Prop
  -- `⊢ ⊤`
  | prop_true_ :
    is_axiom_v1 true_

  -- `⊢ phi → (psi → phi)`
  | prop_1_
    (phi psi : Formula_) :
    is_axiom_v1 (phi.imp_ (psi.imp_ phi))

  -- `⊢ (phi → (psi → chi)) → ((phi → psi) → (phi → chi))`
  | prop_2_
    (phi psi chi : Formula_) :
    is_axiom_v1 ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi)))

  -- `⊢ (¬ phi → ¬ psi) → (psi → phi)`
  | prop_3_
    (phi psi : Formula_) :
    is_axiom_v1 (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi))

  -- `⊢ (∀ v (phi → psi)) → ((∀ v phi) → (∀ v psi))`
  | pred_1_
    (v : VarName_)
    (phi psi : Formula_) :
    is_axiom_v1 ((forall_ v (phi.imp_ psi)).imp_ ((forall_ v phi).imp_ (forall_ v psi)))

  -- `⊢ (∀ v phi) → phi(t/v)` provided `phi` admits `t` for `v`
  | pred_2_
    (v t : VarName_)
    (phi phi' : Formula_) :
    FOL.NV.Sub.Var.One.Rec.fast_admits_var_one_rec v t phi →
    FOL.NV.Sub.Var.One.Rec.fast_replace_free_var_one_rec v t phi = phi' →
    is_axiom_v1 ((forall_ v phi).imp_ phi')

  -- `⊢ phi → (∀ v phi)` provided `v` is not free in `phi`
  | pred_3_
    (v : VarName_)
    (phi : Formula_) :
    ¬ var_is_free_in v phi →
    is_axiom_v1 (phi.imp_ (forall_ v phi))

  -- `⊢ ∀ v (v = v)`
  | eq_1_ (v : VarName_) :
    is_axiom_v1 (forall_ v (eq_ v v))

  /-
    `⊢ ∀ x_0 ... ∀ x_n ∀ y_0 ... y_n ((x_0 = y_0) ∧ ... ∧ (x_n = y_n) ∧ ⊤) →((pred_ name [x_0 ... x_n] ↔ pred_ name [y_0 ... y_n]))`
  -/
  | eq_2_pred_const_
    (name : PredName_)
    (n : ℕ)
    (xs ys : Fin n → VarName_) :
    is_axiom_v1
      (Forall_ (List.ofFn xs)
        (Forall_ (List.ofFn ys)
          ((And_ (List.ofFn fun i : Fin n => eq_ (xs i) (ys i))).imp_
            ((pred_const_ name (List.ofFn xs)).iff_ (pred_const_ name (List.ofFn ys))))))

  /-
    `⊢ ∀ x_0 ∀ x_1 ∀ y_0 ∀ y_1 ((x_0 = y_0) ∧ (x_1 = y_1)) → ((eq_ x_0 x_1) ↔ (eq_ y_0 y_1))`
  -/
  | eq_2_eq_
    (x_0 x_1 y_0 y_1 : VarName_) :
    is_axiom_v1
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
    is_axiom_v1 phi →
    is_axiom_v1 (forall_ v phi)

  | def_false_ :
    is_axiom_v1 (false_.iff_ (not_ true_))

  | def_and_
    (phi psi : Formula_) :
    is_axiom_v1 ((phi.and_ psi).iff_ (not_ (phi.imp_ (not_ psi))))

  | def_or_
    (phi psi : Formula_) :
    is_axiom_v1 ((phi.or_ psi).iff_ ((not_ phi).imp_ psi))

  | def_iff_
    (phi psi : Formula_) :
    is_axiom_v1 (not_ (((phi.iff_ psi).imp_ (not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi))))).imp_ (not_ ((not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi)))).imp_ (phi.iff_ psi)))))

  | def_exists_
    (v : VarName_)
    (phi : Formula_) :
    is_axiom_v1 ((exists_ v phi).iff_ (not_ (forall_ v (not_ phi))))

/--
  `is_deduct_v1 Δ F` := True if and only if there is a deduction of `F` from `Δ` in classical first order logic.
-/
inductive is_deduct_v1 (Δ : Set Formula_) : Formula_ → Prop

  | axiom_
    (phi : Formula_) :
    is_axiom_v1 phi →
    is_deduct_v1 Δ phi

  | assume_
    (phi : Formula_) :
    phi ∈ Δ →
    is_deduct_v1 Δ phi

  | mp_
    (phi psi : Formula_) :
    is_deduct_v1 Δ (phi.imp_ psi) →
    is_deduct_v1 Δ phi →
    is_deduct_v1 Δ psi


/--
  `is_proof_v1 F` := True if and only if there is a proof of `F` in classical first order logic.
-/
def is_proof_v1 (F : Formula_) : Prop :=
  is_deduct_v1 ∅ F


/--
  `is_proof_v2 F` := True if and only if there is a proof of `F` in classical first order logic.

  This definition is equivalent to `is_proof_v1`.
-/
inductive is_proof_v2 : Formula_ → Prop

  -- `⊢ ⊤`
  | prop_true_ : is_proof_v2 true_

  -- `⊢ phi → (psi → phi)`
  | prop_1_
    (phi psi : Formula_) :
    is_proof_v2 (phi.imp_ (psi.imp_ phi))

  -- `⊢ (phi → (psi → chi)) → ((phi → psi) → (phi → chi))`
  | prop_2_
    (phi psi chi : Formula_) :
    is_proof_v2
      ((phi.imp_ (psi.imp_ chi)).imp_
        ((phi.imp_ psi).imp_ (phi.imp_ chi)))

  -- `⊢ (¬ phi → ¬ psi) → (psi → phi)`
  | prop_3_
    (phi psi : Formula_) :
    is_proof_v2
      (((not_ phi).imp_ (not_ psi)).imp_
        (psi.imp_ phi))

  -- `⊢ (∀ v (phi → psi)) → ((∀ v phi) → (∀ v psi))`
  | pred_1_
    (v : VarName_) (phi psi : Formula_) :
    is_proof_v2
      ((forall_ v (phi.imp_ psi)).imp_
        ((forall_ v phi).imp_
          (forall_ v psi)))

  -- `⊢ (∀ v phi) → phi(t/v)` provided `phi` admits `t` for `v`
  | pred_2_
    (v t : VarName_) (phi phi' : Formula_) :
    FOL.NV.Sub.Var.One.Rec.fast_admits_var_one_rec v t phi →
      FOL.NV.Sub.Var.One.Rec.fast_replace_free_var_one_rec v t phi = phi' →
        is_proof_v2 ((forall_ v phi).imp_ phi')

  -- `⊢ phi → (∀ v phi)` provided `v` is not free in `phi`
  | pred_3_
    (v : VarName_)
    (phi : Formula_) :
    ¬ var_is_free_in v phi →
    is_proof_v2 (phi.imp_ (forall_ v phi))

  -- `⊢ ∀ v (v = v)`
  | eq_1_
    (v : VarName_) :
    is_proof_v2 (forall_ v (eq_ v v))

  /-
    `⊢ ∀ x_0 ... ∀ x_n ∀ y_0 ... y_n ((x_0 = y_0) ∧ ... ∧ (x_n = y_n) ∧ ⊤) →((pred_ name [x_0 ... x_n] ↔ pred_ name [y_0 ... y_n]))`
  -/
  | eq_2_pred_const_
    (name : PredName_)
    (n : ℕ)
    (xs ys : Fin n → VarName_) :
    is_proof_v2
      (Forall_ (List.ofFn xs)
        (Forall_ (List.ofFn ys)
          ((And_ (List.ofFn fun i : Fin n => eq_ (xs i) (ys i))).imp_
            ((pred_const_ name (List.ofFn xs)).iff_ (pred_const_ name (List.ofFn ys))))))

  /-
    `⊢ ∀ x_0 ∀ x_1 ∀ y_0 ∀ y_1 ((x_0 = y_0) ∧ (x_1 = y_1)) → ((eq_ x_0 x_1) ↔ (eq_ y_0 y_1))`
  -/
  | eq_2_eq_
    (x_0 x_1 y_0 y_1 : VarName_) :
    is_proof_v2
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
    is_proof_v2 phi →
    is_proof_v2 (forall_ v phi)

  -- `⊢ phi → psi ⇒ ⊢ phi ⇒ ⊢ psi`
  | mp_
    (phi psi : Formula_) :
    is_proof_v2 (phi.imp_ psi) →
    is_proof_v2 phi →
    is_proof_v2 psi

  | def_false_ :
    is_proof_v2 (false_.iff_ (not_ true_))

  | def_and_
    (phi psi : Formula_) :
    is_proof_v2 ((phi.and_ psi).iff_ (not_ (phi.imp_ (not_ psi))))

  | def_or_
    (phi psi : Formula_) :
    is_proof_v2 ((phi.or_ psi).iff_ ((not_ phi).imp_ psi))

  | def_iff_
    (phi psi : Formula_) :
    is_proof_v2 (not_ (((phi.iff_ psi).imp_ (not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi))))).imp_ (not_ ((not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi)))).imp_ (phi.iff_ psi)))))

  | def_exists_
    (v : VarName_)
    (phi : Formula_) :
    is_proof_v2 ((exists_ v phi).iff_ (not_ (forall_ v (not_ phi))))

#lint
