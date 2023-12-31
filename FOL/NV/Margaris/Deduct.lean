import FOL.NV.Sub.Var.One.Rec.Admits


set_option autoImplicit false


namespace FOL.NV.Margaris

open Formula


/--
  IsPropAxiom F := True if and only if F is a logical axiom of classical propositional logic.
-/
inductive IsPropAxiom : Formula → Prop
  -- ⊢ ⊤
  | prop_true_ :
    IsPropAxiom true_

  -- ⊢ phi → (psi → phi)
  | prop_1_
    (phi psi : Formula) :
    IsPropAxiom (phi.imp_ (psi.imp_ phi))

  -- ⊢ (phi → (psi → chi)) → ((phi → psi) → (phi → chi))
  | prop_2_
    (phi psi chi : Formula) :
    IsPropAxiom ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi)))

  -- ⊢ (¬ phi → ¬ psi) → (psi → phi)
  | prop_3_
    (phi psi : Formula) :
    IsPropAxiom (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi))

  | def_false_ :
    IsPropAxiom (false_.iff_ (not_ true_))

  | def_and_
    (phi psi : Formula) :
    IsPropAxiom ((phi.and_ psi).iff_ (not_ (phi.imp_ (not_ psi))))

  | def_or_
    (phi psi : Formula) :
    IsPropAxiom ((phi.or_ psi).iff_ ((not_ phi).imp_ psi))

  | def_iff_
    (phi psi : Formula) :
    IsPropAxiom (not_ (((phi.iff_ psi).imp_ (not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi))))).imp_ (not_ ((not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi)))).imp_ (phi.iff_ psi)))))


/--
  IsPropDeduct Δ F := True if and only if there is a deduction of F from Δ in classical propositional logic.
-/
inductive IsPropDeduct (Δ : Set Formula) : Formula → Prop
  | axiom_
    (phi : Formula) :
    IsPropAxiom phi →
    IsPropDeduct Δ phi

  | assume_
    (phi : Formula) :
    phi ∈ Δ →
    IsPropDeduct Δ phi

  | mp_
    (phi psi : Formula) :
    IsPropDeduct Δ (phi.imp_ psi) →
    IsPropDeduct Δ phi →
    IsPropDeduct Δ psi


/--
  IsPropProof F := True if and only if there is a proof of F in classical propositional logic.
-/
def IsPropProof (phi : Formula) : Prop :=
  IsPropDeduct ∅ phi


/--
  IsAxiom F := True if and only if F is a logical axiom of classical first order logic.
-/
inductive IsAxiom : Formula → Prop
  -- ⊢ ⊤
  | prop_true_ :
    IsAxiom true_

  -- ⊢ phi → (psi → phi)
  | prop_1_
    (phi psi : Formula) :
    IsAxiom (phi.imp_ (psi.imp_ phi))

  -- ⊢ (phi → (psi → chi)) → ((phi → psi) → (phi → chi))
  | prop_2_
    (phi psi chi : Formula) :
    IsAxiom ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi)))

  -- ⊢ (¬ phi → ¬ psi) → (psi → phi)
  | prop_3_
    (phi psi : Formula) :
    IsAxiom (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi))

  -- ⊢ (∀ v (phi → psi)) → ((∀ v phi) → (∀ v psi))
  | pred_1_
    (v : VarName)
    (phi psi : Formula) :
    IsAxiom ((forall_ v (phi.imp_ psi)).imp_ ((forall_ v phi).imp_ (forall_ v psi)))

  -- ⊢ (∀ v phi) → phi(t/v)  provided phi admits t for v
  | pred_2_
    (v t : VarName)
    (phi phi' : Formula) :
    Sub.Var.One.Rec.fastAdmits v t phi →
    Sub.Var.One.Rec.fastReplaceFree v t phi = phi' →
    IsAxiom ((forall_ v phi).imp_ phi')

  -- ⊢ phi → (∀ v phi)  provided v is not free in phi
  | pred_3_
    (v : VarName)
    (phi : Formula) :
    ¬ isFreeIn v phi →
    IsAxiom (phi.imp_ (forall_ v phi))

  -- ⊢ ∀ v (v = v)
  | eq_1_ (v : VarName) :
    IsAxiom (forall_ v (eq_ v v))

  /-
    ⊢ ∀ x_0 ... ∀ x_n ∀ y_0 ... y_n ((x_0 = y_0) ∧ ... ∧ (x_n = y_n) ∧ ⊤) →((pred_ name [x_0 ... x_n] ↔ pred_ name [y_0 ... y_n]))
  -/
  | eq_2_pred_const_
    (name : PredName)
    (n : ℕ)
    (xs ys : Fin n → VarName) :
    IsAxiom
      (Forall_ (List.ofFn xs)
        (Forall_ (List.ofFn ys)
          ((And_ (List.ofFn fun i : Fin n => eq_ (xs i) (ys i))).imp_
            ((pred_const_ name (List.ofFn xs)).iff_ (pred_const_ name (List.ofFn ys))))))

  /-
    ⊢ ∀ x_0 ∀ x_1 ∀ y_0 ∀ y_1 ((x_0 = y_0) ∧ (x_1 = y_1)) → ((eq_ x_0 x_1) ↔ (eq_ y_0 y_1))
  -/
  | eq_2_eq_
    (x_0 x_1 y_0 y_1 : VarName) :
    IsAxiom
      (forall_ x_0
        (forall_ x_1
          (forall_ y_0
            (forall_ y_1
              ((and_ (eq_ x_0 y_0) (eq_ x_1 y_1)).imp_
                ((eq_ x_0 x_1).iff_ (eq_ y_0 y_1)))))))

  -- ⊢ phi ⇒ ⊢ ∀ v phi
  | gen_
    (v : VarName)
    (phi : Formula) :
    IsAxiom phi →
    IsAxiom (forall_ v phi)

  | def_false_ :
    IsAxiom (false_.iff_ (not_ true_))

  | def_and_
    (phi psi : Formula) :
    IsAxiom ((phi.and_ psi).iff_ (not_ (phi.imp_ (not_ psi))))

  | def_or_
    (phi psi : Formula) :
    IsAxiom ((phi.or_ psi).iff_ ((not_ phi).imp_ psi))

  | def_iff_
    (phi psi : Formula) :
    IsAxiom (not_ (((phi.iff_ psi).imp_ (not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi))))).imp_ (not_ ((not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi)))).imp_ (phi.iff_ psi)))))

  | def_exists_
    (v : VarName)
    (phi : Formula) :
    IsAxiom ((exists_ v phi).iff_ (not_ (forall_ v (not_ phi))))

/--
  IsDeduct Δ F := True if and only if there is a deduction of F from Δ in classical first order logic.
-/
inductive IsDeduct (Δ : Set Formula) : Formula → Prop

  | axiom_
    (phi : Formula) :
    IsAxiom phi →
    IsDeduct Δ phi

  | assume_
    (phi : Formula) :
    phi ∈ Δ →
    IsDeduct Δ phi

  | mp_
    (phi psi : Formula) :
    IsDeduct Δ (phi.imp_ psi) →
    IsDeduct Δ phi →
    IsDeduct Δ psi


/--
  IsProof F := True if and only if there is a proof of F in classical first order logic.
-/
def IsProof (F : Formula) : Prop :=
  IsDeduct ∅ F


/--
  IsProofAlt F := True if and only if there is a proof of F in classical first order logic.

  This definition is equivalent to IsProof.
-/
inductive IsProofAlt : Formula → Prop

  -- ⊢ ⊤
  | prop_true_ : IsProofAlt true_

  -- ⊢ phi → (psi → phi)
  | prop_1_
    (phi psi : Formula) :
    IsProofAlt (phi.imp_ (psi.imp_ phi))

  -- ⊢ (phi → (psi → chi)) → ((phi → psi) → (phi → chi))
  | prop_2_
    (phi psi chi : Formula) :
    IsProofAlt
      ((phi.imp_ (psi.imp_ chi)).imp_
        ((phi.imp_ psi).imp_ (phi.imp_ chi)))

  -- ⊢ (¬ phi → ¬ psi) → (psi → phi)
  | prop_3_
    (phi psi : Formula) :
    IsProofAlt
      (((not_ phi).imp_ (not_ psi)).imp_
        (psi.imp_ phi))

  -- ⊢ (∀ v (phi → psi)) → ((∀ v phi) → (∀ v psi))
  | pred_1_
    (v : VarName) (phi psi : Formula) :
    IsProofAlt
      ((forall_ v (phi.imp_ psi)).imp_
        ((forall_ v phi).imp_
          (forall_ v psi)))

  -- ⊢ (∀ v phi) → phi(t/v)  provided phi admits t for v
  | pred_2_
    (v t : VarName) (phi phi' : Formula) :
    Sub.Var.One.Rec.fastAdmits v t phi →
      Sub.Var.One.Rec.fastReplaceFree v t phi = phi' →
        IsProofAlt ((forall_ v phi).imp_ phi')

  -- ⊢ phi → (∀ v phi)  provided v is not free in phi
  | pred_3_
    (v : VarName)
    (phi : Formula) :
    ¬ isFreeIn v phi →
    IsProofAlt (phi.imp_ (forall_ v phi))

  -- ⊢ ∀ v (v = v)
  | eq_1_
    (v : VarName) :
    IsProofAlt (forall_ v (eq_ v v))

  /-
    ⊢ ∀ x_0 ... ∀ x_n ∀ y_0 ... y_n ((x_0 = y_0) ∧ ... ∧ (x_n = y_n) ∧ ⊤) →((pred_ name [x_0 ... x_n] ↔ pred_ name [y_0 ... y_n]))
  -/
  | eq_2_pred_const_
    (name : PredName)
    (n : ℕ)
    (xs ys : Fin n → VarName) :
    IsProofAlt
      (Forall_ (List.ofFn xs)
        (Forall_ (List.ofFn ys)
          ((And_ (List.ofFn fun i : Fin n => eq_ (xs i) (ys i))).imp_
            ((pred_const_ name (List.ofFn xs)).iff_ (pred_const_ name (List.ofFn ys))))))

  /-
    ⊢ ∀ x_0 ∀ x_1 ∀ y_0 ∀ y_1 ((x_0 = y_0) ∧ (x_1 = y_1)) → ((eq_ x_0 x_1) ↔ (eq_ y_0 y_1))
  -/
  | eq_2_eq_
    (x_0 x_1 y_0 y_1 : VarName) :
    IsProofAlt
      (forall_ x_0
        (forall_ x_1
          (forall_ y_0
            (forall_ y_1
              ((and_ (eq_ x_0 y_0) (eq_ x_1 y_1)).imp_
                ((eq_ x_0 x_1).iff_ (eq_ y_0 y_1)))))))

  -- ⊢ phi ⇒ ⊢ ∀ v phi
  | gen_
    (v : VarName)
    (phi : Formula) :
    IsProofAlt phi →
    IsProofAlt (forall_ v phi)

  -- ⊢ phi → psi ⇒ ⊢ phi ⇒ ⊢ psi
  | mp_
    (phi psi : Formula) :
    IsProofAlt (phi.imp_ psi) →
    IsProofAlt phi →
    IsProofAlt psi

  | def_false_ :
    IsProofAlt (false_.iff_ (not_ true_))

  | def_and_
    (phi psi : Formula) :
    IsProofAlt ((phi.and_ psi).iff_ (not_ (phi.imp_ (not_ psi))))

  | def_or_
    (phi psi : Formula) :
    IsProofAlt ((phi.or_ psi).iff_ ((not_ phi).imp_ psi))

  | def_iff_
    (phi psi : Formula) :
    IsProofAlt (not_ (((phi.iff_ psi).imp_ (not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi))))).imp_ (not_ ((not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi)))).imp_ (phi.iff_ psi)))))

  | def_exists_
    (v : VarName)
    (phi : Formula) :
    IsProofAlt ((exists_ v phi).iff_ (not_ (forall_ v (not_ phi))))

#lint
