import FOL.NV.Rules.Prop.Prop_1.Prop
import FOL.NV.Rules.Pred.Pred_2.Pred
import FOL.NV.Sub.Var.One.Rec.Admits
import FOL.NV.ReplaceSubFormula


set_option autoImplicit false


open Formula_

open FOL.NV.Sub.Var.One.Rec


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


-------------------------------------------------------------------------------


lemma is_prop_axiom_v1_imp_is_axiom_v1
  (F : Formula_)
  (h1 : is_prop_axiom_v1 F) :
  is_axiom_v1 F :=
  by
  induction h1
  case prop_true_ =>
    apply is_axiom_v1.prop_true_
  case prop_1_ phi psi =>
    apply is_axiom_v1.prop_1_
  case prop_2_ phi psi chi =>
    apply is_axiom_v1.prop_2_
  case prop_3_ phi psi =>
    apply is_axiom_v1.prop_3_
  case def_false_ =>
    apply is_axiom_v1.def_false_
  case def_and_ phi psi =>
    apply is_axiom_v1.def_and_
  case def_or_ phi psi =>
    apply is_axiom_v1.def_or_
  case def_iff_ phi psi =>
    apply is_axiom_v1.def_iff_


lemma is_prop_deduct_v1_imp_is_deduct_v1
  (Δ : Set Formula_)
  (F : Formula_)
  (h1 : is_prop_deduct_v1 Δ F) :
  is_deduct_v1 Δ F :=
  by
  induction h1
  case axiom_ phi ih =>
    apply is_deduct_v1.axiom_
    apply is_prop_axiom_v1_imp_is_axiom_v1
    exact ih
  case assume_ phi ih =>
    apply is_deduct_v1.assume_
    exact ih
  case mp_ phi psi ih_1 ih_2 ih_3 ih_4 =>
    apply is_deduct_v1.mp_ phi
    · exact ih_3
    · exact ih_4


lemma is_prop_proof_v1_imp_is_proof_v1
  (F : Formula_)
  (h1 : is_prop_proof_v1 F) :
  is_proof_v1 F :=
  by
  unfold is_prop_proof_v1 at h1
  unfold is_proof_v1
  apply is_prop_deduct_v1_imp_is_deduct_v1
  exact h1


-------------------------------------------------------------------------------


/--
phi ∧ psi := ¬ ( phi → ¬ psi )
-/
axiom def_and_ (phi psi : Formula_) : and_ phi psi = not_ (phi.imp_ (not_ psi))

/--
  phi ↔ psi := ( phi → psi ) ∧ ( psi → phi )
-/
axiom def_iff_ (phi psi : Formula_) : iff_ phi psi = (phi.imp_ psi).and_ (psi.imp_ phi)

/--
  ∃ x phi := ¬ ∀ x ¬ phi
-/
axiom def_exists_ (x : VarName_) (phi : Formula_) : exists_ x phi = not_ (forall_ x (not_ phi))


def def_eq_ (x y : VarName_) : Formula_ :=
  pred_const_ (PredName_.mk "=") [x, y]


theorem T_14_10_pred_v1
  (Δ : Set Formula_)
  (F : Formula_)
  (h1 : is_deduct_v1 Δ F) :
  ∀ (Γ : Set Formula_), is_deduct_v1 (Δ ∪ Γ) F :=
  by
  intro Γ
  induction h1
  case axiom_ h1_phi h1_1 =>
    apply is_deduct_v1.axiom_
    exact h1_1
  case assume_ h1_phi h1_1 =>
    apply is_deduct_v1.assume_
    simp
    left
    exact h1_1
  case mp_ h1_phi h1_psi _ _ h1_ih_1 h1_ih_2 =>
    apply is_deduct_v1.mp_ h1_phi
    · exact h1_ih_1
    · exact h1_ih_2


theorem C_14_11_pred_v1
  (F : Formula_)
  (h1 : is_proof_v1 F) :
  ∀ (Δ : Set Formula_), is_deduct_v1 Δ F :=
  by
  intro Δ
  obtain s1 := T_14_10_pred_v1 ∅ F h1 Δ
  simp at s1
  exact s1

alias proof_imp_deduct_pred_v1 := C_14_11_pred_v1


-- Deduction Theorem
theorem T_14_3_pred_v1
  (Δ : Set Formula_)
  (P Q : Formula_)
  (h1 : is_deduct_v1 (Δ ∪ {P}) Q) :
  is_deduct_v1 Δ (P.imp_ Q) :=
  by
  induction h1
  case axiom_ h1_phi h1_1 =>
    apply is_deduct_v1.mp_ h1_phi
    · apply is_deduct_v1.axiom_
      apply is_axiom_v1.prop_1_
    · apply is_deduct_v1.axiom_
      exact h1_1
  case assume_ h1_phi h1_1 =>
    simp at h1_1
    cases h1_1
    case inl h1_1 =>
      rw [h1_1]
      apply proof_imp_deduct_pred_v1
      apply is_prop_proof_v1_imp_is_proof_v1
      apply prop_id
    case inr h1_1 =>
      apply is_deduct_v1.mp_ h1_phi
      · apply is_deduct_v1.axiom_
        apply is_axiom_v1.prop_1_
      · apply is_deduct_v1.assume_
        exact h1_1
  case mp_ h1_phi h1_psi _ _ h1_ih_1
    h1_ih_2 =>
    apply is_deduct_v1.mp_ (P.imp_ h1_phi)
    · apply is_deduct_v1.mp_ (P.imp_ (h1_phi.imp_ h1_psi))
      · apply is_deduct_v1.axiom_
        apply is_axiom_v1.prop_2_
      · exact h1_ih_1
    · exact h1_ih_2

alias deduction_theorem_pred_v1 := T_14_3_pred_v1


/-
/--
  IsReplOfVarInListFun u v l_u l_v := True if and only if l_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of u in l_u by occurrences of v.
-/
def IsReplOfVarInListFun
  (u v : VarName_) :
  List VarName_ → List VarName_ → Prop
  | [], [] => True
  | hd_u :: tl_u, hd_v :: tl_v =>
    (hd_u = hd_v ∨ (hd_u = u ∧ hd_v = v)) ∧ IsReplOfVarInListFun u v tl_u tl_v
  | _, _ => False


/--
  IsReplOfVarInFormulaFun u v P_u P_v := True if and only if P_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of u in P_u by occurrences of v.
-/
def IsReplOfVarInFormulaFun
  (u v : VarName_) :
  Formula_ → Formula_ → Prop
  | pred_var_ name_u args_u, pred_var_ name_v args_v =>
      name_u = name_v ∧ IsReplOfVarInListFun u v args_u args_v
  | pred_const_ name_u args_u, pred_const_ name_v args_v =>
      name_u = name_v ∧ IsReplOfVarInListFun u v args_u args_v
  | eq_ x_u y_u, eq_ x_v y_v =>
      IsReplOfVarInListFun u v [x_u, y_u] [x_v, y_v]
  | true_, true_ => True
  | false_, false_ => True
  | not_ P_u, not_ P_v => IsReplOfVarInFormulaFun u v P_u P_v
  | imp_ P_u Q_u, imp_ P_v Q_v =>
      IsReplOfVarInFormulaFun u v P_u P_v ∧
      IsReplOfVarInFormulaFun u v Q_u Q_v
  | and_ P_u Q_u, and_ P_v Q_v =>
      IsReplOfVarInFormulaFun u v P_u P_v ∧
      IsReplOfVarInFormulaFun u v Q_u Q_v
  | or_ P_u Q_u, or_ P_v Q_v =>
      IsReplOfVarInFormulaFun u v P_u P_v ∧
      IsReplOfVarInFormulaFun u v Q_u Q_v
  | iff_ P_u Q_u, iff_ P_v Q_v =>
      IsReplOfVarInFormulaFun u v P_u P_v ∧
      IsReplOfVarInFormulaFun u v Q_u Q_v
  | forall_ x P_u, forall_ x' P_v =>
      x = x' ∧ IsReplOfVarInFormulaFun u v P_u P_v
  | exists_ x P_u, exists_ x' P_v =>
      x = x' ∧ IsReplOfVarInFormulaFun u v P_u P_v
  | _, _ => False


/--
  IsReplOfVarInFormula u v P_u P_v := True if and only if P_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of u in P_u by occurrences of v.
-/
inductive IsReplOfVarInFormula
  (u v : VarName_) :
  Formula_ → Formula_ → Prop
  | pred_const_
    (name : PredName_)
    (n : ℕ)
    (args_u args_v : Fin n → VarName_) :
    (∀ (i : Fin n), (args_u i = args_v i) ∨ (args_u i = u ∧ args_v i = v)) →
    IsReplOfVarInFormula u v (pred_const_ name (List.ofFn args_u)) (pred_const_ name (List.ofFn args_v))

  | pred_var_
    (name : PredName_)
    (n : ℕ)
    (args_u args_v : Fin n → VarName_) :
    (∀ (i : Fin n), (args_u i = args_v i) ∨ (args_u i = u ∧ args_v i = v)) →
    IsReplOfVarInFormula u v (pred_var_ name (List.ofFn args_u)) (pred_var_ name (List.ofFn args_v))

  | eq_
    (x_u y_u x_v y_v : VarName_) :
    ((x_u = x_v) ∨ (x_u = u ∧ x_v = v)) →
    ((y_u = y_v) ∨ (y_u = u ∧ y_v = v)) →
    IsReplOfVarInFormula u v (eq_ x_u y_u) (eq_ x_v y_v)

  | true_ :
    IsReplOfVarInFormula u v true_ true_

  | false_ :
    IsReplOfVarInFormula u v false_ false_

  | not_
    (P_u P_v : Formula_) :
    IsReplOfVarInFormula u v P_u P_v →
    IsReplOfVarInFormula u v P_u.not_ P_v.not_

  | imp_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    IsReplOfVarInFormula u v P_u P_v →
    IsReplOfVarInFormula u v Q_u Q_v →
    IsReplOfVarInFormula u v (P_u.imp_ Q_u) (P_v.imp_ Q_v)

  | and_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    IsReplOfVarInFormula u v P_u P_v →
    IsReplOfVarInFormula u v Q_u Q_v →
    IsReplOfVarInFormula u v (P_u.and_ Q_u) (P_v.and_ Q_v)

  | or_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    IsReplOfVarInFormula u v P_u P_v →
    IsReplOfVarInFormula u v Q_u Q_v →
    IsReplOfVarInFormula u v (P_u.or_ Q_u) (P_v.or_ Q_v)

  | iff_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    IsReplOfVarInFormula u v P_u P_v →
    IsReplOfVarInFormula u v Q_u Q_v →
    IsReplOfVarInFormula u v (P_u.iff_ Q_u) (P_v.iff_ Q_v)

  | forall_
    (x : VarName_)
    (P_u P_v : Formula_) :
    IsReplOfVarInFormula u v P_u P_v →
    IsReplOfVarInFormula u v (forall_ x P_u) (forall_ x P_v)

  | exists_
    (x : VarName_)
    (P_u P_v : Formula_) :
    IsReplOfVarInFormula u v P_u P_v →
    IsReplOfVarInFormula u v (exists_ x P_u) (exists_ x P_v)


theorem extracted_1
  (u v : VarName_)
  (n : ℕ)
  (args_u args_v : Fin n → VarName_)
  (h1 : ∀ (i : Fin n), args_u i = args_v i ∨ args_u i = u ∧ args_v i = v) :
  IsReplOfVarInListFun u v (List.ofFn args_u) (List.ofFn args_v) :=
  by
  induction n
  case zero =>
    simp_all only [IsEmpty.forall_iff, List.ofFn_zero]
    unfold IsReplOfVarInListFun
    trivial
  case succ m ih =>
    simp_all only [List.ofFn_succ]
    unfold IsReplOfVarInListFun
    constructor
    · apply h1
    · exact ih (fun i => args_u i.succ) (fun i => args_v i.succ) fun i => h1 i.succ


example
  (u v : VarName_)
  (F F' : Formula_)
  (h1 : IsReplOfVarInFormula u v F F') :
  IsReplOfVarInFormulaFun u v F F' :=
  by
  induction h1
  case
      pred_const_ name n args_u args_v ih
    | pred_var_ name n args_u args_v ih =>
    unfold IsReplOfVarInFormulaFun
    constructor
    · rfl
    · apply extracted_1
      exact ih
  case eq_ x_u y_u x_v y_v ih_1 ih_2 =>
    unfold IsReplOfVarInFormulaFun
    simp only [IsReplOfVarInListFun]
    tauto
  case true_ =>
    simp only [IsReplOfVarInFormulaFun]
  case false_ =>
    simp only [IsReplOfVarInFormulaFun]
  case not_ P_u P_v ih_1 ih_2 =>
    unfold IsReplOfVarInFormulaFun
    exact ih_2
  case
      imp_ P_u Q_u P_v Q_v ih_1 ih_2 ih_3 ih_4
    | and_ P_u Q_u P_v Q_v ih_1 ih_2 ih_3 ih_4
    | or_ P_u Q_u P_v Q_v ih_1 ih_2 ih_3 ih_4
    | iff_ P_u Q_u P_v Q_v ih_1 ih_2 ih_3 ih_4 =>
    unfold IsReplOfVarInFormulaFun
    tauto
  case
      forall_ x P_u P_v ih_1 ih_2
    | exists_ x P_u P_v ih_1 ih_2 =>
    unfold IsReplOfVarInFormulaFun
    tauto


/--
  IsReplOfFormulaInFormulaFun U V P_u P_v := True if and only if P_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of U in P_u by occurrences of V.
-/
def IsReplOfFormulaInFormulaFun
  (U V : Formula_) :
  Formula_ → Formula_ → Prop
  | not_ P_u, not_ P_v => IsReplOfFormulaInFormulaFun U V P_u P_v
  | imp_ P_u Q_u, imp_ P_v Q_v =>
    IsReplOfFormulaInFormulaFun U V P_u P_v ∧ IsReplOfFormulaInFormulaFun U V Q_u Q_v
  | and_ P_u Q_u, and_ P_v Q_v =>
    IsReplOfFormulaInFormulaFun U V P_u P_v ∧ IsReplOfFormulaInFormulaFun U V Q_u Q_v
  | or_ P_u Q_u, or_ P_v Q_v =>
    IsReplOfFormulaInFormulaFun U V P_u P_v ∧ IsReplOfFormulaInFormulaFun U V Q_u Q_v
  | iff_ P_u Q_u, iff_ P_v Q_v =>
    IsReplOfFormulaInFormulaFun U V P_u P_v ∧ IsReplOfFormulaInFormulaFun U V Q_u Q_v
  | forall_ x P_u, forall_ x' P_v => x = x' ∧ IsReplOfFormulaInFormulaFun U V P_u P_v
  | exists_ x P_u, exists_ x' P_v => x = x' ∧ IsReplOfFormulaInFormulaFun U V P_u P_v
  | P_u, P_v => P_u = P_v ∨ (P_u = U ∧ P_v = V)


/--
  IsReplOfFormulaInFormula U V P_u P_v := True if and only if P_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of U in P_u by occurrences of V.
-/
inductive IsReplOfFormulaInFormula
  (U V : Formula_) :
  Formula_ → Formula_ → Prop

    -- not replacing an occurrence
  | same_
    (P_u P_v : Formula_) :
    P_u = P_v →
    IsReplOfFormulaInFormula U V P_u P_v

    -- replacing an occurrence
  | diff_
    (P_u P_v : Formula_) :
    P_u = U →
    P_v = V →
    IsReplOfFormulaInFormula U V P_u P_v

  | not_
    (P_u P_v : Formula_) :
    IsReplOfFormulaInFormula U V P_u P_v →
    IsReplOfFormulaInFormula U V P_u.not_ P_v.not_

  | imp_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    IsReplOfFormulaInFormula U V P_u P_v →
    IsReplOfFormulaInFormula U V Q_u Q_v →
    IsReplOfFormulaInFormula U V (P_u.imp_ Q_u) (P_v.imp_ Q_v)

  | and_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    IsReplOfFormulaInFormula U V P_u P_v →
    IsReplOfFormulaInFormula U V Q_u Q_v →
    IsReplOfFormulaInFormula U V (P_u.and_ Q_u) (P_v.and_ Q_v)

  | or_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    IsReplOfFormulaInFormula U V P_u P_v →
    IsReplOfFormulaInFormula U V Q_u Q_v →
    IsReplOfFormulaInFormula U V (P_u.or_ Q_u) (P_v.or_ Q_v)

  | iff_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    IsReplOfFormulaInFormula U V P_u P_v →
    IsReplOfFormulaInFormula U V Q_u Q_v →
    IsReplOfFormulaInFormula U V (P_u.iff_ Q_u) (P_v.iff_ Q_v)

  | forall_
    (x : VarName_)
    (P_u P_v : Formula_) :
    IsReplOfFormulaInFormula U V P_u P_v →
    IsReplOfFormulaInFormula U V (forall_ x P_u) (forall_ x P_v)

  | exists_
    (x : VarName_)
    (P_u P_v : Formula_) :
    IsReplOfFormulaInFormula U V P_u P_v →
    IsReplOfFormulaInFormula U V (exists_ x P_u) (exists_ x P_v)
-/


def similar
  (P_u P_v : Formula_)
  (u v : VarName_) :
  Prop :=
  ¬ var_is_free_in v P_u ∧
    ¬ var_is_free_in u P_v ∧
      fast_admits_var_one_rec u v P_u ∧
        fast_admits_var_one_rec v u P_v ∧ P_v = fast_replace_free_var_one_rec u v P_u ∧ P_u = fast_replace_free_var_one_rec v u P_v


-- Universal Elimination
theorem T_17_1
  (P : Formula_)
  (v t : VarName_)
  (Δ : Set Formula_)
  (h1 : is_deduct_v1 Δ (forall_ v P))
  (h2 : fast_admits_var_one_rec v t P) :
  is_deduct_v1 Δ (fast_replace_free_var_one_rec v t P) :=
  by
  apply is_deduct_v1.mp_ (forall_ v P)
  · apply is_deduct_v1.axiom_
    apply is_axiom_v1.pred_2_ v t P (fast_replace_free_var_one_rec v t P) h2
    rfl
  · exact h1

alias spec := T_17_1
alias forall_elim := T_17_1


theorem spec_id
  (v : VarName_)
  (P : Formula_)
  (Δ : Set Formula_)
  (h1 : is_deduct_v1 Δ (forall_ v P)) :
  is_deduct_v1 Δ P :=
  by
  apply is_deduct_v1.mp_ (forall_ v P)
  · apply is_deduct_v1.axiom_
    apply is_axiom_v1.pred_2_ v v P
    · apply fast_admits_var_one_rec_self
    · apply fast_replace_free_var_one_rec_self
  · exact h1

alias forall_elim_id := spec_id


theorem T_17_3
  (P : Formula_)
  (v t : VarName_)
  (h1 : fast_admits_var_one_rec v t P) :
  is_proof_v1 ((fast_replace_free_var_one_rec v t P).imp_ (exists_ v P)) :=
  by
  simp only [fast_admits_var_one_rec] at h1

  simp only [def_exists_]
  -- simp only [Formula_.exists_]

  simp only [is_proof_v1]
  apply is_deduct_v1.mp_ ((forall_ v P.not_).imp_ (fast_replace_free_var_one_rec v t P).not_)
  · apply is_prop_deduct_v1_imp_is_deduct_v1
    SC
  · apply is_deduct_v1.axiom_
    apply is_axiom_v1.pred_2_ v t
    · simp only [fast_admits_var_one_rec]
      simp only [fast_admits_var_one_rec_aux]
      exact h1
    · rfl


-- Existential Introduction
theorem T_17_4
  (P : Formula_)
  (v t : VarName_)
  (Δ : Set Formula_)
  (h1 : fast_admits_var_one_rec v t P)
  (h2 : is_deduct_v1 Δ (fast_replace_free_var_one_rec v t P)) :
  is_deduct_v1 Δ (exists_ v P) :=
  by
  apply is_deduct_v1.mp_ (fast_replace_free_var_one_rec v t P)
  · apply proof_imp_deduct_pred_v1
    apply T_17_3
    exact h1
  · exact h2

alias exists_intro := T_17_4


theorem exists_intro_id
  (P : Formula_)
  (v : VarName_)
  (Δ : Set Formula_)
  (h1 : is_deduct_v1 Δ P) :
  is_deduct_v1 Δ (exists_ v P) :=
  by
  apply T_17_4 P v v Δ
  · apply fast_admits_var_one_rec_self
  · simp only [fast_replace_free_var_one_rec_self]
    exact h1


theorem T_17_6
  (P : Formula_)
  (v : VarName_) :
  is_proof_v1 ((forall_ v P).imp_ (exists_ v P)) :=
  by
  apply deduction_theorem_pred_v1
  simp
  apply exists_intro_id
  apply spec_id v
  apply is_deduct_v1.assume_
  simp


theorem T_17_7
  (F : Formula_)
  (v : VarName_)
  (Δ : Set Formula_)
  (h1 : is_deduct_v1 Δ F)
  (h2 : ∀ (H : Formula_), H ∈ Δ → ¬ var_is_free_in v H) :
  is_deduct_v1 Δ (forall_ v F) :=
  by
  induction h1
  case axiom_ h1_phi h1_1 =>
    apply is_deduct_v1.axiom_
    apply is_axiom_v1.gen_
    exact h1_1
  case assume_ h1_phi h1_1 =>
    apply is_deduct_v1.mp_ h1_phi
    · apply is_deduct_v1.axiom_
      apply is_axiom_v1.pred_3_
      exact h2 h1_phi h1_1
    · apply is_deduct_v1.assume_
      exact h1_1
  case mp_ h1_phi h1_psi _ _ h1_ih_1 h1_ih_2 =>
    apply is_deduct_v1.mp_ (forall_ v h1_phi)
    · apply is_deduct_v1.mp_ (forall_ v (h1_phi.imp_ h1_psi))
      · apply is_deduct_v1.axiom_
        apply is_axiom_v1.pred_1_
      · exact h1_ih_1
    · exact h1_ih_2

alias generalization := T_17_7


-- Universal Introduction
theorem univ_intro
  (P : Formula_)
  (v t : VarName_)
  (Δ : Set Formula_)
  (h1 : ¬ var_occurs_in t P)
  (h2 : is_deduct_v1 Δ (fast_replace_free_var_one_rec v t P))
  (h3 : ∀ (H : Formula_), H ∈ Δ → ¬ var_is_free_in t H) :
  is_deduct_v1 Δ (forall_ v P) :=
  by
  rw [← fast_replace_free_var_one_rec_inverse P v t h1]
  apply is_deduct_v1.mp_ (forall_ t (fast_replace_free_var_one_rec v t P))
  · apply proof_imp_deduct_pred_v1
    apply deduction_theorem_pred_v1
    simp
    apply generalization
    · apply spec
      · apply is_deduct_v1.assume_
        simp
      · apply fast_replace_free_var_one_rec_fast_admits_var_one_rec
        exact h1
    · simp
      simp only [var_is_free_in]
      simp
      intro a1 contra
      exact not_var_is_free_in_fast_replace_free_var_one_rec P v t a1 contra
  · exact generalization (fast_replace_free_var_one_rec v t P) t Δ h2 h3


theorem is_proof_v2_imp_is_proof_v1
  (F : Formula_)
  (h1 : is_proof_v2 F) :
  is_proof_v1 F :=
  by
  unfold is_proof_v1
  induction h1
  case prop_true_ =>
    apply is_deduct_v1.axiom_
    apply is_axiom_v1.prop_true_
  case prop_1_ h1_phi h1_psi =>
    apply is_deduct_v1.axiom_
    apply is_axiom_v1.prop_1_
  case prop_2_ h1_phi h1_psi h1_chi =>
    apply is_deduct_v1.axiom_
    apply is_axiom_v1.prop_2_
  case prop_3_ h1_phi h1_psi =>
    apply is_deduct_v1.axiom_
    apply is_axiom_v1.prop_3_
  case pred_1_ h1_v h1_phi h1_psi =>
    apply is_deduct_v1.axiom_
    apply is_axiom_v1.pred_1_
  case pred_2_ h1_v h1_t h1_phi h1_phi' h1_1 h1_ih_1 =>
    apply is_deduct_v1.axiom_
    exact is_axiom_v1.pred_2_ h1_v h1_t h1_phi h1_phi' h1_1 h1_ih_1
  case pred_3_ h1_v h1_phi h1_1 =>
    apply is_deduct_v1.axiom_
    apply is_axiom_v1.pred_3_
    exact h1_1
  case eq_1_ h1 =>
    apply is_deduct_v1.axiom_
    apply is_axiom_v1.eq_1_
  case eq_2_pred_const_ h1_name h1_n h1_xs h1_ys =>
    apply is_deduct_v1.axiom_
    apply is_axiom_v1.eq_2_pred_const_
  case eq_2_eq_ h1_x_0 h1_y_0 h1_x_1 h1_y_1 =>
    apply is_deduct_v1.axiom_
    apply is_axiom_v1.eq_2_eq_
  case gen_ h1_v h1_phi h1_1 h1_ih =>
    apply generalization
    · exact h1_ih
    · simp
  case mp_ h1_phi h1_psi h1_1 h1_2 h1_ih_1 h1_ih_2 =>
    exact is_deduct_v1.mp_ h1_phi h1_psi h1_ih_1 h1_ih_2
  case def_false_ =>
    apply is_deduct_v1.axiom_
    apply is_axiom_v1.def_false_
  case def_and_ h1_phi h1_psi =>
    apply is_deduct_v1.axiom_
    apply is_axiom_v1.def_and_
  case def_or_ h1_phi h1_psi =>
    apply is_deduct_v1.axiom_
    apply is_axiom_v1.def_or_
  case def_iff_ h1_phi h1_psi =>
    apply is_deduct_v1.axiom_
    apply is_axiom_v1.def_iff_
  case def_exists_ h1_v h1_phi =>
    apply is_deduct_v1.axiom_
    apply is_axiom_v1.def_exists_


theorem is_proof_v1_imp_is_proof_v2
  (F : Formula_)
  (h1 : is_proof_v1 F) :
  is_proof_v2 F :=
  by
  unfold is_proof_v1 at h1
  induction h1
  case axiom_ h1_phi h1_1 =>
    induction h1_1
    case prop_true_ =>
      apply is_proof_v2.prop_true_
    case prop_1_ h1_1_phi h1_1_psi =>
      apply is_proof_v2.prop_1_
    case prop_2_ h1_1_phi h1_1_psi h1_1_chi =>
      apply is_proof_v2.prop_2_
    case prop_3_ h1_1_phi h1_1_psi =>
      apply is_proof_v2.prop_3_
    case pred_1_ h1_1_v h1_1_phi h1_1_psi =>
      apply is_proof_v2.pred_1_
    case pred_2_ h1_1_v h1_1_t h1_1_phi h1_1_1 h1_1_ih_1 h1_1_ih_2 =>
      apply is_proof_v2.pred_2_ h1_1_v h1_1_t h1_1_phi h1_1_1 h1_1_ih_1 h1_1_ih_2
    case pred_3_ h1_1_v h1_1_phi h1_1_1 =>
      apply is_proof_v2.pred_3_
      exact h1_1_1
    case eq_1_ h1_1 =>
      apply is_proof_v2.eq_1_
    case eq_2_pred_const_ h1_1_name h1_1_n h1_1_xs h1_1_ys =>
      apply is_proof_v2.eq_2_pred_const_
    case eq_2_eq_ h1_1_x_0 h1_1_y_0 h1_1_x_1 h1_1_y_1 =>
      apply is_proof_v2.eq_2_eq_
    case gen_ h1_1_v h1_1_phi h1_1_1 h1_1_ih =>
      apply is_proof_v2.gen_
      exact h1_1_ih
    case def_false_ =>
      apply is_proof_v2.def_false_
    case def_and_ h1_1_phi h1_1_psi =>
      apply is_proof_v2.def_and_
    case def_or_ h1_1_phi h1_1_psi =>
      apply is_proof_v2.def_or_
    case def_iff_ h1_1_phi h1_1_psi =>
      apply is_proof_v2.def_iff_
    case def_exists_ h1_1_v h1_1_phi =>
      apply is_proof_v2.def_exists_
  case assume_ h1_phi h1_1 =>
    simp at h1_1
  case mp_ h1_phi h1_psi h1_1 h1_2 h1_ih_1 h1_ih_2 =>
    exact is_proof_v2.mp_ h1_phi h1_psi h1_ih_1 h1_ih_2


theorem T_17_10
  (P : Formula_)
  (u v : VarName_) :
  is_proof_v1 ((forall_ u (forall_ v P)).imp_ (forall_ v (forall_ u P))) :=
  by
  apply deduction_theorem_pred_v1
  simp
  apply generalization
  · apply generalization
    · apply spec_id v P
      apply spec_id u (forall_ v P)
      apply is_deduct_v1.assume_
      simp
    · simp
      simp only [var_is_free_in]
      simp
  · simp
    simp only [var_is_free_in]
    simp


theorem T_17_11
  (P Q : Formula_)
  (v : VarName_)
  (h1 : ¬ var_is_free_in v Q) :
  is_proof_v1 ((forall_ v (P.imp_ Q)).imp_ ((exists_ v P).imp_ Q)) :=
  by
  apply deduction_theorem_pred_v1
  simp
  simp only [def_exists_]
  apply is_deduct_v1.mp_ (Q.not_.imp_ (forall_ v Q.not_))
  · apply is_deduct_v1.mp_ ((forall_ v Q.not_).imp_ (forall_ v P.not_))
    · apply is_prop_deduct_v1_imp_is_deduct_v1
      SC
    · apply is_deduct_v1.mp_ (forall_ v (Q.not_.imp_ P.not_))
      · apply is_deduct_v1.axiom_
        apply is_axiom_v1.pred_1_
      · apply generalization
        · apply is_deduct_v1.mp_ (P.imp_ Q)
          · apply proof_imp_deduct_pred_v1
            apply is_prop_proof_v1_imp_is_proof_v1
            apply T_14_7
          · apply spec_id v (P.imp_ Q)
            apply is_deduct_v1.assume_
            simp
        · simp
          simp only [var_is_free_in]
          simp
  · apply is_deduct_v1.axiom_
    apply is_axiom_v1.pred_3_
    simp only [var_is_free_in]
    exact h1


-- Rule C
theorem T_17_12
  (P Q : Formula_)
  (v : VarName_)
  (Δ : Set Formula_)
  (h1 : is_deduct_v1 Δ (exists_ v P))
  (h2 : is_deduct_v1 (Δ ∪ {P}) Q)
  (h3 : ∀ (H : Formula_), H ∈ Δ → ¬ var_is_free_in v H)
  (h4 : ¬ var_is_free_in v Q) :
  is_deduct_v1 Δ Q :=
  by
  apply is_deduct_v1.mp_ (exists_ v P)
  · apply is_deduct_v1.mp_ (forall_ v (P.imp_ Q))
    · apply proof_imp_deduct_pred_v1
      exact T_17_11 P Q v h4
    · apply generalization
      · apply deduction_theorem_pred_v1
        exact h2
      · exact h3
  · exact h1

alias rule_C := T_17_12


-- Existential Elimination
theorem exists_elim
  (P Q : Formula_)
  (v t : VarName_)
  (Δ : Set Formula_)
  (h1 : is_deduct_v1 Δ (exists_ v P))
  (h2 : is_deduct_v1 (Δ ∪ {fast_replace_free_var_one_rec v t P}) Q)
  (h3 : ¬ var_occurs_in t P)
  (h4 : ¬ var_occurs_in t Q)
  (h5 : ∀ (H : Formula_), H ∈ Δ → ¬ var_is_free_in t H) : is_deduct_v1 Δ Q :=
  by
  refine' rule_C (fast_replace_free_var_one_rec v t P) Q t Δ _ h2 h5 _
  · simp only [def_exists_] at h1
    simp only [def_exists_]
    apply is_deduct_v1.mp_ (forall_ v P.not_).not_
    · apply is_deduct_v1.mp_ ((forall_ t (fast_replace_free_var_one_rec v t P.not_)).imp_ (forall_ v P.not_))
      · apply is_prop_deduct_v1_imp_is_deduct_v1
        SC
      · apply deduction_theorem_pred_v1
        apply univ_intro P.not_ v t _ h3
        · apply spec_id t
          apply is_deduct_v1.assume_
          simp
        · intro H a1
          simp at a1
          cases a1
          case _ c1 =>
            rw [c1]
            simp only [var_is_free_in]
            simp
          case _ c1 =>
            exact h5 H c1
    · exact h1
  · intro contra
    apply h4
    apply var_is_free_in_imp_var_occurs_in
    exact contra


theorem T_17_14
  (P Q : Formula_)
  (v : VarName_) :
  is_proof_v1 ((exists_ v (P.and_ Q)).imp_ ((exists_ v P).and_ (exists_ v Q))) :=
  by
  apply deduction_theorem_pred_v1
  simp
  apply rule_C (P.and_ Q) ((exists_ v P).and_ (exists_ v Q)) v
  · apply is_deduct_v1.assume_
    simp
  · apply is_deduct_v1.mp_ (exists_ v Q)
    · apply is_deduct_v1.mp_ (exists_ v P)
      · simp only [def_and_]
        apply is_prop_deduct_v1_imp_is_deduct_v1
        SC
      · apply exists_intro P v v
        · apply fast_admits_var_one_rec_self
        · simp only [fast_replace_free_var_one_rec_self]
          apply is_deduct_v1.mp_ (P.and_ Q)
          · simp only [def_and_]
            apply is_prop_deduct_v1_imp_is_deduct_v1
            SC
          · apply is_deduct_v1.assume_
            simp
    · apply exists_intro Q v v
      · apply fast_admits_var_one_rec_self
      · simp only [fast_replace_free_var_one_rec_self]
        apply is_deduct_v1.mp_ (P.and_ Q)
        · simp only [def_and_]
          apply is_prop_deduct_v1_imp_is_deduct_v1
          SC
        · apply is_deduct_v1.assume_
          simp
  · simp only [def_and_]
    simp only [def_exists_]
    simp
    simp only [var_is_free_in]
    simp
  · simp only [def_and_]
    simp only [def_exists_]
    simp only [var_is_free_in]
    simp


theorem T_18_1_left
  (P Q : Formula_)
  (v : VarName_) :
  is_proof_v1 ((forall_ v (P.iff_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q))) :=
  by
  simp only [def_iff_]
  apply deduction_theorem_pred_v1
  apply deduction_theorem_pred_v1
  simp
  apply generalization
  · apply is_deduct_v1.mp_ P
    · apply is_deduct_v1.mp_ ((P.imp_ Q).and_ (Q.imp_ P))
      · simp only [def_and_]
        apply is_prop_deduct_v1_imp_is_deduct_v1
        SC
      · apply spec_id v
        apply is_deduct_v1.assume_
        simp
    · apply spec_id v
      apply is_deduct_v1.assume_
      simp
  · simp
    simp only [var_is_free_in]
    simp


theorem T_18_1_right
  (P Q : Formula_)
  (v : VarName_) :
  is_proof_v1 ((forall_ v (P.iff_ Q)).imp_ ((forall_ v Q).imp_ (forall_ v P))) :=
  by
  simp only [def_iff_]
  apply deduction_theorem_pred_v1
  apply deduction_theorem_pred_v1
  simp
  apply generalization
  · apply is_deduct_v1.mp_ Q
    · apply is_deduct_v1.mp_ ((P.imp_ Q).and_ (Q.imp_ P))
      · simp only [def_and_]
        apply is_prop_deduct_v1_imp_is_deduct_v1
        SC
      · apply spec_id v
        apply is_deduct_v1.assume_
        simp
    · apply spec_id v
      apply is_deduct_v1.assume_
      simp
  · simp
    simp only [var_is_free_in]
    simp


theorem T_18_1
  (P Q : Formula_)
  (v : VarName_) :
  is_proof_v1 ((forall_ v (P.iff_ Q)).imp_ ((forall_ v P).iff_ (forall_ v Q))) :=
  by
  apply is_deduct_v1.mp_ ((forall_ v (P.iff_ Q)).imp_ ((forall_ v Q).imp_ (forall_ v P)))
  · apply is_deduct_v1.mp_ ((forall_ v (P.iff_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q)))
    · simp only [def_iff_]
      simp only [def_and_]
      apply is_prop_deduct_v1_imp_is_deduct_v1
      SC
    · apply T_18_1_left
  · apply T_18_1_right


theorem Forall_spec_id
  (xs : List VarName_)
  (P : Formula_) :
  is_proof_v1 ((Forall_ xs P).imp_ P) :=
  by
  induction xs
  case nil =>
    simp only [Forall_]
    apply is_prop_deduct_v1_imp_is_deduct_v1
    apply prop_id
  case cons xs_hd xs_tl xs_ih =>
    simp only [Forall_]
    apply deduction_theorem_pred_v1
    simp
    apply is_deduct_v1.mp_ (Forall_ xs_tl P)
    · apply proof_imp_deduct_pred_v1
      exact xs_ih
    · apply spec_id xs_hd
      apply is_deduct_v1.assume_
      simp
      rfl


theorem Forall_spec_id'
  (xs : List VarName_)
  (P : Formula_)
  (Δ : Set Formula_)
  (h1 : is_deduct_v1 Δ (Forall_ xs P)) :
  is_deduct_v1 Δ P :=
  by
  induction xs
  case nil =>
    simp only [Forall_] at h1
    simp at h1
    exact h1
  case cons xs_hd xs_tl xs_ih =>
    simp only [Forall_] at h1
    simp at h1
    apply xs_ih
    simp only [Forall_]
    apply spec_id xs_hd
    exact h1


theorem Forall_var_is_bound_in
  (P : Formula_)
  (xs : List VarName_)
  (x : VarName_) :
  var_is_bound_in x (Forall_ xs P) ↔ x ∈ xs ∨ var_is_bound_in x P :=
  by
  simp only [Formula_.Forall_]
  induction xs
  case nil =>
    simp
  case cons xs_hd xs_tl xs_ih =>
    simp
    simp only [var_is_bound_in]
    simp only [xs_ih]
    tauto


theorem Forall_var_is_free_in
  (P : Formula_)
  (xs : List VarName_)
  (x : VarName_) :
  var_is_free_in x (Forall_ xs P) ↔ x ∉ xs ∧ var_is_free_in x P :=
  by
  simp only [Formula_.Forall_]
  induction xs
  case nil =>
    simp
  case cons xs_hd xs_tl xs_ih =>
    simp
    simp only [var_is_free_in]
    simp only [xs_ih]
    tauto


-- The equivalence theorem
theorem T_18_2
  (U V : Formula_)
  (P_U P_V : Formula_)
  (l : List VarName_)
  (h1 : is_repl_of_formula_in_formula U V P_U P_V)
  (h2 : ∀ (v : VarName_), (var_is_free_in v U ∨ var_is_free_in v V) ∧ var_is_bound_in v P_U → v ∈ l) :
  is_proof_v1 ((Forall_ l (U.iff_ V)).imp_ (P_U.iff_ P_V)) :=
  by
  induction h1
  case same_ h1_P h1_P' h1_1 =>
    subst h1_1
    simp only [def_iff_]
    simp only [def_and_]
    apply is_prop_deduct_v1_imp_is_deduct_v1
    SC
  case diff_ h1_P h1_P' h1_1 h1_2 =>
    rw [h1_1]
    rw [h1_2]
    apply Forall_spec_id
  case not_ h1_P h1_P' h1_1 h1_ih =>
    simp only [var_is_bound_in] at h2
    apply is_deduct_v1.mp_ ((Forall_ l (U.iff_ V)).imp_ (h1_P.iff_ h1_P'))
    · simp only [def_iff_]
      simp only [def_and_]
      apply is_prop_deduct_v1_imp_is_deduct_v1
      SC
    · exact h1_ih h2
  case imp_ h1_P h1_Q h1_P' h1_Q' h1_1 h1_2 h1_ih_1 h1_ih_2 =>
    simp only [var_is_bound_in] at h2
    apply is_deduct_v1.mp_ ((Forall_ l (U.iff_ V)).imp_ (h1_P.iff_ h1_P'))
    · apply is_deduct_v1.mp_ ((Forall_ l (U.iff_ V)).imp_ (h1_Q.iff_ h1_Q'))
      · simp only [def_iff_]
        simp only [def_and_]
        apply is_prop_deduct_v1_imp_is_deduct_v1
        SC
      · apply h1_ih_2
        intro v a2
        apply h2 v
        tauto
    · apply h1_ih_1
      intro v a1
      apply h2 v
      obtain ⟨a1_left, a1_right⟩ := a1
      constructor
      · exact a1_left
      · left
        exact a1_right
  case forall_ h1_u h1_v h1_P_U h1_P_V h1_ih_1 h1_ih_2 h1_ih_3 =>
    rw [h1_ih_1]

    simp only [var_is_bound_in] at h2
    simp at h2

    apply deduction_theorem_pred_v1
    simp
    apply is_deduct_v1.mp_ (forall_ h1_v (h1_P_U.iff_ h1_P_V))
    · apply proof_imp_deduct_pred_v1
      apply T_18_1
    · apply generalization
      · apply is_deduct_v1.mp_ (Forall_ l (U.iff_ V))
        · apply proof_imp_deduct_pred_v1
          apply h1_ih_3
          intro v a1
          obtain ⟨a1_left, a1_right⟩ := a1
          apply h2 v a1_left
          right
          apply a1_right
        · apply is_deduct_v1.assume_
          simp
      · intro H a1
        simp at a1
        rw [a1]
        simp only [Forall_var_is_free_in]
        simp only [def_iff_]
        simp only [def_and_]
        simp only [var_is_free_in]
        simp
        contrapose
        simp
        intro a2
        apply h2
        simp_all
        · tauto
        · left
          symm
          exact h1_ih_1
  all_goals
    sorry


theorem C_18_3
  (U V : Formula_)
  (P_U P_V : Formula_)
  (h1 : is_repl_of_formula_in_formula U V P_U P_V)
  (h2 : is_proof_v1 (U.iff_ V)) :
  is_proof_v1 (P_U.iff_ P_V) :=
  by
  apply is_deduct_v1.mp_ (Forall_ ((U.free_var_set ∪ V.free_var_set) ∩ P_U.bound_var_set).toList (U.iff_ V))
  · apply T_18_2 U V P_U P_V ((U.free_var_set ∪ V.free_var_set) ∩ P_U.bound_var_set).toList h1
    intro v a1
    simp
    simp only [var_is_free_in_iff_mem_free_var_set] at a1
    simp only [var_is_bound_in_iff_mem_bound_var_set] at a1
    exact a1
  · simp only [Formula_.Forall_]
    induction ((U.free_var_set ∪ V.free_var_set) ∩ P_U.bound_var_set).toList
    case _ =>
      simp
      exact h2
    case _ hd tl ih =>
      simp
      apply generalization
      · exact ih
      · simp


-- The replacement theorem
theorem C_18_4
  (U V : Formula_)
  (P_U P_V : Formula_)
  (Δ : Set Formula_)
  (h1 : is_repl_of_formula_in_formula U V P_U P_V)
  (h2 : is_proof_v1 (U.iff_ V))
  (h3 : is_deduct_v1 Δ P_U) :
  is_deduct_v1 Δ P_V :=
  by
  apply is_deduct_v1.mp_ P_U
  · apply is_deduct_v1.mp_ (P_U.iff_ P_V)
    · simp only [def_iff_]
      simp only [def_and_]
      apply is_prop_deduct_v1_imp_is_deduct_v1
      SC
    · apply proof_imp_deduct_pred_v1
      exact C_18_3 U V P_U P_V h1 h2
  · exact h3


theorem T_18_5
  (P : Formula_)
  (v : VarName_) :
  is_proof_v1 ((forall_ v P).iff_ (exists_ v P.not_).not_) :=
  by
  simp only [def_exists_]
  apply C_18_4 P P.not_.not_ ((forall_ v P).iff_ (forall_ v P).not_.not_)
  · simp only [def_iff_]
    simp only [def_and_]
    apply is_repl_of_formula_in_formula.not_
    apply is_repl_of_formula_in_formula.imp_
    · apply is_repl_of_formula_in_formula.imp_
      · apply is_repl_of_formula_in_formula.same_
        rfl
      · apply is_repl_of_formula_in_formula.not_
        apply is_repl_of_formula_in_formula.not_
        apply is_repl_of_formula_in_formula.forall_
        · rfl
        · apply is_repl_of_formula_in_formula.diff_
          · rfl
          · rfl
    · apply is_repl_of_formula_in_formula.not_
      apply is_repl_of_formula_in_formula.imp_
      · apply is_repl_of_formula_in_formula.not_
        apply is_repl_of_formula_in_formula.not_
        apply is_repl_of_formula_in_formula.forall_
        · rfl
        · apply is_repl_of_formula_in_formula.diff_
          · rfl
          · rfl
      · apply is_repl_of_formula_in_formula.same_
        rfl
  · simp only [def_iff_]
    simp only [def_and_]
    apply is_prop_deduct_v1_imp_is_deduct_v1
    SC
  · simp only [def_iff_]
    simp only [def_and_]
    apply is_prop_deduct_v1_imp_is_deduct_v1
    SC


theorem T_18_6
  (P_u P_v : Formula_)
  (u v : VarName_)
  (h1 : similar P_u P_v u v) :
  is_proof_v1 ((forall_ u P_u).iff_ (forall_ v P_v)) :=
  by
  simp only [similar] at h1
  obtain ⟨h1_left, ⟨h1_right_left, ⟨h1_right_right_left, ⟨ h1_right_right_right_left, ⟨h1_right_right_right_right_left, h1_right_right_right_right_right⟩⟩⟩⟩⟩ := h1

  apply is_deduct_v1.mp_ ((forall_ v P_v).imp_ (forall_ u P_u))
  · apply is_deduct_v1.mp_ ((forall_ u P_u).imp_ (forall_ v P_v))
    · simp only [def_iff_]
      simp only [def_and_]
      apply is_prop_deduct_v1_imp_is_deduct_v1
      SC
    · apply deduction_theorem_pred_v1
      simp
      apply generalization
      · rw [h1_right_right_right_right_left]
        apply spec
        · apply is_deduct_v1.assume_
          simp
        · exact h1_right_right_left
      · intro H a1
        simp at a1
        subst a1
        simp only [var_is_free_in]
        simp
        intro _
        exact h1_left
  · apply deduction_theorem_pred_v1
    simp
    apply generalization
    · rw [h1_right_right_right_right_right]
      apply spec
      · apply is_deduct_v1.assume_
        simp
      · exact h1_right_right_right_left
    · intro H a1
      simp at a1
      rw [a1]
      simp only [var_is_free_in]
      simp
      intro _
      exact h1_right_left


-- Change of bound variable
theorem T_18_7
  (P_u P_v Q Q' : Formula_)
  (u v : VarName_)
  (Δ : Set Formula_)
  (h1 : is_deduct_v1 Δ Q)
  (h2 : is_repl_of_formula_in_formula (forall_ u P_u) (forall_ v P_v) Q Q')
  (h3 : similar P_u P_v u v) :
  is_deduct_v1 Δ Q' :=
  by
  apply C_18_4 (forall_ u P_u) (forall_ v P_v) Q Q' Δ h2
  · apply T_18_6 P_u P_v u v h3
  · exact h1


theorem similar_not
  (P_u P_v : Formula_)
  (u v : VarName_)
  (h1 : similar P_u P_v u v) :
  similar P_u.not_ P_v.not_ u v :=
  by
  simp only [similar] at *
  simp only [var_is_free_in] at *
  simp only [fast_admits_var_one_rec] at *
  simp only [fast_admits_var_one_rec_aux] at *
  simp only [fast_replace_free_var_one_rec] at *
  tauto


theorem T_18_8
  (P_u P_v : Formula_)
  (u v : VarName_)
  (h1 : similar P_u P_v u v) :
  is_proof_v1 ((exists_ u P_u).iff_ (exists_ v P_v)) :=
  by
  simp only [def_exists_]
  apply is_deduct_v1.mp_ ((forall_ u P_u.not_).iff_ (forall_ v P_v.not_))
  · simp only [def_iff_]
    simp only [def_and_]
    apply is_prop_deduct_v1_imp_is_deduct_v1
    SC
  · apply T_18_6
    exact similar_not P_u P_v u v h1


theorem T18_9
  (Q Q' : Formula_)
  (P_u P_v : Formula_)
  (u v : VarName_)
  (Δ : Set Formula_)
  (h1 : is_deduct_v1 Δ Q)
  (h2 : is_repl_of_formula_in_formula (exists_ u P_u) (exists_ v P_v) Q Q')
  (h3 : similar P_u P_v u v) :
  is_deduct_v1 Δ Q' :=
  by
  apply C_18_4 (exists_ u P_u) (exists_ v P_v) Q Q' Δ h2
  · exact T_18_8 P_u P_v u v h3
  · exact h1


theorem T_19_1
  (P : Formula_)
  (v : VarName_)
  (h1 : ¬ var_is_free_in v P) :
  is_proof_v1 ((forall_ v P).iff_ P) :=
  by
  apply is_deduct_v1.mp_ ((forall_ v P).imp_ P)
  · apply is_deduct_v1.mp_ (P.imp_ (forall_ v P))
    · simp only [def_iff_]
      simp only [def_and_]
      apply is_prop_deduct_v1_imp_is_deduct_v1
      SC
    · apply is_deduct_v1.axiom_
      exact is_axiom_v1.pred_3_ v P h1
  · apply is_deduct_v1.axiom_
    apply is_axiom_v1.pred_2_ v v P P
    · apply fast_admits_var_one_rec_self
    · apply fast_replace_free_var_one_rec_self


theorem T_19_2
  (P : Formula_)
  (u v : VarName_) :
  is_proof_v1 ((forall_ u (forall_ v P)).iff_ (forall_ v (forall_ u P))) :=
  by
  apply is_deduct_v1.mp_ ((forall_ u (forall_ v P)).imp_ (forall_ v (forall_ u P)))
  · apply is_deduct_v1.mp_ ((forall_ v (forall_ u P)).imp_ (forall_ u (forall_ v P)))
    · simp only [def_iff_]
      simp only [def_and_]
      apply is_prop_deduct_v1_imp_is_deduct_v1
      SC
    · apply T_17_10
  · apply T_17_10


theorem T_19_3
  (P : Formula_)
  (v : VarName_) :
  is_proof_v1 ((forall_ v P.not_).iff_ (exists_ v P).not_) :=
  by
  simp only [def_exists_]
  simp only [def_iff_]
  simp only [def_and_]
  apply is_prop_deduct_v1_imp_is_deduct_v1
  SC


theorem T_19_4
  (P : Formula_)
  (u v : VarName_) :
  is_proof_v1 ((exists_ u (forall_ v P)).imp_ (forall_ v (exists_ u P))) :=
  by
  apply deduction_theorem_pred_v1
  simp
  apply generalization
  · apply rule_C (forall_ v P) (exists_ u P) u {exists_ u (forall_ v P)}
    · apply is_deduct_v1.assume_
      simp
    · apply exists_intro P u u
      · apply fast_admits_var_one_rec_self
      · simp only [fast_replace_free_var_one_rec_self]
        apply spec_id v
        apply is_deduct_v1.assume_
        simp
    · simp
      simp only [def_exists_]
      simp only [var_is_free_in]
      simp
    · simp only [def_exists_]
      simp only [var_is_free_in]
      simp
  · simp
    simp only [def_exists_]
    simp only [var_is_free_in]
    simp


theorem T_19_5
  (P Q : Formula_)
  (v : VarName_)
  (h1 : ¬ var_is_free_in v P) :
  is_proof_v1 ((forall_ v (P.iff_ Q)).imp_ (P.iff_ (forall_ v Q))) :=
  by
  apply is_deduct_v1.mp_ ((forall_ v P).iff_ P)
  · apply is_deduct_v1.mp_ ((forall_ v (P.iff_ Q)).imp_ ((forall_ v P).iff_ (forall_ v Q)))
    · simp only [def_iff_]
      simp only [def_and_]
      apply is_prop_deduct_v1_imp_is_deduct_v1
      SC
    · exact T_18_1 P Q v
  · exact T_19_1 P v h1


theorem T_19_6_left
  (P Q : Formula_)
  (v : VarName_) :
  is_proof_v1 ((forall_ v (P.iff_ Q)).imp_ ((exists_ v P).imp_ (exists_ v Q))) :=
  by
  apply deduction_theorem_pred_v1
  apply deduction_theorem_pred_v1
  simp
  apply rule_C P (exists_ v Q) v {exists_ v P, forall_ v (P.iff_ Q)}
  · apply is_deduct_v1.assume_
    simp
  · apply exists_intro Q v v
    · apply fast_admits_var_one_rec_self
    · simp only [fast_replace_free_var_one_rec_self]
      apply is_deduct_v1.mp_ P
      · apply is_deduct_v1.mp_ (P.iff_ Q)
        · simp only [def_iff_]
          simp only [def_and_]
          apply is_prop_deduct_v1_imp_is_deduct_v1
          SC
        · apply spec_id v
          apply is_deduct_v1.assume_
          simp
      · apply is_deduct_v1.assume_
        simp
  · simp only [def_exists_]
    simp
    simp only [var_is_free_in]
    simp
  · simp only [def_exists_]
    simp only [var_is_free_in]
    simp


theorem T_19_6_right
  (P Q : Formula_)
  (v : VarName_) :
  is_proof_v1 ((forall_ v (P.iff_ Q)).imp_ ((exists_ v Q).imp_ (exists_ v P))) :=
  by
  apply deduction_theorem_pred_v1
  simp
  apply is_deduct_v1.mp_ (forall_ v (Q.iff_ P))
  · apply proof_imp_deduct_pred_v1
    apply T_19_6_left Q P v
  · apply generalization
    · apply is_deduct_v1.mp_ (P.iff_ Q)
      · simp only [def_iff_]
        simp only [def_and_]
        apply is_prop_deduct_v1_imp_is_deduct_v1
        SC
      · apply spec_id v
        apply is_deduct_v1.assume_
        simp
    · simp
      simp only [var_is_free_in]
      simp


theorem T_19_6
  (P Q : Formula_)
  (v : VarName_) :
  is_proof_v1 ((forall_ v (P.iff_ Q)).imp_ ((exists_ v P).iff_ (exists_ v Q))) :=
  by
  apply is_deduct_v1.mp_ ((forall_ v (P.iff_ Q)).imp_ ((exists_ v P).imp_ (exists_ v Q)))
  · apply is_deduct_v1.mp_ ((forall_ v (P.iff_ Q)).imp_ ((exists_ v Q).imp_ (exists_ v P)))
    · simp only [def_exists_]
      simp only [def_iff_]
      simp only [def_and_]
      apply is_prop_deduct_v1_imp_is_deduct_v1
      SC
    · apply T_19_6_right
  · apply T_19_6_left


theorem T_19_TS_21_left
  (P Q : Formula_)
  (v : VarName_)
  (h1 : ¬ var_is_free_in v P) :
  is_proof_v1 ((forall_ v (P.imp_ Q)).imp_ (P.imp_ (forall_ v Q))) :=
  by
  apply C_18_4 (forall_ v P) P ((forall_ v (P.imp_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q)))
  · apply is_repl_of_formula_in_formula.imp_
    · apply is_repl_of_formula_in_formula.same_
      rfl
    · apply is_repl_of_formula_in_formula.imp_
      · apply is_repl_of_formula_in_formula.diff_
        · rfl
        · rfl
      · apply is_repl_of_formula_in_formula.same_
        rfl
  · exact T_19_1 P v h1
  · apply is_deduct_v1.axiom_
    apply is_axiom_v1.pred_1_


theorem T_19_TS_21_right
  (P Q : Formula_)
  (v : VarName_)
  (h1 : ¬ var_is_free_in v P) :
  is_proof_v1 ((P.imp_ (forall_ v Q)).imp_ (forall_ v (P.imp_ Q))) :=
  by
  apply deduction_theorem_pred_v1
  simp
  apply generalization
  · apply deduction_theorem_pred_v1
    apply spec_id v
    apply is_deduct_v1.mp_ P
    · apply is_deduct_v1.assume_
      simp
    · apply is_deduct_v1.assume_
      simp
  · intro H a1
    simp at a1
    subst a1
    simp only [var_is_free_in]
    simp
    exact h1


theorem T_19_TS_21
  (P Q : Formula_)
  (v : VarName_)
  (h1 : ¬ var_is_free_in v P) :
  is_proof_v1 ((forall_ v (P.imp_ Q)).iff_ (P.imp_ (forall_ v Q))) :=
  by
  apply is_deduct_v1.mp_ ((forall_ v (P.imp_ Q)).imp_ (P.imp_ (forall_ v Q)))
  · apply is_deduct_v1.mp_ ((P.imp_ (forall_ v Q)).imp_ (forall_ v (P.imp_ Q)))
    · simp only [def_iff_]
      simp only [def_and_]
      apply is_prop_deduct_v1_imp_is_deduct_v1
      SC
    · exact T_19_TS_21_right P Q v h1
  · exact T_19_TS_21_left P Q v h1


theorem T_21_1
  (x y : VarName_) :
  is_proof_v1 (forall_ x (forall_ y ((eq_ x y).imp_ (eq_ y x)))) :=
  by
  apply generalization
  · apply generalization
    · apply is_deduct_v1.mp_ (eq_ y y)
      · apply is_deduct_v1.mp_ (((eq_ y y).and_ (eq_ x y)).imp_ ((eq_ y x).iff_ (eq_ y y)))
        · simp only [def_iff_]
          simp only [def_and_]
          apply is_prop_deduct_v1_imp_is_deduct_v1
          SC
        · apply spec_id y
          apply spec_id y
          apply spec_id x
          apply spec_id y
          apply is_deduct_v1.axiom_
          exact is_axiom_v1.eq_2_eq_ y x y y
      · apply spec_id y
        apply is_deduct_v1.axiom_
        exact is_axiom_v1.eq_1_ y
    · intro H a1
      simp at a1
  · intro H a1
    simp at a1


theorem T_21_2
  (x y z : VarName_) :
  is_proof_v1 (forall_ x (forall_ y (forall_ z (((eq_ x y).and_ (eq_ y z)).imp_ (eq_ x z))))) :=
  by
  apply generalization
  · apply generalization
    · apply generalization
      · apply is_deduct_v1.mp_ (eq_ z z)
        · apply is_deduct_v1.mp_ (((eq_ x y).and_ (eq_ z z)).imp_ ((eq_ x z).iff_ (eq_ y z)))
          · simp only [def_iff_]
            simp only [def_and_]
            apply is_prop_deduct_v1_imp_is_deduct_v1
            SC
          · apply spec_id z
            apply spec_id y
            apply spec_id z
            apply spec_id x
            apply is_deduct_v1.axiom_
            exact is_axiom_v1.eq_2_eq_ x z y z
        · apply spec_id z
          apply is_deduct_v1.axiom_
          exact is_axiom_v1.eq_1_ z
      · intro H a1
        simp at a1
    · intro H a1
      simp at a1
  · intro H a1
    simp at a1


theorem T_21_8
  (P_r P_s : Formula_)
  (r s : VarName_)
  (h1 : is_repl_of_var_in_formula_fin r s P_r P_s)
  (h2 : ¬ var_is_bound_in r P_r)
  (h3 : ¬ var_is_bound_in s P_r) :
  is_proof_v1 ((eq_ r s).imp_ (P_r.iff_ P_s)) :=
  by
  induction h1
  case true_ =>
    simp only [def_iff_]
    simp only [def_and_]
    apply is_prop_deduct_v1_imp_is_deduct_v1
    SC
  case pred_const_ name n args_u args_v h1_1 =>
    apply is_deduct_v1.mp_ ((eq_ r s).imp_ ((pred_const_ name (List.ofFn args_u)).iff_ (pred_const_ name (List.ofFn args_v))))
    · apply is_prop_deduct_v1_imp_is_deduct_v1
      SC
    · apply is_deduct_v1.mp_ ((eq_ r s).imp_ (And_ (List.ofFn fun (i : Fin n) => eq_ (args_u i) (args_v i))))
      · apply is_deduct_v1.mp_ ((And_ (List.ofFn fun (i : Fin n) => eq_ (args_u i) (args_v i))).imp_ ((pred_const_ name (List.ofFn args_u)).iff_ (pred_const_ name (List.ofFn args_v))))
        · simp only [def_iff_]
          simp only [def_and_]
          apply is_prop_deduct_v1_imp_is_deduct_v1
          SC
        · apply Forall_spec_id' (List.ofFn args_v)
          apply Forall_spec_id' (List.ofFn args_u)
          apply is_deduct_v1.axiom_
          exact is_axiom_v1.eq_2_pred_const_ name n args_u args_v
      · clear h2
        clear h3
        simp only [And_]
        induction n
        case _ =>
          simp
          apply is_prop_deduct_v1_imp_is_deduct_v1
          SC
        case _ n ih =>
          simp
          apply is_deduct_v1.mp_ ((eq_ r s).imp_ (List.foldr and_ true_ (List.ofFn fun (i : Fin n) => eq_ (args_u i.succ) (args_v i.succ))))
          · apply is_deduct_v1.mp_ ((eq_ r s).imp_ (eq_ (args_u 0) (args_v 0)))
            · simp only [def_and_]
              apply is_prop_deduct_v1_imp_is_deduct_v1
              SC
            · specialize h1_1 0
              cases h1_1
              case _ c1 =>
                apply is_deduct_v1.mp_ (eq_ (args_u 0) (args_v 0))
                · apply is_prop_deduct_v1_imp_is_deduct_v1
                  SC
                · simp only [c1]
                  apply spec_id (args_v 0)
                  apply is_deduct_v1.axiom_
                  apply is_axiom_v1.eq_1_
              case _ c1 =>
                obtain ⟨c1_left, c1_right⟩ := c1
                subst c1_left
                subst c1_right
                apply is_prop_deduct_v1_imp_is_deduct_v1
                SC
          · apply ih
            intro i
            apply h1_1
  case not_ P_u P_v h1_1 h1_ih =>
    simp only [var_is_bound_in] at h2
    simp only [var_is_bound_in] at h3
    specialize h1_ih h2 h3
    apply is_deduct_v1.mp_ ((eq_ r s).imp_ (P_u.iff_ P_v))
    · simp only [def_iff_]
      simp only [def_and_]
      apply is_prop_deduct_v1_imp_is_deduct_v1
      SC
    · exact h1_ih
  case imp_ P_u Q_u P_v Q_v h1_1 h1_2 h1_ih_1
    h1_ih_2 =>
    simp only [var_is_bound_in] at h2
    simp at h2
    obtain ⟨h2_left, h2_right⟩ := h2
    simp only [var_is_bound_in] at h3
    simp at h3
    obtain ⟨h3_left, h3_right⟩ := h3
    specialize h1_ih_1 h2_left h3_left
    specialize h1_ih_2 h2_right h3_right
    apply is_deduct_v1.mp_ ((eq_ r s).imp_ (Q_u.iff_ Q_v))
    · apply is_deduct_v1.mp_ ((eq_ r s).imp_ (P_u.iff_ P_v))
      · simp only [def_iff_]
        simp only [def_and_]
        apply is_prop_deduct_v1_imp_is_deduct_v1
        SC
      · exact h1_ih_1
    · exact h1_ih_2
  case forall_ x P_u P_v h1_1 h1_ih =>
    simp only [var_is_bound_in] at h2
    simp at h2
    obtain ⟨h2_left, h2_right⟩ := h2

    simp only [var_is_bound_in] at h3
    simp at h3
    obtain ⟨h3_left, h3_right⟩ := h3
    apply deduction_theorem_pred_v1
    simp
    apply is_deduct_v1.mp_ (forall_ x (P_u.iff_ P_v))
    · apply proof_imp_deduct_pred_v1
      apply T_18_1
    · apply is_deduct_v1.mp_ (eq_ r s)
      · apply proof_imp_deduct_pred_v1
        apply is_deduct_v1.mp_ (forall_ x ((eq_ r s).imp_ (P_u.iff_ P_v)))
        · apply T_19_TS_21_left
          · simp only [var_is_free_in]
            simp
            constructor
            · simp only [ne_comm]
              exact h2_left
            · simp only [ne_comm]
              exact h3_left
        · apply generalization
          · exact h1_ih h2_right h3_right
          · intro H a1
            simp at a1
      · apply is_deduct_v1.assume_
        simp
  all_goals
    sorry


--#lint
