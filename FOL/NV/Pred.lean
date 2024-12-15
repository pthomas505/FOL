import FOL.NV.Prop


set_option autoImplicit false


open Formula_

open FOL.NV.Sub.Var.One.Rec


axiom def_false_ : false_ = not_ true_

/--
  phi ∨ psi := ¬ phi → psi
-/
axiom def_or_ (phi psi : Formula_) : or_ phi psi = (not_ phi).imp_ psi

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


def ProofEquiv (P Q : Formula_) : Prop :=
  is_proof_v1 (P.iff_ Q)


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


def Similar
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


theorem specId
  (v : VarName_)
  (P : Formula_)
  (Δ : Set Formula_)
  (h1 : is_deduct_v1 Δ (forall_ v P)) :
  is_deduct_v1 Δ P :=
  by
  apply is_deduct_v1.mp_ (forall_ v P)
  · apply is_deduct_v1.axiom_
    apply is_axiom_v1.pred_2_ v v P
    · exact fast_admits_var_one_rec_self P v
    · exact fast_replace_free_var_one_rec_self P v
  · exact h1

alias forall_elim_id := specId


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
  · SC
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
  · apply proof_imp_deduct
    apply T_17_3
    exact h1
  · exact h2

alias exists_intro := T_17_4


theorem existsIntroId
  (P : Formula_)
  (v : VarName_)
  (Δ : Set Formula_)
  (h1 : is_deduct_v1 Δ P) :
  is_deduct_v1 Δ (exists_ v P) :=
  by
  apply T_17_4 P v v Δ
  · exact fast_admits_var_one_rec_self P v
  · simp only [fast_replace_free_var_one_rec_self]
    exact h1


theorem T_17_6
  (P : Formula_)
  (v : VarName_) :
  is_proof_v1 ((forall_ v P).imp_ (exists_ v P)) :=
  by
  apply deduction_theorem
  simp
  apply existsIntroId
  apply specId v
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
theorem univIntro
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
  · apply proof_imp_deduct
    apply deduction_theorem
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


theorem isProofAltImpIsDeduct
  (F : Formula_)
  (h1 : is_proof_v2 F) :
  is_deduct_v1 ∅ F :=
  by
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


theorem isDeductImpIsProofAlt
  (F : Formula_)
  (h1 : is_deduct_v1 ∅ F) :
  is_proof_v2 F :=
  by
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
  apply deduction_theorem
  simp
  apply generalization
  · apply generalization
    · apply specId v P
      apply specId u (forall_ v P)
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
  apply deduction_theorem
  simp
  simp only [def_exists_]
  -- simp only [exists_]
  apply is_deduct_v1.mp_ (Q.not_.imp_ (forall_ v Q.not_))
  · apply is_deduct_v1.mp_ ((forall_ v Q.not_).imp_ (forall_ v P.not_))
    · SC
    · apply is_deduct_v1.mp_ (forall_ v (Q.not_.imp_ P.not_))
      · apply is_deduct_v1.axiom_
        apply is_axiom_v1.pred_1_
      · apply generalization
        · apply is_deduct_v1.mp_ (P.imp_ Q)
          · apply proof_imp_deduct
            apply T_14_7
          · apply specId v (P.imp_ Q)
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
    · apply proof_imp_deduct
      exact T_17_11 P Q v h4
    · apply generalization
      · apply deduction_theorem
        exact h2
      · exact h3
  · exact h1

alias rule_C := T_17_12


-- Existential Elimination
theorem existsElim
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
    -- simp only [exists_] at h1
    simp only [def_exists_]
    -- simp only [exists_]
    apply is_deduct_v1.mp_ (forall_ v P.not_).not_
    · apply is_deduct_v1.mp_ ((forall_ t (fast_replace_free_var_one_rec v t P.not_)).imp_ (forall_ v P.not_))
      · SC
      · apply deduction_theorem
        apply univIntro P.not_ v t _ h3
        · apply specId t
          apply is_deduct_v1.assume_
          simp
        · intro H a1
          simp at a1
          cases a1
          case _ c1 =>
            subst c1
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
  apply deduction_theorem
  simp
  apply rule_C (P.and_ Q) ((exists_ v P).and_ (exists_ v Q)) v
  · apply is_deduct_v1.assume_
    simp
  · apply is_deduct_v1.mp_ (exists_ v Q)
    · apply is_deduct_v1.mp_ (exists_ v P)
      · simp only [def_and_]
        -- simp only [formula.and_]
        SC
      · apply exists_intro P v v
        · apply fast_admits_var_one_rec_self
        · simp only [fast_replace_free_var_one_rec_self]
          apply is_deduct_v1.mp_ (P.and_ Q)
          · simp only [def_and_]
            -- simp only [formula.and_]
            SC
          · apply is_deduct_v1.assume_
            simp
    · apply exists_intro Q v v
      · apply fast_admits_var_one_rec_self
      · simp only [fast_replace_free_var_one_rec_self]
        apply is_deduct_v1.mp_ (P.and_ Q)
        · simp only [def_and_]
          -- simp only [formula.and_]
          SC
        · apply is_deduct_v1.assume_
          simp
  · simp only [def_and_]
    -- simp only [and_]
    simp only [def_exists_]
    -- simp only [exists_]
    simp
    simp only [var_is_free_in]
    simp
  · simp only [def_and_]
    -- simp only [and_]
    simp only [def_exists_]
    -- simp only [exists_]
    simp only [var_is_free_in]
    simp


theorem T_18_1_left
  (P Q : Formula_)
  (v : VarName_) :
  is_proof_v1 ((forall_ v (P.iff_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q))) :=
  by
  simp only [def_iff_]
  -- simp only [iff_]
  apply deduction_theorem
  apply deduction_theorem
  simp
  apply generalization
  · apply is_deduct_v1.mp_ P
    · apply is_deduct_v1.mp_ ((P.imp_ Q).and_ (Q.imp_ P))
      · simp only [def_and_]
        -- simp only [formula.and_]
        SC
      · apply specId v
        apply is_deduct_v1.assume_
        simp
    · apply specId v
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
  -- simp only [iff_]
  apply deduction_theorem
  apply deduction_theorem
  simp
  apply generalization
  · apply is_deduct_v1.mp_ Q
    · apply is_deduct_v1.mp_ ((P.imp_ Q).and_ (Q.imp_ P))
      · simp only [def_and_]
        -- simp only [formula.and_]
        SC
      · apply specId v
        apply is_deduct_v1.assume_
        simp
    · apply specId v
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
      -- simp only [formula.iff_]
      simp only [def_and_]
      -- simp only [formula.and_]
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
    apply prop_id
  case cons xs_hd xs_tl xs_ih =>
    simp only [Forall_]
    apply deduction_theorem
    simp
    apply is_deduct_v1.mp_ (Forall_ xs_tl P)
    apply proof_imp_deduct
    exact xs_ih
    apply specId xs_hd
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
    apply specId xs_hd
    exact h1


theorem Forall_isBoundIn
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


theorem Forall_isFreeIn
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
  (h1 : IsReplOfFormulaInFormula U V P_U P_V)
  (h2 : ∀ (v : VarName_), (var_is_free_in v U ∨ var_is_free_in v V) ∧ var_is_bound_in v P_U → v ∈ l) :
  is_proof_v1 ((Forall_ l (U.iff_ V)).imp_ (P_U.iff_ P_V)) :=
  by
  induction h1
  case same_ h1_P h1_P' h1_1 =>
    subst h1_1
    simp only [def_iff_]
    -- simp only [formula.iff_]
    simp only [def_and_]
    -- simp only [formula.and_]
    SC
  case diff_ h1_P h1_P' h1_1 h1_2 =>
    subst h1_1
    subst h1_2
    apply Forall_spec_id
  case not_ h1_P h1_P' h1_1 h1_ih =>
    simp only [var_is_bound_in] at h2
    apply is_deduct_v1.mp_ ((Forall_ l (U.iff_ V)).imp_ (h1_P.iff_ h1_P'))
    · simp only [def_iff_]
      -- simp only [formula.iff_]
      simp only [def_and_]
      -- simp only [formula.and_]
      SC
    · exact h1_ih h2
  case imp_ h1_P h1_Q h1_P' h1_Q' h1_1 h1_2 h1_ih_1 h1_ih_2 =>
    simp only [var_is_bound_in] at h2
    apply is_deduct_v1.mp_ ((Forall_ l (U.iff_ V)).imp_ (h1_P.iff_ h1_P'))
    · apply is_deduct_v1.mp_ ((Forall_ l (U.iff_ V)).imp_ (h1_Q.iff_ h1_Q'))
      · simp only [def_iff_]
        -- simp only [formula.iff_]
        simp only [def_and_]
        -- simp only [formula.and_]
        SC
      · apply h1_ih_2
        intro v a2
        apply h2 v
        tauto
    · apply h1_ih_1
      intro v a1
      apply h2 v
      cases a1
      case _ a1_left a1_right =>
        constructor
        · exact a1_left
        · left
          exact a1_right
  case forall_ h1_x h1_P h1_P' h1_1 h1_ih =>
    simp only [var_is_bound_in] at h2
    simp at h2
    apply deduction_theorem
    simp
    apply is_deduct_v1.mp_ (forall_ h1_x (h1_P.iff_ h1_P'))
    · apply proof_imp_deduct
      apply T_18_1
    · apply generalization
      · apply is_deduct_v1.mp_ (Forall_ l (U.iff_ V))
        · apply proof_imp_deduct
          apply h1_ih
          intro v a1
          cases a1
          case _ a1_left a1_right =>
            apply h2 v a1_left
            right
            apply a1_right
        · apply is_deduct_v1.assume_
          simp
      · intro H a1
        simp at a1
        subst a1
        simp only [Forall_isFreeIn]
        simp only [def_iff_]
        -- simp only [formula.iff_]
        simp only [def_and_]
        -- simp only [formula.and_]
        simp only [var_is_free_in]
        simp
        contrapose
        push_neg
        intro a2
        apply h2
        simp_all
        · tauto
        · left
          rfl
  all_goals
    sorry


theorem C_18_3
  (U V : Formula_)
  (P_U P_V : Formula_)
  (h1 : IsReplOfFormulaInFormula U V P_U P_V)
  (h2 : is_proof_v1 (U.iff_ V)) : is_proof_v1 (P_U.iff_ P_V) :=
  by
  apply
    is_deduct_v1.mp_
      (Forall_ ((U.free_var_set ∪ V.free_var_set) ∩ P_U.bound_var_set).toList (U.iff_ V))
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
  (h1 : IsReplOfFormulaInFormula U V P_U P_V)
  (h2 : is_proof_v1 (U.iff_ V))
  (h3 : is_deduct_v1 Δ P_U) :
  is_deduct_v1 Δ P_V :=
  by
  apply is_deduct_v1.mp_ P_U
  · apply is_deduct_v1.mp_ (P_U.iff_ P_V)
    · simp only [def_iff_]
      simp only [def_and_]
      -- simp only [formula.iff_]
      -- simp only [formula.and_]
      SC
    · apply proof_imp_deduct
      exact C_18_3 U V P_U P_V h1 h2
  · exact h3


theorem T_18_5
  (P : Formula_)
  (v : VarName_) :
  is_proof_v1 ((forall_ v P).iff_ (exists_ v P.not_).not_) :=
  by
  simp only [def_exists_]
  -- simp only [exists_]
  apply C_18_4 P P.not_.not_ ((forall_ v P).iff_ (forall_ v P).not_.not_)
  · simp only [def_iff_]
    simp only [def_and_]
    -- simp only [formula.iff_]
    -- simp only [formula.and_]
    apply IsReplOfFormulaInFormula.not_
    apply IsReplOfFormulaInFormula.imp_
    · apply IsReplOfFormulaInFormula.imp_
      · apply IsReplOfFormulaInFormula.same_
        rfl
      · apply IsReplOfFormulaInFormula.not_
        apply IsReplOfFormulaInFormula.not_
        apply IsReplOfFormulaInFormula.forall_
        apply IsReplOfFormulaInFormula.diff_
        · rfl
        · rfl
    · apply IsReplOfFormulaInFormula.not_
      apply IsReplOfFormulaInFormula.imp_
      · apply IsReplOfFormulaInFormula.not_
        apply IsReplOfFormulaInFormula.not_
        apply IsReplOfFormulaInFormula.forall_
        apply IsReplOfFormulaInFormula.diff_
        · rfl
        · rfl
      · apply IsReplOfFormulaInFormula.same_
        rfl
  · simp only [def_iff_]
    simp only [def_and_]
    -- simp only [formula.iff_]
    -- simp only [formula.and_]
    SC
  · simp only [def_iff_]
    simp only [def_and_]
    -- simp only [formula.iff_]
    -- simp only [formula.and_]
    SC


theorem T_18_6
  (P_u P_v : Formula_)
  (u v : VarName_)
  (h1 : Similar P_u P_v u v) :
  is_proof_v1 ((forall_ u P_u).iff_ (forall_ v P_v)) :=
  by
  simp only [Similar] at h1
  cases h1
  case _ h1_left h1_right =>
    cases h1_right
    case _ h1_right_left h1_right_right =>
      cases h1_right_right
      case _ h1_right_right_left h1_right_right_right =>
        cases h1_right_right_right
        case _ h1_right_right_right_left h1_right_right_right_right =>
          cases h1_right_right_right_right
          case _ h1_right_right_right_right_left h1_right_right_right_right_right =>
            apply is_deduct_v1.mp_ ((forall_ v P_v).imp_ (forall_ u P_u))
            · apply is_deduct_v1.mp_ ((forall_ u P_u).imp_ (forall_ v P_v))
              · simp only [def_iff_]
                simp only [def_and_]
                -- simp only [formula.iff_]
                -- simp only [formula.and_]
                SC
              · apply deduction_theorem
                simp
                apply generalization
                · subst h1_right_right_right_right_left
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
            · apply deduction_theorem
              simp
              apply generalization
              · subst h1_right_right_right_right_right
                apply spec
                · apply is_deduct_v1.assume_
                  simp
                · exact h1_right_right_right_left
              · intro H a1
                simp at a1
                subst a1
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
  (h2 : IsReplOfFormulaInFormula (forall_ u P_u) (forall_ v P_v) Q Q')
  (h3 : Similar P_u P_v u v) :
  is_deduct_v1 Δ Q' :=
  by
  apply C_18_4 (forall_ u P_u) (forall_ v P_v) Q Q' Δ h2
  · apply T_18_6 P_u P_v u v h3
  · exact h1


theorem similar_not
  (P_u P_v : Formula_)
  (u v : VarName_)
  (h1 : Similar P_u P_v u v) :
  Similar P_u.not_ P_v.not_ u v :=
  by
  simp only [Similar] at *
  simp only [var_is_free_in] at *
  simp only [fast_admits_var_one_rec] at *
  simp only [fast_admits_var_one_rec_aux] at *
  simp only [fast_replace_free_var_one_rec] at *
  tauto


theorem T_18_8
  (P_u P_v : Formula_)
  (u v : VarName_)
  (h1 : Similar P_u P_v u v) :
  is_proof_v1 ((exists_ u P_u).iff_ (exists_ v P_v)) :=
  by
  simp only [def_exists_]
  -- simp only [exists_]
  apply is_deduct_v1.mp_ ((forall_ u P_u.not_).iff_ (forall_ v P_v.not_))
  · simp only [def_iff_]
    simp only [def_and_]
    -- simp only [formula.iff_]
    -- simp only [formula.and_]
    SC
  · apply T_18_6
    exact similar_not P_u P_v u v h1


theorem T18_9
  (Q Q' : Formula_)
  (P_u P_v : Formula_)
  (u v : VarName_)
  (Δ : Set Formula_)
  (h1 : is_deduct_v1 Δ Q)
  (h2 : IsReplOfFormulaInFormula (exists_ u P_u) (exists_ v P_v) Q Q')
  (h3 : Similar P_u P_v u v) :
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
    -- sim only [formula.iff_]
      simp only [def_and_]
      -- simp only [formula.and_]
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
      -- simp only [formula.iff_]
      -- simp only [formula.and_]
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
  -- simp only [Formula_.exists_]
  -- simp only [formula.iff_]
  -- simp only [formula.and_]
  SC


theorem T_19_4
  (P : Formula_)
  (u v : VarName_) :
  is_proof_v1 ((exists_ u (forall_ v P)).imp_ (forall_ v (exists_ u P))) :=
  by
  apply deduction_theorem
  simp
  apply generalization
  · apply rule_C (forall_ v P) (exists_ u P) u {exists_ u (forall_ v P)}
    · apply is_deduct_v1.assume_
      simp
    · apply exists_intro P u u
      · apply fast_admits_var_one_rec_self
      · simp only [fast_replace_free_var_one_rec_self]
        apply specId v
        apply is_deduct_v1.assume_
        simp
    · simp
      simp only [def_exists_]
      -- simp only [Formula_.exists_]
      simp only [var_is_free_in]
      simp
    · simp only [def_exists_]
      simp only [var_is_free_in]
      -- simp only [exists_]
      -- simp only [is_free_in]
      simp
  · simp
    simp only [def_exists_]
    -- simp only [Formula_.exists_]
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
      -- simp only [formula.iff_]
      -- simp only [formula.and_]
      SC
    · exact T_18_1 P Q v
  · exact T_19_1 P v h1


theorem T_19_6_left
  (P Q : Formula_)
  (v : VarName_) :
  is_proof_v1 ((forall_ v (P.iff_ Q)).imp_ ((exists_ v P).imp_ (exists_ v Q))) :=
  by
  apply deduction_theorem
  apply deduction_theorem
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
          -- simp only [iff_]
          -- simp only [and_]
          SC
        · apply specId v
          apply is_deduct_v1.assume_
          simp
      · apply is_deduct_v1.assume_
        simp
  · simp only [def_exists_]
    -- simp only [exists_]
    simp
    simp only [var_is_free_in]
    simp
  · simp only [def_exists_]
    -- simp only [exists_]
    simp only [var_is_free_in]
    simp


theorem T_19_6_right
  (P Q : Formula_)
  (v : VarName_) :
  is_proof_v1 ((forall_ v (P.iff_ Q)).imp_ ((exists_ v Q).imp_ (exists_ v P))) :=
  by
  apply deduction_theorem
  simp
  apply is_deduct_v1.mp_ (forall_ v (Q.iff_ P))
  · apply proof_imp_deduct
    apply T_19_6_left Q P v
  · apply generalization
    · apply is_deduct_v1.mp_ (P.iff_ Q)
      · simp only [def_iff_]
        simp only [def_and_]
        -- simp only [iff_]
        -- simp only [and_]
        SC
      · apply specId v
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
      -- simp only [exists_]
      -- simp only [iff_]
      -- simp only [and_]
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
  · apply IsReplOfFormulaInFormula.imp_
    · apply IsReplOfFormulaInFormula.same_
      rfl
    · apply IsReplOfFormulaInFormula.imp_
      · apply IsReplOfFormulaInFormula.diff_
        · rfl
        · rfl
      · apply IsReplOfFormulaInFormula.same_
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
  apply deduction_theorem
  simp
  apply generalization
  · apply deduction_theorem
    apply specId v
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
      -- simp only [formula.iff_]
      -- simp only [formula.and_]
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
          -- simp only [formula.iff_]
          -- simp only [formula.and_]
          SC
        · apply specId y
          apply specId y
          apply specId x
          apply specId y
          apply is_deduct_v1.axiom_
          exact is_axiom_v1.eq_2_eq_ y x y y
      · apply specId y
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
            -- simp only [formula.iff_]
            -- simp only [formula.and_]
            SC
          · apply specId z
            apply specId y
            apply specId z
            apply specId x
            apply is_deduct_v1.axiom_
            exact is_axiom_v1.eq_2_eq_ x z y z
        · apply specId z
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
  (h1 : IsReplOfVarInFormula r s P_r P_s)
  (h2 : ¬ var_is_bound_in r P_r)
  (h3 : ¬ var_is_bound_in s P_r) :
  is_proof_v1 ((eq_ r s).imp_ (P_r.iff_ P_s)) :=
  by
  induction h1
  case true_ =>
    simp only [def_iff_]
    -- simp only [formula.iff_]
    simp only [def_and_]
    -- simp only [formula.and_]
    SC
  case pred_const_ name n args_u args_v
    h1_1 =>
    apply
      is_deduct_v1.mp_
        ((eq_ r s).imp_ ((pred_const_ name (List.ofFn args_u)).iff_ (pred_const_ name (List.ofFn args_v))))
    · SC
    · apply
        is_deduct_v1.mp_ ((eq_ r s).imp_ (And_ (List.ofFn fun (i : Fin n) => eq_ (args_u i) (args_v i))))
      · apply
          is_deduct_v1.mp_
            ((And_ (List.ofFn fun (i : Fin n) => eq_ (args_u i) (args_v i))).imp_
              ((pred_const_ name (List.ofFn args_u)).iff_ (pred_const_ name (List.ofFn args_v))))
        · simp only [def_iff_]
          -- simp only [formula.iff_]
          simp only [def_and_]
          -- simp only [formula.and_]
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
          SC
        case _ n ih =>
          simp
          apply
            is_deduct_v1.mp_
              ((eq_ r s).imp_
                (List.foldr and_ true_
                  (List.ofFn fun (i : Fin n) => eq_ (args_u i.succ) (args_v i.succ))))
          · apply is_deduct_v1.mp_ ((eq_ r s).imp_ (eq_ (args_u 0) (args_v 0)))
            · simp only [def_and_]
              -- simp only [formula.and_]
              SC
            · specialize h1_1 0
              cases h1_1
              case _ c1 =>
                apply is_deduct_v1.mp_ (eq_ (args_u 0) (args_v 0))
                case _ =>
                  SC
                case _ =>
                  simp only [c1]
                  apply specId (args_v 0)
                  apply is_deduct_v1.axiom_
                  apply is_axiom_v1.eq_1_
              case _ c1 =>
                cases c1
                case _ c1_left c1_right =>
                  subst c1_left
                  subst c1_right
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
      -- simp only [formula.iff_]
      simp only [def_and_]
      -- simp only [formula.and_]
      SC
    · exact h1_ih
  case imp_ P_u Q_u P_v Q_v h1_1 h1_2 h1_ih_1
    h1_ih_2 =>
    simp only [var_is_bound_in] at h2
    push_neg at h2
    cases h2
    case intro h2_left h2_right =>
      simp only [var_is_bound_in] at h3
      push_neg at h3
      cases h3
      case intro h3_left h3_right =>
        specialize h1_ih_1 h2_left h3_left
        specialize h1_ih_2 h2_right h3_right
        apply is_deduct_v1.mp_ ((eq_ r s).imp_ (Q_u.iff_ Q_v))
        · apply is_deduct_v1.mp_ ((eq_ r s).imp_ (P_u.iff_ P_v))
          · simp only [def_iff_]
            -- simp only [formula.iff_]
            simp only [def_and_]
            -- simp only [formula.and_]
            SC
          · exact h1_ih_1
        · exact h1_ih_2
  case forall_ x P_u P_v h1_1 h1_ih =>
    simp only [var_is_bound_in] at h2
    push_neg at h2
    cases h2
    case _ h2_left h2_right =>
      simp only [var_is_bound_in] at h3
      push_neg at h3
      cases h3
      case _ h3_left h3_right =>
        apply deduction_theorem
        simp
        apply is_deduct_v1.mp_ (forall_ x (P_u.iff_ P_v))
        · apply proof_imp_deduct
          apply T_18_1
        · apply is_deduct_v1.mp_ (eq_ r s)
          · apply proof_imp_deduct
            apply is_deduct_v1.mp_ (forall_ x ((eq_ r s).imp_ (P_u.iff_ P_v)))
            · apply T_19_TS_21_left
              · -- simp only [formula.eq_]
                simp only [var_is_free_in]
                push_neg
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
