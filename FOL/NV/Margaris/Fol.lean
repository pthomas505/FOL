import FOL.NV.Margaris.Prop


set_option autoImplicit false


namespace FOL.NV

open Formula

open Sub.Var.One.Rec

open Margaris


def ProofEquiv (P Q : Formula) : Prop :=
  IsProof (P.iff_ Q)


/--
  IsReplOfVarInListFun u v l_u l_v := True if and only if l_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of u in l_u by occurrences of v.
-/
def IsReplOfVarInListFun
  (u v : VarName) :
  List VarName → List VarName → Prop
  | [], [] => True
  | hd_u :: tl_u, hd_v :: tl_v =>
    (hd_u = hd_v ∨ (hd_u = u ∧ hd_v = v)) ∧ IsReplOfVarInListFun u v tl_u tl_v
  | _, _ => False


/--
  IsReplOfVarInFormulaFun u v P_u P_v := True if and only if P_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of u in P_u by occurrences of v.
-/
def IsReplOfVarInFormulaFun
  (u v : VarName) :
  Formula → Formula → Prop
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
  (u v : VarName) :
  Formula → Formula → Prop
  | pred_const_
    (name : PredName)
    (n : ℕ)
    (args_u args_v : Fin n → VarName) :
    (∀ (i : Fin n), (args_u i = args_v i) ∨ (args_u i = u ∧ args_v i = v)) →
    IsReplOfVarInFormula u v (pred_const_ name (List.ofFn args_u)) (pred_const_ name (List.ofFn args_v))

  | pred_var_
    (name : PredName)
    (n : ℕ)
    (args_u args_v : Fin n → VarName) :
    (∀ (i : Fin n), (args_u i = args_v i) ∨ (args_u i = u ∧ args_v i = v)) →
    IsReplOfVarInFormula u v (pred_var_ name (List.ofFn args_u)) (pred_var_ name (List.ofFn args_v))

  | eq_
    (x_u y_u x_v y_v : VarName) :
    ((x_u = x_v) ∨ (x_u = u ∧ x_v = v)) →
    ((y_u = y_v) ∨ (y_u = u ∧ y_v = v)) →
    IsReplOfVarInFormula u v (eq_ x_u y_u) (eq_ x_v y_v)

  | true_ :
    IsReplOfVarInFormula u v true_ true_

  | false_ :
    IsReplOfVarInFormula u v false_ false_

  | not_
    (P_u P_v : Formula) :
    IsReplOfVarInFormula u v P_u P_v →
    IsReplOfVarInFormula u v P_u.not_ P_v.not_

  | imp_
    (P_u Q_u : Formula)
    (P_v Q_v : Formula) :
    IsReplOfVarInFormula u v P_u P_v →
    IsReplOfVarInFormula u v Q_u Q_v →
    IsReplOfVarInFormula u v (P_u.imp_ Q_u) (P_v.imp_ Q_v)

  | and_
    (P_u Q_u : Formula)
    (P_v Q_v : Formula) :
    IsReplOfVarInFormula u v P_u P_v →
    IsReplOfVarInFormula u v Q_u Q_v →
    IsReplOfVarInFormula u v (P_u.and_ Q_u) (P_v.and_ Q_v)

  | or_
    (P_u Q_u : Formula)
    (P_v Q_v : Formula) :
    IsReplOfVarInFormula u v P_u P_v →
    IsReplOfVarInFormula u v Q_u Q_v →
    IsReplOfVarInFormula u v (P_u.or_ Q_u) (P_v.or_ Q_v)

  | iff_
    (P_u Q_u : Formula)
    (P_v Q_v : Formula) :
    IsReplOfVarInFormula u v P_u P_v →
    IsReplOfVarInFormula u v Q_u Q_v →
    IsReplOfVarInFormula u v (P_u.iff_ Q_u) (P_v.iff_ Q_v)

  | forall_
    (x : VarName)
    (P_u P_v : Formula) :
    IsReplOfVarInFormula u v P_u P_v →
    IsReplOfVarInFormula u v (forall_ x P_u) (forall_ x P_v)

  | exists_
    (x : VarName)
    (P_u P_v : Formula) :
    IsReplOfVarInFormula u v P_u P_v →
    IsReplOfVarInFormula u v (exists_ x P_u) (exists_ x P_v)


/--
  IsReplOfFormulaInFormulaFun U V P_u P_v := True if and only if P_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of U in P_u by occurrences of V.
-/
def IsReplOfFormulaInFormulaFun
  (U V : Formula) :
  Formula → Formula → Prop
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
  (U V : Formula) :
  Formula → Formula → Prop

    -- not replacing an occurrence
  | same_
    (P_u P_v : Formula) :
    P_u = P_v →
    IsReplOfFormulaInFormula U V P_u P_v

    -- replacing an occurrence
  | diff_
    (P_u P_v : Formula) :
    P_u = U →
    P_v = V →
    IsReplOfFormulaInFormula U V P_u P_v

  | not_
    (P_u P_v : Formula) :
    IsReplOfFormulaInFormula U V P_u P_v →
    IsReplOfFormulaInFormula U V P_u.not_ P_v.not_

  | imp_
    (P_u Q_u : Formula)
    (P_v Q_v : Formula) :
    IsReplOfFormulaInFormula U V P_u P_v →
    IsReplOfFormulaInFormula U V Q_u Q_v →
    IsReplOfFormulaInFormula U V (P_u.imp_ Q_u) (P_v.imp_ Q_v)

  | and_
    (P_u Q_u : Formula)
    (P_v Q_v : Formula) :
    IsReplOfFormulaInFormula U V P_u P_v →
    IsReplOfFormulaInFormula U V Q_u Q_v →
    IsReplOfFormulaInFormula U V (P_u.and_ Q_u) (P_v.and_ Q_v)

  | or_
    (P_u Q_u : Formula)
    (P_v Q_v : Formula) :
    IsReplOfFormulaInFormula U V P_u P_v →
    IsReplOfFormulaInFormula U V Q_u Q_v →
    IsReplOfFormulaInFormula U V (P_u.or_ Q_u) (P_v.or_ Q_v)

  | iff_
    (P_u Q_u : Formula)
    (P_v Q_v : Formula) :
    IsReplOfFormulaInFormula U V P_u P_v →
    IsReplOfFormulaInFormula U V Q_u Q_v →
    IsReplOfFormulaInFormula U V (P_u.iff_ Q_u) (P_v.iff_ Q_v)

  | forall_
    (x : VarName)
    (P_u P_v : Formula) :
    IsReplOfFormulaInFormula U V P_u P_v →
    IsReplOfFormulaInFormula U V (forall_ x P_u) (forall_ x P_v)

  | exists_
    (x : VarName)
    (P_u P_v : Formula) :
    IsReplOfFormulaInFormula U V P_u P_v →
    IsReplOfFormulaInFormula U V (exists_ x P_u) (exists_ x P_v)


def Similar
  (P_u P_v : Formula)
  (u v : VarName) :
  Prop :=
  ¬ isFreeIn v P_u ∧
    ¬ isFreeIn u P_v ∧
      fastAdmits u v P_u ∧
        fastAdmits v u P_v ∧ P_v = fastReplaceFree u v P_u ∧ P_u = fastReplaceFree v u P_v


-- Universal Elimination
theorem T_17_1
  (P : Formula)
  (v t : VarName)
  (Δ : Set Formula)
  (h1 : IsDeduct Δ (forall_ v P))
  (h2 : fastAdmits v t P) :
  IsDeduct Δ (fastReplaceFree v t P) :=
  by
  apply IsDeduct.mp_ (forall_ v P)
  · apply IsDeduct.axiom_
    apply IsAxiom.pred_2_ v t P (fastReplaceFree v t P) h2
    rfl
  · exact h1

alias spec := T_17_1
alias forall_elim := T_17_1


theorem specId
  (v : VarName)
  (P : Formula)
  (Δ : Set Formula)
  (h1 : IsDeduct Δ (forall_ v P)) :
  IsDeduct Δ P :=
  by
  apply IsDeduct.mp_ (forall_ v P)
  · apply IsDeduct.axiom_
    apply IsAxiom.pred_2_ v v P
    · exact fastAdmits_self P v
    · exact fastReplaceFree_self P v
  · exact h1

alias forall_elim_id := specId


theorem T_17_3
  (P : Formula)
  (v t : VarName)
  (h1 : fastAdmits v t P) :
  IsProof ((fastReplaceFree v t P).imp_ (exists_ v P)) :=
  by
  simp only [fastAdmits] at h1

  simp only [def_exists_]
  -- simp only [Formula.exists_]

  simp only [IsProof]
  apply IsDeduct.mp_ ((forall_ v P.not_).imp_ (fastReplaceFree v t P).not_)
  · SC
  · apply IsDeduct.axiom_
    apply IsAxiom.pred_2_ v t
    · simp only [fastAdmits]
      simp only [fastAdmitsAux]
      exact h1
    · rfl


-- Existential Introduction
theorem T_17_4
  (P : Formula)
  (v t : VarName)
  (Δ : Set Formula)
  (h1 : fastAdmits v t P)
  (h2 : IsDeduct Δ (fastReplaceFree v t P)) :
  IsDeduct Δ (exists_ v P) :=
  by
  apply IsDeduct.mp_ (fastReplaceFree v t P)
  · apply proof_imp_deduct
    apply T_17_3
    exact h1
  · exact h2

alias exists_intro := T_17_4


theorem existsIntroId
  (P : Formula)
  (v : VarName)
  (Δ : Set Formula)
  (h1 : IsDeduct Δ P) :
  IsDeduct Δ (exists_ v P) :=
  by
  apply T_17_4 P v v Δ
  · exact fastAdmits_self P v
  · simp only [fastReplaceFree_self]
    exact h1


theorem T_17_6
  (P : Formula)
  (v : VarName) :
  IsProof ((forall_ v P).imp_ (exists_ v P)) :=
  by
  apply deduction_theorem
  simp
  apply existsIntroId
  apply specId v
  apply IsDeduct.assume_
  simp


theorem T_17_7
  (F : Formula)
  (v : VarName)
  (Δ : Set Formula)
  (h1 : IsDeduct Δ F)
  (h2 : ∀ (H : Formula), H ∈ Δ → ¬ isFreeIn v H) :
  IsDeduct Δ (forall_ v F) :=
  by
  induction h1
  case axiom_ h1_phi h1_1 =>
    apply IsDeduct.axiom_
    apply IsAxiom.gen_
    exact h1_1
  case assume_ h1_phi h1_1 =>
    apply IsDeduct.mp_ h1_phi
    · apply IsDeduct.axiom_
      apply IsAxiom.pred_3_
      exact h2 h1_phi h1_1
    · apply IsDeduct.assume_
      exact h1_1
  case mp_ h1_phi h1_psi _ _ h1_ih_1 h1_ih_2 =>
    apply IsDeduct.mp_ (forall_ v h1_phi)
    · apply IsDeduct.mp_ (forall_ v (h1_phi.imp_ h1_psi))
      · apply IsDeduct.axiom_
        apply IsAxiom.pred_1_
      · exact h1_ih_1
    · exact h1_ih_2

alias generalization := T_17_7


-- Universal Introduction
theorem univIntro
  (P : Formula)
  (v t : VarName)
  (Δ : Set Formula)
  (h1 : ¬ occursIn t P)
  (h2 : IsDeduct Δ (fastReplaceFree v t P))
  (h3 : ∀ (H : Formula), H ∈ Δ → ¬ isFreeIn t H) :
  IsDeduct Δ (forall_ v P) :=
  by
  rw [← fastReplaceFree_inverse P v t h1]
  apply IsDeduct.mp_ (forall_ t (fastReplaceFree v t P))
  · apply proof_imp_deduct
    apply deduction_theorem
    simp
    apply generalization
    · apply spec
      · apply IsDeduct.assume_
        simp
      · apply fastReplaceFree_fastAdmits
        exact h1
    · simp
      simp only [isFreeIn]
      simp
      intro a1 contra
      exact not_isFreeIn_fastReplaceFree P v t a1 contra
  · exact generalization (fastReplaceFree v t P) t Δ h2 h3


theorem isProofAltImpIsDeduct
  (F : Formula)
  (h1 : IsProofAlt F) :
  IsDeduct ∅ F :=
  by
  induction h1
  case prop_true_ =>
    apply IsDeduct.axiom_
    apply IsAxiom.prop_true_
  case prop_1_ h1_phi h1_psi =>
    apply IsDeduct.axiom_
    apply IsAxiom.prop_1_
  case prop_2_ h1_phi h1_psi h1_chi =>
    apply IsDeduct.axiom_
    apply IsAxiom.prop_2_
  case prop_3_ h1_phi h1_psi =>
    apply IsDeduct.axiom_
    apply IsAxiom.prop_3_
  case pred_1_ h1_v h1_phi h1_psi =>
    apply IsDeduct.axiom_
    apply IsAxiom.pred_1_
  case pred_2_ h1_v h1_t h1_phi h1_phi' h1_1 h1_ih_1 =>
    apply IsDeduct.axiom_
    exact IsAxiom.pred_2_ h1_v h1_t h1_phi h1_phi' h1_1 h1_ih_1
  case pred_3_ h1_v h1_phi h1_1 =>
    apply IsDeduct.axiom_
    apply IsAxiom.pred_3_
    exact h1_1
  case eq_1_ h1 =>
    apply IsDeduct.axiom_
    apply IsAxiom.eq_1_
  case eq_2_pred_const_ h1_name h1_n h1_xs h1_ys =>
    apply IsDeduct.axiom_
    apply IsAxiom.eq_2_pred_const_
  case eq_2_eq_ h1_x_0 h1_y_0 h1_x_1 h1_y_1 =>
    apply IsDeduct.axiom_
    apply IsAxiom.eq_2_eq_
  case gen_ h1_v h1_phi h1_1 h1_ih =>
    apply generalization
    · exact h1_ih
    · simp
  case mp_ h1_phi h1_psi h1_1 h1_2 h1_ih_1 h1_ih_2 =>
    exact IsDeduct.mp_ h1_phi h1_psi h1_ih_1 h1_ih_2
  all_goals
    sorry


theorem isDeductImpIsProofAlt
  (F : Formula)
  (h1 : IsDeduct ∅ F) :
  IsProofAlt F :=
  by
  induction h1
  case axiom_ h1_phi h1_1 =>
    induction h1_1
    case prop_true_ =>
      apply IsProofAlt.prop_true_
    case prop_1_ h1_1_phi h1_1_psi =>
      apply IsProofAlt.prop_1_
    case prop_2_ h1_1_phi h1_1_psi h1_1_chi =>
      apply IsProofAlt.prop_2_
    case prop_3_ h1_1_phi h1_1_psi =>
      apply IsProofAlt.prop_3_
    case pred_1_ h1_1_v h1_1_phi h1_1_psi =>
      apply IsProofAlt.pred_1_
    case pred_2_ h1_1_v h1_1_t h1_1_phi h1_1_1 h1_1_ih_1 h1_1_ih_2 =>
      apply IsProofAlt.pred_2_ h1_1_v h1_1_t h1_1_phi h1_1_1 h1_1_ih_1 h1_1_ih_2
    case pred_3_ h1_1_v h1_1_phi h1_1_1 =>
      apply IsProofAlt.pred_3_
      exact h1_1_1
    case eq_1_ h1_1 =>
      apply IsProofAlt.eq_1_
    case eq_2_pred_const_ h1_1_name h1_1_n h1_1_xs h1_1_ys =>
      apply IsProofAlt.eq_2_pred_const_
    case eq_2_eq_ h1_1_x_0 h1_1_y_0 h1_1_x_1 h1_1_y_1 =>
      apply IsProofAlt.eq_2_eq_
    case gen_ h1_1_v h1_1_phi h1_1_1 h1_1_ih =>
      apply IsProofAlt.gen_
      exact h1_1_ih
    all_goals
      sorry
  case assume_ h1_phi h1_1 =>
    simp at h1_1
  case mp_ h1_phi h1_psi h1_1 h1_2 h1_ih_1 h1_ih_2 =>
    exact IsProofAlt.mp_ h1_phi h1_psi h1_ih_1 h1_ih_2


theorem T_17_10
  (P : Formula)
  (u v : VarName) :
  IsProof ((forall_ u (forall_ v P)).imp_ (forall_ v (forall_ u P))) :=
  by
  apply deduction_theorem
  simp
  apply generalization
  · apply generalization
    · apply specId v P
      apply specId u (forall_ v P)
      apply IsDeduct.assume_
      simp
    · simp
      simp only [isFreeIn]
      simp
  · simp
    simp only [isFreeIn]
    simp


theorem T_17_11
  (P Q : Formula)
  (v : VarName)
  (h1 : ¬ isFreeIn v Q) :
  IsProof ((forall_ v (P.imp_ Q)).imp_ ((exists_ v P).imp_ Q)) :=
  by
  apply deduction_theorem
  simp
  simp only [def_exists_]
  -- simp only [exists_]
  apply IsDeduct.mp_ (Q.not_.imp_ (forall_ v Q.not_))
  · apply IsDeduct.mp_ ((forall_ v Q.not_).imp_ (forall_ v P.not_))
    · SC
    · apply IsDeduct.mp_ (forall_ v (Q.not_.imp_ P.not_))
      · apply IsDeduct.axiom_
        apply IsAxiom.pred_1_
      · apply generalization
        · apply IsDeduct.mp_ (P.imp_ Q)
          · apply proof_imp_deduct
            apply T_14_7
          · apply specId v (P.imp_ Q)
            apply IsDeduct.assume_
            simp
        · simp
          simp only [isFreeIn]
          simp
  · apply IsDeduct.axiom_
    apply IsAxiom.pred_3_
    simp only [isFreeIn]
    exact h1


-- Rule C
theorem T_17_12
  (P Q : Formula)
  (v : VarName)
  (Δ : Set Formula)
  (h1 : IsDeduct Δ (exists_ v P))
  (h2 : IsDeduct (Δ ∪ {P}) Q)
  (h3 : ∀ (H : Formula), H ∈ Δ → ¬ isFreeIn v H)
  (h4 : ¬ isFreeIn v Q) :
  IsDeduct Δ Q :=
  by
  apply IsDeduct.mp_ (exists_ v P)
  · apply IsDeduct.mp_ (forall_ v (P.imp_ Q))
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
  (P Q : Formula)
  (v t : VarName)
  (Δ : Set Formula)
  (h1 : IsDeduct Δ (exists_ v P))
  (h2 : IsDeduct (Δ ∪ {fastReplaceFree v t P}) Q)
  (h3 : ¬ occursIn t P)
  (h4 : ¬ occursIn t Q)
  (h5 : ∀ (H : Formula), H ∈ Δ → ¬ isFreeIn t H) : IsDeduct Δ Q :=
  by
  refine' rule_C (fastReplaceFree v t P) Q t Δ _ h2 h5 _
  · simp only [def_exists_] at h1
    -- simp only [exists_] at h1
    simp only [def_exists_]
    -- simp only [exists_]
    apply IsDeduct.mp_ (forall_ v P.not_).not_
    · apply IsDeduct.mp_ ((forall_ t (fastReplaceFree v t P.not_)).imp_ (forall_ v P.not_))
      · SC
      · apply deduction_theorem
        apply univIntro P.not_ v t _ h3
        · apply specId t
          apply IsDeduct.assume_
          simp
        · intro H a1
          simp at a1
          cases a1
          case _ c1 =>
            subst c1
            simp only [isFreeIn]
            simp
          case _ c1 =>
            exact h5 H c1
    · exact h1
  · intro contra
    apply h4
    apply isFreeIn_imp_occursIn
    exact contra


theorem T_17_14
  (P Q : Formula)
  (v : VarName) :
  IsProof ((exists_ v (P.and_ Q)).imp_ ((exists_ v P).and_ (exists_ v Q))) :=
  by
  apply deduction_theorem
  simp
  apply rule_C (P.and_ Q) ((exists_ v P).and_ (exists_ v Q)) v
  · apply IsDeduct.assume_
    simp
  · apply IsDeduct.mp_ (exists_ v Q)
    · apply IsDeduct.mp_ (exists_ v P)
      · simp only [def_and_]
        -- simp only [formula.and_]
        SC
      · apply exists_intro P v v
        · apply fastAdmits_self
        · simp only [fastReplaceFree_self]
          apply IsDeduct.mp_ (P.and_ Q)
          · simp only [def_and_]
            -- simp only [formula.and_]
            SC
          · apply IsDeduct.assume_
            simp
    · apply exists_intro Q v v
      · apply fastAdmits_self
      · simp only [fastReplaceFree_self]
        apply IsDeduct.mp_ (P.and_ Q)
        · simp only [def_and_]
          -- simp only [formula.and_]
          SC
        · apply IsDeduct.assume_
          simp
  · simp only [def_and_]
    -- simp only [and_]
    simp only [def_exists_]
    -- simp only [exists_]
    simp
    simp only [isFreeIn]
    simp
  · simp only [def_and_]
    -- simp only [and_]
    simp only [def_exists_]
    -- simp only [exists_]
    simp only [isFreeIn]
    simp


theorem T_18_1_left
  (P Q : Formula)
  (v : VarName) :
  IsProof ((forall_ v (P.iff_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q))) :=
  by
  simp only [def_iff_]
  -- simp only [iff_]
  apply deduction_theorem
  apply deduction_theorem
  simp
  apply generalization
  · apply IsDeduct.mp_ P
    · apply IsDeduct.mp_ ((P.imp_ Q).and_ (Q.imp_ P))
      · simp only [def_and_]
        -- simp only [formula.and_]
        SC
      · apply specId v
        apply IsDeduct.assume_
        simp
    · apply specId v
      apply IsDeduct.assume_
      simp
  · simp
    simp only [isFreeIn]
    simp


theorem T_18_1_right
  (P Q : Formula)
  (v : VarName) :
  IsProof ((forall_ v (P.iff_ Q)).imp_ ((forall_ v Q).imp_ (forall_ v P))) :=
  by
  simp only [def_iff_]
  -- simp only [iff_]
  apply deduction_theorem
  apply deduction_theorem
  simp
  apply generalization
  · apply IsDeduct.mp_ Q
    · apply IsDeduct.mp_ ((P.imp_ Q).and_ (Q.imp_ P))
      · simp only [def_and_]
        -- simp only [formula.and_]
        SC
      · apply specId v
        apply IsDeduct.assume_
        simp
    · apply specId v
      apply IsDeduct.assume_
      simp
  · simp
    simp only [isFreeIn]
    simp


theorem T_18_1
  (P Q : Formula)
  (v : VarName) :
  IsProof ((forall_ v (P.iff_ Q)).imp_ ((forall_ v P).iff_ (forall_ v Q))) :=
  by
  apply IsDeduct.mp_ ((forall_ v (P.iff_ Q)).imp_ ((forall_ v Q).imp_ (forall_ v P)))
  · apply IsDeduct.mp_ ((forall_ v (P.iff_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q)))
    · simp only [def_iff_]
      -- simp only [formula.iff_]
      simp only [def_and_]
      -- simp only [formula.and_]
      SC
    · apply T_18_1_left
  · apply T_18_1_right


theorem Forall_spec_id
  (xs : List VarName)
  (P : Formula) :
  IsProof ((Forall_ xs P).imp_ P) :=
  by
  induction xs
  case nil =>
    simp only [Forall_]
    apply prop_id
  case cons xs_hd xs_tl xs_ih =>
    simp only [Forall_]
    apply deduction_theorem
    simp
    apply IsDeduct.mp_ (Forall_ xs_tl P)
    apply proof_imp_deduct
    exact xs_ih
    apply specId xs_hd
    apply IsDeduct.assume_
    simp
    rfl


theorem Forall_spec_id'
  (xs : List VarName)
  (P : Formula)
  (Δ : Set Formula)
  (h1 : IsDeduct Δ (Forall_ xs P)) :
  IsDeduct Δ P :=
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
  (P : Formula)
  (xs : List VarName)
  (x : VarName) :
  isBoundIn x (Forall_ xs P) ↔ x ∈ xs ∨ isBoundIn x P :=
  by
  simp only [Formula.Forall_]
  induction xs
  case nil =>
    simp
  case cons xs_hd xs_tl xs_ih =>
    simp
    simp only [isBoundIn]
    simp only [xs_ih]
    tauto


theorem Forall_isFreeIn
  (P : Formula)
  (xs : List VarName)
  (x : VarName) :
  isFreeIn x (Forall_ xs P) ↔ x ∉ xs ∧ isFreeIn x P :=
  by
  simp only [Formula.Forall_]
  induction xs
  case nil =>
    simp
  case cons xs_hd xs_tl xs_ih =>
    simp
    simp only [isFreeIn]
    simp only [xs_ih]
    tauto


-- The equivalence theorem
theorem T_18_2
  (U V : Formula)
  (P_U P_V : Formula)
  (l : List VarName)
  (h1 : IsReplOfFormulaInFormula U V P_U P_V)
  (h2 : ∀ (v : VarName), (isFreeIn v U ∨ isFreeIn v V) ∧ isBoundIn v P_U → v ∈ l) :
  IsProof ((Forall_ l (U.iff_ V)).imp_ (P_U.iff_ P_V)) :=
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
    simp only [isBoundIn] at h2
    apply IsDeduct.mp_ ((Forall_ l (U.iff_ V)).imp_ (h1_P.iff_ h1_P'))
    · simp only [def_iff_]
      -- simp only [formula.iff_]
      simp only [def_and_]
      -- simp only [formula.and_]
      SC
    · exact h1_ih h2
  case imp_ h1_P h1_Q h1_P' h1_Q' h1_1 h1_2 h1_ih_1
    h1_ih_2 =>
    simp only [isBoundIn] at h2
    apply IsDeduct.mp_ ((Forall_ l (U.iff_ V)).imp_ (h1_P.iff_ h1_P'))
    · apply IsDeduct.mp_ ((Forall_ l (U.iff_ V)).imp_ (h1_Q.iff_ h1_Q'))
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
  case forall_ h1_x h1_P h1_P' h1_1
    h1_ih =>
    simp only [isBoundIn] at h2
    simp at h2
    apply deduction_theorem
    simp
    apply IsDeduct.mp_ (forall_ h1_x (h1_P.iff_ h1_P'))
    · apply proof_imp_deduct
      apply T_18_1
    · apply generalization
      · apply IsDeduct.mp_ (Forall_ l (U.iff_ V))
        · apply proof_imp_deduct
          apply h1_ih
          intro v a1
          cases a1
          case _ a1_left a1_right =>
            apply h2 v a1_left
            right
            apply a1_right
        · apply IsDeduct.assume_
          simp
      · intro H a1
        simp at a1
        subst a1
        simp only [Forall_isFreeIn]
        simp only [def_iff_]
        -- simp only [formula.iff_]
        simp only [def_and_]
        -- simp only [formula.and_]
        simp only [isFreeIn]
        sorry
  all_goals
    sorry


theorem C_18_3
  (U V : Formula)
  (P_U P_V : Formula)
  (h1 : IsReplOfFormulaInFormula U V P_U P_V)
  (h2 : IsProof (U.iff_ V)) : IsProof (P_U.iff_ P_V) :=
  by
  apply
    IsDeduct.mp_
      (Forall_ ((U.freeVarSet ∪ V.freeVarSet) ∩ P_U.boundVarSet).toList (U.iff_ V))
  · apply T_18_2 U V P_U P_V ((U.freeVarSet ∪ V.freeVarSet) ∩ P_U.boundVarSet).toList h1
    intro v a1
    simp
    simp only [isFreeIn_iff_mem_freeVarSet] at a1
    simp only [isBoundIn_iff_mem_boundVarSet] at a1
    exact a1
  · simp only [Formula.Forall_]
    induction ((U.freeVarSet ∪ V.freeVarSet) ∩ P_U.boundVarSet).toList
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
  (U V : Formula)
  (P_U P_V : Formula)
  (Δ : Set Formula)
  (h1 : IsReplOfFormulaInFormula U V P_U P_V)
  (h2 : IsProof (U.iff_ V))
  (h3 : IsDeduct Δ P_U) :
  IsDeduct Δ P_V :=
  by
  apply IsDeduct.mp_ P_U
  · apply IsDeduct.mp_ (P_U.iff_ P_V)
    · simp only [def_iff_]
      simp only [def_and_]
      -- simp only [formula.iff_]
      -- simp only [formula.and_]
      SC
    · apply proof_imp_deduct
      exact C_18_3 U V P_U P_V h1 h2
  · exact h3


theorem T_18_5
  (P : Formula)
  (v : VarName) :
  IsProof ((forall_ v P).iff_ (exists_ v P.not_).not_) :=
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
  (P_u P_v : Formula)
  (u v : VarName)
  (h1 : Similar P_u P_v u v) :
  IsProof ((forall_ u P_u).iff_ (forall_ v P_v)) :=
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
            apply IsDeduct.mp_ ((forall_ v P_v).imp_ (forall_ u P_u))
            · apply IsDeduct.mp_ ((forall_ u P_u).imp_ (forall_ v P_v))
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
                  · apply IsDeduct.assume_
                    simp
                  · exact h1_right_right_left
                · intro H a1
                  simp at a1
                  subst a1
                  simp only [isFreeIn]
                  simp
                  intro _
                  exact h1_left
            · apply deduction_theorem
              simp
              apply generalization
              · subst h1_right_right_right_right_right
                apply spec
                · apply IsDeduct.assume_
                  simp
                · exact h1_right_right_right_left
              · intro H a1
                simp at a1
                subst a1
                simp only [isFreeIn]
                simp
                intro _
                exact h1_right_left


-- Change of bound variable
theorem T_18_7
  (P_u P_v Q Q' : Formula)
  (u v : VarName)
  (Δ : Set Formula)
  (h1 : IsDeduct Δ Q)
  (h2 : IsReplOfFormulaInFormula (forall_ u P_u) (forall_ v P_v) Q Q')
  (h3 : Similar P_u P_v u v) :
  IsDeduct Δ Q' :=
  by
  apply C_18_4 (forall_ u P_u) (forall_ v P_v) Q Q' Δ h2
  · apply T_18_6 P_u P_v u v h3
  · exact h1


theorem similar_not
  (P_u P_v : Formula)
  (u v : VarName)
  (h1 : Similar P_u P_v u v) :
  Similar P_u.not_ P_v.not_ u v :=
  by
  simp only [Similar] at *
  simp only [isFreeIn] at *
  simp only [fastAdmits] at *
  simp only [fastAdmitsAux] at *
  simp only [fastReplaceFree] at *
  tauto


theorem T_18_8
  (P_u P_v : Formula)
  (u v : VarName)
  (h1 : Similar P_u P_v u v) :
  IsProof ((exists_ u P_u).iff_ (exists_ v P_v)) :=
  by
  simp only [def_exists_]
  -- simp only [exists_]
  apply IsDeduct.mp_ ((forall_ u P_u.not_).iff_ (forall_ v P_v.not_))
  · simp only [def_iff_]
    simp only [def_and_]
    -- simp only [formula.iff_]
    -- simp only [formula.and_]
    SC
  · apply T_18_6
    exact similar_not P_u P_v u v h1


theorem T18_9
  (Q Q' : Formula)
  (P_u P_v : Formula)
  (u v : VarName)
  (Δ : Set Formula)
  (h1 : IsDeduct Δ Q)
  (h2 : IsReplOfFormulaInFormula (exists_ u P_u) (exists_ v P_v) Q Q')
  (h3 : Similar P_u P_v u v) :
  IsDeduct Δ Q' :=
  by
  apply C_18_4 (exists_ u P_u) (exists_ v P_v) Q Q' Δ h2
  · exact T_18_8 P_u P_v u v h3
  · exact h1


theorem T_19_1
  (P : Formula)
  (v : VarName)
  (h1 : ¬ isFreeIn v P) :
  IsProof ((forall_ v P).iff_ P) :=
  by
  apply IsDeduct.mp_ ((forall_ v P).imp_ P)
  · apply IsDeduct.mp_ (P.imp_ (forall_ v P))
    · simp only [def_iff_]
    -- sim only [formula.iff_]
      simp only [def_and_]
      -- simp only [formula.and_]
      SC
    · apply IsDeduct.axiom_
      exact IsAxiom.pred_3_ v P h1
  · apply IsDeduct.axiom_
    apply IsAxiom.pred_2_ v v P P
    · apply fastAdmits_self
    · apply fastReplaceFree_self


theorem T_19_2
  (P : Formula)
  (u v : VarName) :
  IsProof ((forall_ u (forall_ v P)).iff_ (forall_ v (forall_ u P))) :=
  by
  apply IsDeduct.mp_ ((forall_ u (forall_ v P)).imp_ (forall_ v (forall_ u P)))
  · apply IsDeduct.mp_ ((forall_ v (forall_ u P)).imp_ (forall_ u (forall_ v P)))
    · simp only [def_iff_]
      simp only [def_and_]
      -- simp only [formula.iff_]
      -- simp only [formula.and_]
      SC
    · apply T_17_10
  · apply T_17_10


theorem T_19_3
  (P : Formula)
  (v : VarName) :
  IsProof ((forall_ v P.not_).iff_ (exists_ v P).not_) :=
  by
  simp only [def_exists_]
  simp only [def_iff_]
  simp only [def_and_]
  -- simp only [Formula.exists_]
  -- simp only [formula.iff_]
  -- simp only [formula.and_]
  SC


theorem T_19_4
  (P : Formula)
  (u v : VarName) :
  IsProof ((exists_ u (forall_ v P)).imp_ (forall_ v (exists_ u P))) :=
  by
  apply deduction_theorem
  simp
  apply generalization
  · apply rule_C (forall_ v P) (exists_ u P) u {exists_ u (forall_ v P)}
    · apply IsDeduct.assume_
      simp
    · apply exists_intro P u u
      · apply fastAdmits_self
      · simp only [fastReplaceFree_self]
        apply specId v
        apply IsDeduct.assume_
        simp
    · simp
      simp only [def_exists_]
      -- simp only [Formula.exists_]
      simp only [isFreeIn]
      simp
    · simp only [def_exists_]
      simp only [isFreeIn]
      -- simp only [exists_]
      -- simp only [is_free_in]
      simp
  · simp
    simp only [def_exists_]
    -- simp only [Formula.exists_]
    simp only [isFreeIn]
    simp


theorem T_19_5
  (P Q : Formula)
  (v : VarName)
  (h1 : ¬ isFreeIn v P) :
  IsProof ((forall_ v (P.iff_ Q)).imp_ (P.iff_ (forall_ v Q))) :=
  by
  apply IsDeduct.mp_ ((forall_ v P).iff_ P)
  · apply IsDeduct.mp_ ((forall_ v (P.iff_ Q)).imp_ ((forall_ v P).iff_ (forall_ v Q)))
    · simp only [def_iff_]
      simp only [def_and_]
      -- simp only [formula.iff_]
      -- simp only [formula.and_]
      SC
    · exact T_18_1 P Q v
  · exact T_19_1 P v h1


theorem T_19_6_left
  (P Q : Formula)
  (v : VarName) :
  IsProof ((forall_ v (P.iff_ Q)).imp_ ((exists_ v P).imp_ (exists_ v Q))) :=
  by
  apply deduction_theorem
  apply deduction_theorem
  simp
  apply rule_C P (exists_ v Q) v {exists_ v P, forall_ v (P.iff_ Q)}
  · apply IsDeduct.assume_
    simp
  · apply exists_intro Q v v
    · apply fastAdmits_self
    · simp only [fastReplaceFree_self]
      apply IsDeduct.mp_ P
      · apply IsDeduct.mp_ (P.iff_ Q)
        · simp only [def_iff_]
          simp only [def_and_]
          -- simp only [iff_]
          -- simp only [and_]
          SC
        · apply specId v
          apply IsDeduct.assume_
          simp
      · apply IsDeduct.assume_
        simp
  · simp only [def_exists_]
    -- simp only [exists_]
    simp
    simp only [isFreeIn]
    simp
  · simp only [def_exists_]
    -- simp only [exists_]
    simp only [isFreeIn]
    simp


theorem T_19_6_right
  (P Q : Formula)
  (v : VarName) :
  IsProof ((forall_ v (P.iff_ Q)).imp_ ((exists_ v Q).imp_ (exists_ v P))) :=
  by
  apply deduction_theorem
  simp
  apply IsDeduct.mp_ (forall_ v (Q.iff_ P))
  · apply proof_imp_deduct
    apply T_19_6_left Q P v
  · apply generalization
    · apply IsDeduct.mp_ (P.iff_ Q)
      · simp only [def_iff_]
        simp only [def_and_]
        -- simp only [iff_]
        -- simp only [and_]
        SC
      · apply specId v
        apply IsDeduct.assume_
        simp
    · simp
      simp only [isFreeIn]
      simp


theorem T_19_6
  (P Q : Formula)
  (v : VarName) :
  IsProof ((forall_ v (P.iff_ Q)).imp_ ((exists_ v P).iff_ (exists_ v Q))) :=
  by
  apply IsDeduct.mp_ ((forall_ v (P.iff_ Q)).imp_ ((exists_ v P).imp_ (exists_ v Q)))
  · apply IsDeduct.mp_ ((forall_ v (P.iff_ Q)).imp_ ((exists_ v Q).imp_ (exists_ v P)))
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
  (P Q : Formula)
  (v : VarName)
  (h1 : ¬ isFreeIn v P) :
  IsProof ((forall_ v (P.imp_ Q)).imp_ (P.imp_ (forall_ v Q))) :=
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
  · apply IsDeduct.axiom_
    apply IsAxiom.pred_1_


theorem T_19_TS_21_right
  (P Q : Formula)
  (v : VarName)
  (h1 : ¬ isFreeIn v P) :
  IsProof ((P.imp_ (forall_ v Q)).imp_ (forall_ v (P.imp_ Q))) :=
  by
  apply deduction_theorem
  simp
  apply generalization
  · apply deduction_theorem
    apply specId v
    apply IsDeduct.mp_ P
    · apply IsDeduct.assume_
      simp
    · apply IsDeduct.assume_
      simp
  · intro H a1
    simp at a1
    subst a1
    simp only [isFreeIn]
    simp
    exact h1


theorem T_19_TS_21
  (P Q : Formula)
  (v : VarName)
  (h1 : ¬ isFreeIn v P) :
  IsProof ((forall_ v (P.imp_ Q)).iff_ (P.imp_ (forall_ v Q))) :=
  by
  apply IsDeduct.mp_ ((forall_ v (P.imp_ Q)).imp_ (P.imp_ (forall_ v Q)))
  · apply IsDeduct.mp_ ((P.imp_ (forall_ v Q)).imp_ (forall_ v (P.imp_ Q)))
    · simp only [def_iff_]
      simp only [def_and_]
      -- simp only [formula.iff_]
      -- simp only [formula.and_]
      SC
    · exact T_19_TS_21_right P Q v h1
  · exact T_19_TS_21_left P Q v h1


theorem T_21_1
  (x y : VarName) :
  IsProof (forall_ x (forall_ y ((eq_ x y).imp_ (eq_ y x)))) :=
  by
  apply generalization
  · apply generalization
    · apply IsDeduct.mp_ (eq_ y y)
      · apply IsDeduct.mp_ (((eq_ y y).and_ (eq_ x y)).imp_ ((eq_ y x).iff_ (eq_ y y)))
        · simp only [def_iff_]
          simp only [def_and_]
          -- simp only [formula.iff_]
          -- simp only [formula.and_]
          SC
        · apply specId y
          apply specId y
          apply specId x
          apply specId y
          apply IsDeduct.axiom_
          exact IsAxiom.eq_2_eq_ y x y y
      · apply specId y
        apply IsDeduct.axiom_
        exact IsAxiom.eq_1_ y
    · intro H a1
      simp at a1
  · intro H a1
    simp at a1


theorem T_21_2
  (x y z : VarName) :
  IsProof (forall_ x (forall_ y (forall_ z (((eq_ x y).and_ (eq_ y z)).imp_ (eq_ x z))))) :=
  by
  apply generalization
  · apply generalization
    · apply generalization
      · apply IsDeduct.mp_ (eq_ z z)
        · apply IsDeduct.mp_ (((eq_ x y).and_ (eq_ z z)).imp_ ((eq_ x z).iff_ (eq_ y z)))
          · simp only [def_iff_]
            simp only [def_and_]
            -- simp only [formula.iff_]
            -- simp only [formula.and_]
            SC
          · apply specId z
            apply specId y
            apply specId z
            apply specId x
            apply IsDeduct.axiom_
            exact IsAxiom.eq_2_eq_ x z y z
        · apply specId z
          apply IsDeduct.axiom_
          exact IsAxiom.eq_1_ z
      · intro H a1
        simp at a1
    · intro H a1
      simp at a1
  · intro H a1
    simp at a1


theorem T_21_8
  (P_r P_s : Formula)
  (r s : VarName)
  (h1 : IsReplOfVarInFormula r s P_r P_s)
  (h2 : ¬ isBoundIn r P_r)
  (h3 : ¬ isBoundIn s P_r) :
  IsProof ((eq_ r s).imp_ (P_r.iff_ P_s)) :=
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
      IsDeduct.mp_
        ((eq_ r s).imp_ ((pred_const_ name (List.ofFn args_u)).iff_ (pred_const_ name (List.ofFn args_v))))
    · SC
    · apply
        IsDeduct.mp_ ((eq_ r s).imp_ (And_ (List.ofFn fun (i : Fin n) => eq_ (args_u i) (args_v i))))
      · apply
          IsDeduct.mp_
            ((And_ (List.ofFn fun (i : Fin n) => eq_ (args_u i) (args_v i))).imp_
              ((pred_const_ name (List.ofFn args_u)).iff_ (pred_const_ name (List.ofFn args_v))))
        · simp only [def_iff_]
          -- simp only [formula.iff_]
          simp only [def_and_]
          -- simp only [formula.and_]
          SC
        · apply Forall_spec_id' (List.ofFn args_v)
          apply Forall_spec_id' (List.ofFn args_u)
          apply IsDeduct.axiom_
          exact IsAxiom.eq_2_pred_const_ name n args_u args_v
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
            IsDeduct.mp_
              ((eq_ r s).imp_
                (List.foldr and_ true_
                  (List.ofFn fun (i : Fin n) => eq_ (args_u i.succ) (args_v i.succ))))
          · apply IsDeduct.mp_ ((eq_ r s).imp_ (eq_ (args_u 0) (args_v 0)))
            · simp only [def_and_]
              -- simp only [formula.and_]
              SC
            · specialize h1_1 0
              cases h1_1
              case _ c1 =>
                apply IsDeduct.mp_ (eq_ (args_u 0) (args_v 0))
                case _ =>
                  SC
                case _ =>
                  simp only [c1]
                  apply specId (args_v 0)
                  apply IsDeduct.axiom_
                  apply IsAxiom.eq_1_
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
    simp only [isBoundIn] at h2
    simp only [isBoundIn] at h3
    specialize h1_ih h2 h3
    apply IsDeduct.mp_ ((eq_ r s).imp_ (P_u.iff_ P_v))
    · simp only [def_iff_]
      -- simp only [formula.iff_]
      simp only [def_and_]
      -- simp only [formula.and_]
      SC
    · exact h1_ih
  case imp_ P_u Q_u P_v Q_v h1_1 h1_2 h1_ih_1
    h1_ih_2 =>
    simp only [isBoundIn] at h2
    push_neg at h2
    cases h2
    case intro h2_left h2_right =>
      simp only [isBoundIn] at h3
      push_neg at h3
      cases h3
      case intro h3_left h3_right =>
        specialize h1_ih_1 h2_left h3_left
        specialize h1_ih_2 h2_right h3_right
        apply IsDeduct.mp_ ((eq_ r s).imp_ (Q_u.iff_ Q_v))
        · apply IsDeduct.mp_ ((eq_ r s).imp_ (P_u.iff_ P_v))
          · simp only [def_iff_]
            -- simp only [formula.iff_]
            simp only [def_and_]
            -- simp only [formula.and_]
            SC
          · exact h1_ih_1
        · exact h1_ih_2
  case forall_ x P_u P_v h1_1 h1_ih =>
    simp only [isBoundIn] at h2
    push_neg at h2
    cases h2
    case _ h2_left h2_right =>
      simp only [isBoundIn] at h3
      push_neg at h3
      cases h3
      case _ h3_left h3_right =>
        apply deduction_theorem
        simp
        apply IsDeduct.mp_ (forall_ x (P_u.iff_ P_v))
        · apply proof_imp_deduct
          apply T_18_1
        · apply IsDeduct.mp_ (eq_ r s)
          · apply proof_imp_deduct
            apply IsDeduct.mp_ (forall_ x ((eq_ r s).imp_ (P_u.iff_ P_v)))
            · apply T_19_TS_21_left
              · -- simp only [formula.eq_]
                simp only [isFreeIn]
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
          · apply IsDeduct.assume_
            simp
  all_goals
    sorry


--#lint
