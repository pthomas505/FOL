import MathlibExtra.FunctionUpdateITE
import FOL.NV.Deduct


set_option autoImplicit false


open Formula_


/--
  Used for the soundness and completeness proofs of classical propositional logic.
-/
def Formula_.is_prime : Formula_ → Prop
  | pred_const_ _ _ => True
  | pred_var_ _ _ => True
  | eq_ _ _ => True
  | true_ => False
  | false_ => False
  | not_ _ => False
  | imp_ _ _ => False
  | and_ _ _ => False
  | or_ _ _ => False
  | iff_ _ _ => False
  | forall_ _ _ => True
  | exists_ _ _ => True
  | def_ _ _ => True


def Formula_.prime_set : Formula_ → Finset Formula_
  | pred_const_ X xs => {pred_const_ X xs}
  | pred_var_ X xs => {pred_var_ X xs}
  | eq_ x y => {eq_ x y}
  | true_ => ∅
  | false_ => ∅
  | not_ phi => phi.prime_set
  | imp_ phi psi => phi.prime_set ∪ psi.prime_set
  | and_ phi psi => phi.prime_set ∪ psi.prime_set
  | or_ phi psi => phi.prime_set ∪ psi.prime_set
  | iff_ phi psi => phi.prime_set ∪ psi.prime_set
  | forall_ x phi => {forall_ x phi}
  | exists_ x phi => {exists_ x phi}
  | def_ X xs => {def_ X xs}


def Formula_.substPrime (σ : Formula_ → Formula_) : Formula_ → Formula_
  | pred_const_ X xs => σ (pred_const_ X xs)
  | pred_var_ X xs => σ (pred_var_ X xs)
  | eq_ x y => σ (eq_ x y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (phi.substPrime σ)
  | imp_ phi psi => imp_ (phi.substPrime σ) (psi.substPrime σ)
  | and_ phi psi => and_ (phi.substPrime σ) (psi.substPrime σ)
  | or_ phi psi => or_ (phi.substPrime σ) (psi.substPrime σ)
  | iff_ phi psi => iff_ (phi.substPrime σ) (psi.substPrime σ)
  | forall_ x phi => σ (forall_ x phi)
  | exists_ x phi => σ (exists_ x phi)
  | def_ X xs => σ (def_ X xs)


def VarBoolAssignment := Formula_ → Bool
  deriving Inhabited


def Formula_.evalPrime (V : VarBoolAssignment) : Formula_ → Prop
  | pred_const_ X xs => V (pred_const_ X xs)
  | pred_var_ X xs => V (pred_var_ X xs)
  | eq_ x y => V (eq_ x y)
  | true_ => True
  | false_ => False
  | not_ phi => ¬ Formula_.evalPrime V phi
  | imp_ phi psi => Formula_.evalPrime V phi → Formula_.evalPrime V psi
  | and_ phi psi => Formula_.evalPrime V phi ∧ Formula_.evalPrime V psi
  | or_ phi psi => Formula_.evalPrime V phi ∨ Formula_.evalPrime V psi
  | iff_ phi psi => Formula_.evalPrime V phi ↔ Formula_.evalPrime V psi
  | forall_ x phi => V (forall_ x phi)
  | exists_ x phi => V (exists_ x phi)
  | def_ X xs => V (def_ X xs)


instance
  (V : VarBoolAssignment)
  (F : Formula_) :
  Decidable (Formula_.evalPrime V F) :=
  by
  induction F generalizing V
  all_goals
    simp only [Formula_.evalPrime]
    infer_instance


def Formula_.IsTautoPrime (P : Formula_) : Prop :=
  ∀ V : VarBoolAssignment, P.evalPrime V


def evalPrimeFfToNot
  (V : VarBoolAssignment)
  (P : Formula_) :
  Formula_ :=
  if Formula_.evalPrime V P
  then P
  else P.not_


theorem evalPrime_prime
  (F : Formula_)
  (V : VarBoolAssignment)
  (h1 : F.is_prime) :
  F.evalPrime V = V F :=
  by
  induction F
  case true_ | false_ | not_ | imp_ | and_ | or_ | iff_ =>
    simp only [Formula_.is_prime] at h1
  case pred_const_ | pred_var_ | eq_ | forall_ | exists_ | def_ =>
    rfl


example
  (F : Formula_)
  (V V' : VarBoolAssignment)
  (h1 : ∀ H : Formula_, H ∈ F.prime_set → V H = V' H) :
  F.evalPrime V ↔ F.evalPrime V' :=
  by
  induction F
  case pred_const_ | pred_var_ | eq_ | forall_ | exists_ | def_ =>
    simp only [Formula_.prime_set] at h1

    simp only [Formula_.evalPrime]
    congr! 1
    apply h1
    simp
  case true_ | false_ =>
    simp only [Formula_.evalPrime]
  case not_ phi phi_ih =>
    simp only [Formula_.prime_set] at h1

    simp only [Formula_.evalPrime]
    congr! 1
    exact phi_ih h1
  case
    imp_ phi psi phi_ih psi_ih
  | and_ phi psi phi_ih psi_ih
  | or_ phi psi phi_ih psi_ih
  | iff_ phi psi phi_ih psi_ih =>
    simp only [Formula_.prime_set] at h1
    simp at h1

    simp only [Formula_.evalPrime]
    congr! 1
    · apply phi_ih
      intro H a1
      apply h1
      left
      exact a1
    · apply psi_ih
      intro H a1
      apply h1
      right
      exact a1


theorem evalPrime_substPrime_eq_evalPrime_evalPrime
  (F : Formula_)
  (σ : Formula_ → Formula_)
  (V : VarBoolAssignment) :
  (F.substPrime σ).evalPrime V ↔
    F.evalPrime fun H : Formula_ => (σ H).evalPrime V :=
  by
  induction F
  case pred_const_ | pred_var_ | eq_ | forall_ | exists_ | def_ =>
    simp only [Formula_.substPrime]
    simp only [Formula_.evalPrime]
    simp
  case true_ | false_ =>
    rfl
  case not_ phi phi_ih =>
    simp only [Formula_.substPrime]
    simp only [Formula_.evalPrime]
    congr! 1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [Formula_.substPrime]
    simp only [Formula_.evalPrime]
    congr! 1


theorem isTautoPrime_imp_isTautoPrime_substPrime
  (P : Formula_)
  (h1 : P.IsTautoPrime)
  (σ : Formula_ → Formula_) :
  (Formula_.substPrime σ P).IsTautoPrime :=
  by
  simp only [Formula_.IsTautoPrime] at h1

  simp only [Formula_.IsTautoPrime]
  intro V
  simp only [evalPrime_substPrime_eq_evalPrime_evalPrime P σ V]
  apply h1


example
  (P Q R S : Formula_)
  (V : VarBoolAssignment)
  (σ : Formula_ → Formula_)
  (h1 : P.evalPrime V ↔ Q.evalPrime V) :
  (S.substPrime (Function.updateITE σ R P)).evalPrime V ↔
    (S.substPrime (Function.updateITE σ R Q)).evalPrime V :=
  by
  simp only [evalPrime_substPrime_eq_evalPrime_evalPrime]
  congr! 1
  funext Q'
  simp only [Function.updateITE]
  split_ifs
  · simp
    exact h1
  · rfl


theorem T_13_5
  (P : Formula_) :
  is_proof_v1 (P.imp_ P) :=
  by
  simp only [is_proof_v1]
  apply is_deduct_v1.mp_ (P.imp_ (P.imp_ P))
  · apply is_deduct_v1.mp_ (P.imp_ ((P.imp_ P).imp_ P))
    · apply is_deduct_v1.axiom_
      exact is_axiom_v1.prop_2_ P (P.imp_ P) P
    · apply is_deduct_v1.axiom_
      exact is_axiom_v1.prop_1_ P (P.imp_ P)
  · apply is_deduct_v1.axiom_
    exact is_axiom_v1.prop_1_ P P

alias prop_id := T_13_5


theorem T_13_6_no_deduct
  (P Q : Formula_) :
  is_proof_v1 (P.not_.imp_ (P.imp_ Q)) :=
  by
  apply is_deduct_v1.mp_ (P.not_.imp_ (Q.not_.imp_ P.not_))
  · apply is_deduct_v1.mp_ (P.not_.imp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)))
    · apply is_deduct_v1.axiom_
      apply is_axiom_v1.prop_2_
    · apply is_deduct_v1.mp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q))
      · apply is_deduct_v1.axiom_
        apply is_axiom_v1.prop_1_
      · apply is_deduct_v1.axiom_
        apply is_axiom_v1.prop_3_
  · apply is_deduct_v1.axiom_
    apply is_axiom_v1.prop_1_


theorem T_14_10
  (F : Formula_)
  (Δ : Set Formula_)
  (h1 : is_deduct_v1 Δ F) :
  ∀ Γ : Set Formula_, is_deduct_v1 (Δ ∪ Γ) F :=
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


theorem T_14_10_comm
  (Q : Formula_)
  (Δ : Set Formula_)
  (h1 : is_deduct_v1 Δ Q) :
  ∀ Γ : Set Formula_, is_deduct_v1 (Γ ∪ Δ) Q :=
  by
  simp only [Set.union_comm]
  exact T_14_10 Q Δ h1


theorem C_14_11
  (P : Formula_)
  (h1 : is_proof_v1 P) :
  ∀ Δ : Set Formula_, is_deduct_v1 Δ P :=
  by
  intro Δ
  obtain s1 := T_14_10 P ∅ h1 Δ
  simp at s1
  exact s1

alias proof_imp_deduct := C_14_11


-- Deduction Theorem
theorem T_14_3
  (P Q : Formula_)
  (Δ : Set Formula_)
  (h1 : is_deduct_v1 (Δ ∪ {P}) Q) :
  is_deduct_v1 Δ (P.imp_ Q) :=
  by
  induction h1
  case axiom_ h1_phi h1_1 =>
    apply is_deduct_v1.mp_ h1_phi
    · apply is_deduct_v1.axiom_
      exact is_axiom_v1.prop_1_ h1_phi P
    · apply is_deduct_v1.axiom_
      exact h1_1
  case assume_ h1_phi h1_1 =>
    simp at h1_1
    cases h1_1
    case inl h1_1 =>
      subst h1_1
      apply proof_imp_deduct
      exact prop_id h1_phi
    case inr h1_1 =>
      apply is_deduct_v1.mp_ h1_phi
      · apply is_deduct_v1.axiom_
        exact is_axiom_v1.prop_1_ h1_phi P
      · apply is_deduct_v1.assume_
        exact h1_1
  case mp_ h1_phi h1_psi _ _ h1_ih_1
    h1_ih_2 =>
    apply is_deduct_v1.mp_ (P.imp_ h1_phi)
    · apply is_deduct_v1.mp_ (P.imp_ (h1_phi.imp_ h1_psi))
      · apply is_deduct_v1.axiom_
        exact is_axiom_v1.prop_2_ P h1_phi h1_psi
      · exact h1_ih_1
    · exact h1_ih_2

alias deduction_theorem := T_14_3


theorem T_13_6
  (P Q : Formula_) :
  is_proof_v1 (P.not_.imp_ (P.imp_ Q)) :=
  by
  simp only [is_proof_v1]
  apply deduction_theorem
  apply is_deduct_v1.mp_ (Q.not_.imp_ P.not_)
  · apply is_deduct_v1.axiom_
    exact is_axiom_v1.prop_3_ Q P
  · apply is_deduct_v1.mp_ P.not_
    · apply is_deduct_v1.axiom_
      exact is_axiom_v1.prop_1_ P.not_ Q.not_
    · apply is_deduct_v1.assume_
      simp


theorem T_14_5
  (P : Formula_) :
  is_proof_v1 (P.not_.not_.imp_ P) :=
  by
  simp only [is_proof_v1]
  apply deduction_theorem
  apply is_deduct_v1.mp_ P.not_.not_
  · apply is_deduct_v1.mp_ (P.not_.imp_ P.not_.not_.not_)
    · apply is_deduct_v1.axiom_
      apply is_axiom_v1.prop_3_
    · apply is_deduct_v1.mp_ P.not_.not_
      · apply proof_imp_deduct
        apply T_13_6
      · apply is_deduct_v1.assume_
        simp
  · apply is_deduct_v1.assume_
    simp


theorem T_14_6
  (P : Formula_) :
  is_proof_v1 (P.imp_ P.not_.not_) :=
  by
  simp only [is_proof_v1]
  apply is_deduct_v1.mp_ (P.not_.not_.not_.imp_ P.not_)
  · apply is_deduct_v1.axiom_
    exact is_axiom_v1.prop_3_ P.not_.not_ P
  · apply proof_imp_deduct
    exact T_14_5 P.not_


theorem T_14_7
  (P Q : Formula_) :
  is_proof_v1 ((P.imp_ Q).imp_ (Q.not_.imp_ P.not_)) :=
  by
  simp only [is_proof_v1]
  apply deduction_theorem
  apply is_deduct_v1.mp_ (P.not_.not_.imp_ Q.not_.not_)
  · apply is_deduct_v1.axiom_
    apply is_axiom_v1.prop_3_
  · apply deduction_theorem
    apply is_deduct_v1.mp_ Q
    · apply proof_imp_deduct
      apply T_14_6
    · apply is_deduct_v1.mp_ P
      · apply is_deduct_v1.assume_
        simp
      · apply is_deduct_v1.mp_ P.not_.not_
        · apply proof_imp_deduct
          apply T_14_5
        · apply is_deduct_v1.assume_
          simp


theorem T_14_8
  (Q R : Formula_) :
  is_proof_v1 (Q.imp_ (R.not_.imp_ (Q.imp_ R).not_)) :=
  by
  simp only [is_proof_v1]
  apply deduction_theorem
  apply is_deduct_v1.mp_ ((Q.imp_ R).imp_ R)
  · apply proof_imp_deduct
    apply T_14_7
  · apply deduction_theorem
    apply is_deduct_v1.mp_ Q
    · apply is_deduct_v1.assume_
      simp
    · apply is_deduct_v1.assume_
      simp


theorem T_14_9
  (P S : Formula_) :
  is_proof_v1 ((S.imp_ P).imp_ ((S.not_.imp_ P).imp_ P)) :=
  by
  simp only [is_proof_v1]
  apply deduction_theorem
  apply is_deduct_v1.mp_ (P.not_.imp_ (S.not_.imp_ P).not_)
  · apply is_deduct_v1.axiom_
    apply is_axiom_v1.prop_3_
  · apply deduction_theorem
    apply is_deduct_v1.mp_ P.not_
    · apply is_deduct_v1.mp_ S.not_
      · apply proof_imp_deduct
        apply T_14_8
      · apply is_deduct_v1.mp_ P.not_
        · apply is_deduct_v1.mp_ (S.imp_ P)
          · apply proof_imp_deduct
            apply T_14_7
          · apply is_deduct_v1.assume_
            simp
        · apply is_deduct_v1.assume_
          simp
    · apply is_deduct_v1.assume_
      simp


theorem deductionTheoremConverse
  (P Q : Formula_)
  (Δ : Set Formula_)
  (h1 : is_deduct_v1 Δ (P.imp_ Q)) :
  is_deduct_v1 (Δ ∪ {P}) Q :=
  by
  apply is_deduct_v1.mp_ P
  · exact T_14_10 (P.imp_ Q) Δ h1 {P}
  · apply is_deduct_v1.assume_
    simp


theorem T_14_12
  (P Q : Formula_)
  (Δ Γ : Set Formula_)
  (h1 : is_deduct_v1 Δ P)
  (h2 : is_deduct_v1 Γ (P.imp_ Q)) :
  is_deduct_v1 (Δ ∪ Γ) Q := by
  apply is_deduct_v1.mp_ P
  · apply T_14_10_comm
    exact h2
  · apply T_14_10
    exact h1


theorem C_14_14
  (P Q : Formula_)
  (Γ : Set Formula_)
  (h1 : is_proof_v1 P)
  (h2 : is_deduct_v1 Γ (P.imp_ Q)) :
  is_deduct_v1 Γ Q := by
  apply is_deduct_v1.mp_ P
  · exact h2
  · apply proof_imp_deduct
    exact h1

alias mp_proof_deduct := C_14_14


theorem C_14_15
  (P Q : Formula_)
  (Δ : Set Formula_)
  (h1 : is_deduct_v1 Δ P)
  (h2 : is_proof_v1 (P.imp_ Q)) :
  is_deduct_v1 Δ Q := by
  apply is_deduct_v1.mp_ P
  · apply proof_imp_deduct
    exact h2
  · exact h1

alias mp_deduct_proof := C_14_15


theorem T_14_16
  (F : Formula_)
  (Δ Γ : Set Formula_)
  (h1 : is_deduct_v1 Γ F)
  (h2 : ∀ H : Formula_, H ∈ Γ → is_deduct_v1 Δ H) :
  is_deduct_v1 Δ F :=
  by
  induction h1
  case axiom_ h1_phi h1_1 =>
    apply is_deduct_v1.axiom_
    exact h1_1
  case assume_ h1_phi h1_1 => exact h2 h1_phi h1_1
  case mp_ h1_phi h1_psi _ _ h1_ih_1 h1_ih_2 =>
    exact is_deduct_v1.mp_ h1_phi h1_psi h1_ih_1 h1_ih_2


theorem C_14_17
  (Q : Formula_)
  (Γ : Set Formula_)
  (h1 : is_deduct_v1 Γ Q)
  (h2 : ∀ P : Formula_, P ∈ Γ → is_proof_v1 P) :
  is_proof_v1 Q :=
  by
  simp only [is_proof_v1] at h2

  simp only [is_proof_v1]
  exact T_14_16 Q ∅ Γ h1 h2


theorem eval_not
  (P : Formula_)
  (V : VarBoolAssignment) :
  Formula_.evalPrime V (not_ P) ↔
    ¬ Formula_.evalPrime V P :=
  by
  simp only [Formula_.evalPrime]


theorem eval_imp
  (P Q : Formula_)
  (V : VarBoolAssignment) :
  Formula_.evalPrime V (imp_ P Q) ↔
    (Formula_.evalPrime V P → Formula_.evalPrime V Q) :=
  by
  simp only [Formula_.evalPrime]


theorem eval_false
  (V : VarBoolAssignment) :
  Formula_.evalPrime V false_ ↔
    False :=
  by
  simp only [Formula_.evalPrime]


theorem eval_and
  (P Q : Formula_)
  (V : VarBoolAssignment) :
  Formula_.evalPrime V (and_ P Q) ↔
    (Formula_.evalPrime V P ∧ Formula_.evalPrime V Q) :=
  by
  simp only [Formula_.evalPrime]


theorem eval_or
  (P Q : Formula_)
  (V : VarBoolAssignment) :
  Formula_.evalPrime V (or_ P Q) ↔
    (Formula_.evalPrime V P ∨ Formula_.evalPrime V Q) :=
  by
  simp only [Formula_.evalPrime]


theorem eval_iff
  (P Q : Formula_)
  (V : VarBoolAssignment) :
  Formula_.evalPrime V (iff_ P Q) ↔
    (Formula_.evalPrime V P ↔ Formula_.evalPrime V Q) :=
  by
  simp only [Formula_.evalPrime]


theorem is_tauto_prop_true :
  true_.IsTautoPrime :=
  by
  simp only [Formula_.IsTautoPrime]
  simp only [Formula_.evalPrime]
  simp


theorem is_tauto_prop_1
  (P Q : Formula_) :
  (P.imp_ (Q.imp_ P)).IsTautoPrime :=
  by
  simp only [Formula_.IsTautoPrime]
  tauto


theorem is_tauto_prop_2
  (P Q R : Formula_) :
  ((P.imp_ (Q.imp_ R)).imp_ ((P.imp_ Q).imp_ (P.imp_ R))).IsTautoPrime :=
  by
  simp only [Formula_.IsTautoPrime]
  tauto


theorem is_tauto_prop_3
  (P Q : Formula_) :
  (((not_ P).imp_ (not_ Q)).imp_ (Q.imp_ P)).IsTautoPrime :=
  by
  simp only [Formula_.IsTautoPrime]
  simp only [eval_not, eval_imp]
  tauto


theorem is_tauto_mp
  (P Q : Formula_)
  (h1 : (P.imp_ Q).IsTautoPrime)
  (h2 : P.IsTautoPrime) :
  Q.IsTautoPrime :=
  by
  simp only [Formula_.IsTautoPrime] at h1
  simp only [eval_imp] at h1

  simp only [Formula_.IsTautoPrime] at h2

  tauto


theorem is_tauto_def_false :
  (false_.iff_ (not_ true_)).IsTautoPrime :=
  by
  simp only [Formula_.IsTautoPrime]
  simp only [eval_not, eval_iff]
  tauto

theorem is_tauto_def_and
  (P Q : Formula_) :
  ((P.and_ Q).iff_ (not_ (P.imp_ (not_ Q)))).IsTautoPrime :=
  by
  simp only [Formula_.IsTautoPrime]
  simp only [eval_and, eval_not, eval_imp, eval_iff]
  tauto

theorem is_tauto_def_or
  (P Q : Formula_) :
  ((P.or_ Q).iff_ ((not_ P).imp_ Q)).IsTautoPrime :=
  by
  simp only [Formula_.IsTautoPrime]
  simp only [eval_or, eval_not, eval_imp, eval_iff]
  tauto

theorem is_tauto_def_iff
  (P Q : Formula_) :
  (not_ (((P.iff_ Q).imp_ (not_ ((P.imp_ Q).imp_ (not_ (Q.imp_ P))))).imp_ (not_ ((not_ ((P.imp_ Q).imp_ (not_ (Q.imp_ P)))).imp_ (P.iff_ Q))))).IsTautoPrime :=
  by
  simp only [Formula_.IsTautoPrime]
  simp only [eval_iff, eval_not, eval_imp]
  tauto


/-
  Proof of the soundness of classical propositional logic.
-/
example
  (F : Formula_)
  (h1 : is_prop_proof F) :
  F.IsTautoPrime :=
  by
  induction h1
  case axiom_ h1_phi h1_1 =>
    induction h1_1
    case prop_true_ =>
      exact is_tauto_prop_true
    case prop_1_ h1_1_phi h1_1_psi =>
      exact is_tauto_prop_1 h1_1_phi h1_1_psi
    case prop_2_ h1_1_phi h1_1_psi h1_1_chi =>
      exact is_tauto_prop_2 h1_1_phi h1_1_psi h1_1_chi
    case prop_3_ h1_1_phi h1_1_psi =>
      exact is_tauto_prop_3 h1_1_phi h1_1_psi
    case def_false_ =>
      exact is_tauto_def_false
    case def_and_ h1_1_phi h1_1_psi =>
      exact is_tauto_def_and h1_1_phi h1_1_psi
    case def_or_ h1_1_phi h1_1_psi =>
      exact is_tauto_def_or h1_1_phi h1_1_psi
    case def_iff_ h1_1_phi h1_1_psi =>
      exact is_tauto_def_iff h1_1_phi h1_1_psi
  case assume_ h1_phi h1_1 =>
    simp at h1_1
  case mp_ h1_phi h1_psi _ _ h1_ih_1 h1_ih_2 =>
    exact is_tauto_mp h1_phi h1_psi h1_ih_1 h1_ih_2


theorem mem_prime_set_isPrime
  (F F' : Formula_)
  (h1 : F' ∈ F.prime_set) :
  F'.is_prime :=
  by
  induction F
  case pred_const_ | pred_var_ =>
    simp only [Formula_.prime_set] at h1
    simp at h1
    subst h1
    simp only [Formula_.is_prime]
  case true_ | false_ =>
    simp only [Formula_.prime_set] at h1
    simp at h1
  case eq_ x y =>
    simp only [Formula_.prime_set] at h1
    simp at h1
    subst h1
    simp only [Formula_.is_prime]
  case not_ phi phi_ih =>
    simp only [Formula_.prime_set] at h1
    exact phi_ih h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [Formula_.prime_set] at h1
    simp at h1
    tauto
  case forall_ x phi | exists_ x phi =>
    simp only [Formula_.prime_set] at h1
    simp at h1
    subst h1
    simp only [Formula_.is_prime]
  case def_ =>
    simp only [Formula_.prime_set] at h1
    simp at h1
    subst h1
    simp only [Formula_.is_prime]


theorem L_15_7
  (F F' : Formula_)
  (Δ_U : Set Formula_)
  (V : VarBoolAssignment)
  (Δ_U' : Set Formula_)
  (h1 : F.prime_set.toSet ⊆ Δ_U)
  (h2 : Δ_U' = Δ_U.image (evalPrimeFfToNot V))
  (h3 : F' = evalPrimeFfToNot V F) :
  is_deduct_v1 Δ_U' F' :=
  by
  subst h2
  subst h3
  induction F
  case pred_const_ X xs =>
    let F := pred_const_ X xs
    simp only [Formula_.prime_set] at h1
    simp at h1

    simp only [evalPrimeFfToNot]
    simp only [Formula_.evalPrime]
    apply is_deduct_v1.assume_
    simp
    apply Exists.intro F
    tauto
  case pred_var_ X xs =>
    let F := pred_var_ X xs
    simp only [Formula_.prime_set] at h1
    simp at h1

    simp only [evalPrimeFfToNot]
    simp only [Formula_.evalPrime]
    apply is_deduct_v1.assume_
    simp
    apply Exists.intro F
    tauto
  case eq_ x y =>
    let F := eq_ x y
    simp only [Formula_.prime_set] at h1
    simp at h1

    simp only [evalPrimeFfToNot]
    simp only [Formula_.evalPrime]
    apply is_deduct_v1.assume_
    simp
    apply Exists.intro F
    tauto
  case true_ =>
    apply is_deduct_v1.axiom_
    apply is_axiom_v1.prop_true_
  case false_ =>
    simp only [Formula_.prime_set] at h1
    simp at h1

    simp only [evalPrimeFfToNot]
    simp only [Formula_.evalPrime]
    simp
    sorry
  case not_ phi phi_ih =>
    simp only [Formula_.prime_set] at h1

    simp only [evalPrimeFfToNot] at phi_ih

    simp only [evalPrimeFfToNot]
    simp only [evalPrime]
    simp
    split_ifs
    case _ c1 =>
      simp only [c1] at phi_ih
      simp at phi_ih
      apply is_deduct_v1.mp_ phi
      apply proof_imp_deduct
      apply T_14_6
      exact phi_ih h1
    case _ c1 =>
      simp only [c1] at phi_ih
      simp at phi_ih
      exact phi_ih h1
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula_.prime_set] at h1
    simp at h1

    simp only [evalPrimeFfToNot] at phi_ih
    simp only [evalPrimeFfToNot] at psi_ih

    simp only [evalPrimeFfToNot]

    cases h1
    case intro h1_left h1_right =>
      split_ifs
      case _ c1 =>
        simp only [evalPrime] at c1
        simp only [imp_iff_not_or] at c1
        cases c1
        case _ c1 =>
          simp only [if_neg c1] at phi_ih
          apply is_deduct_v1.mp_ (not_ phi)
          apply proof_imp_deduct
          apply T_13_6
          apply phi_ih h1_left
        case _ c1 =>
          simp only [if_pos c1] at psi_ih
          apply is_deduct_v1.mp_ psi
          apply is_deduct_v1.axiom_
          apply is_axiom_v1.prop_1_
          apply psi_ih
          exact h1_right
      case _ c1 =>
        simp only [evalPrime] at c1
        simp at c1
        cases c1
        case intro c1_left c1_right =>
          simp only [if_pos c1_left] at phi_ih
          simp only [if_neg c1_right] at psi_ih
          apply is_deduct_v1.mp_ psi.not_
          · apply is_deduct_v1.mp_ phi
            · apply proof_imp_deduct
              apply T_14_8
            · exact phi_ih h1_left
          · exact psi_ih h1_right
  case forall_ x phi phi_ih =>
    let F := forall_ x phi

    simp only [Formula_.prime_set] at h1
    simp at h1

    simp only [evalPrimeFfToNot]
    simp only [Formula_.evalPrime]
    apply is_deduct_v1.assume_
    simp
    apply Exists.intro F
    tauto
  case def_ X xs =>
    let F := def_ X xs
    simp only [Formula_.prime_set] at h1
    simp at h1

    simp only [evalPrimeFfToNot]
    simp only [Formula_.evalPrime]
    apply is_deduct_v1.assume_
    simp
    apply Exists.intro F
    tauto
  case and_ | or_ | iff_ | exists_ =>
    sorry


theorem T_14_9_Deduct
  (P U : Formula_)
  (Δ : Set Formula_)
  (h1 : is_deduct_v1 (Δ ∪ {U}) P)
  (h2 : is_deduct_v1 (Δ ∪ {U.not_}) P) :
  is_deduct_v1 Δ P :=
  by
  apply is_deduct_v1.mp_ (U.not_.imp_ P)
  · apply is_deduct_v1.mp_ (U.imp_ P)
    · apply proof_imp_deduct
      apply T_14_9
    · apply deduction_theorem
      exact h1
  · apply deduction_theorem
    exact h2


theorem evalPrimeFfToNot_of_function_updateIte_true
  (F F' : Formula_)
  (V : VarBoolAssignment)
  (h1 : F.is_prime) :
  evalPrimeFfToNot (Function.updateITE V F' true) F =
    Function.updateITE (evalPrimeFfToNot V) F' F F :=
  by
  induction F
  case pred_const_ | pred_var_ | eq_ | forall_ | exists_ | def_ =>
    unfold Function.updateITE
    simp only [evalPrimeFfToNot]
    simp only [Formula_.evalPrime]
    split_ifs <;> tauto
  case true_ | false_ | not_ | imp_ | and_ | or_ | iff_ =>
    simp only [Formula_.is_prime] at h1


theorem evalPrimeFfToNot_of_function_updateIte_false
  (F F' : Formula_)
  (V : VarBoolAssignment)
  (h1 : F.is_prime) :
  evalPrimeFfToNot (Function.updateITE V F' false) F =
    Function.updateITE (evalPrimeFfToNot V) F' F.not_ F :=
  by
  induction F
  case pred_const_ | pred_var_ | eq_ | forall_ | exists_ | def_ =>
    unfold Function.updateITE
    simp only [evalPrimeFfToNot]
    simp only [Formula_.evalPrime]
    split_ifs <;> tauto
  case true_ | false_ | not_ | imp_ | and_ | or_ | iff_ =>
    simp only [Formula_.is_prime] at h1


theorem image_of_evalPrimeFfToNot_of_function_updateIte
  (U : Formula_)
  (Δ : Set Formula_)
  (V : VarBoolAssignment)
  (b : Bool)
  (h1_Δ : ∀ U' : Formula_, U' ∈ Δ → U'.is_prime)
  (h1_U : U.is_prime)
  (h2 : U ∉ Δ) :
  Δ.image (evalPrimeFfToNot (Function.updateITE V U b)) =
    Δ.image (evalPrimeFfToNot V) :=
  by
  apply Set.image_congr
  intro U' a1
  specialize h1_Δ U' a1
  cases b
  · simp only [evalPrimeFfToNot_of_function_updateIte_false U' U V h1_Δ]
    simp only [Function.updateITE]
    simp
    intro a2
    subst a2
    contradiction
  · simp only [evalPrimeFfToNot_of_function_updateIte_true U' U V h1_Δ]
    simp only [Function.updateITE]
    simp
    intro a2
    subst a2
    contradiction


theorem propCompleteAuxAux
  (P U : Formula_)
  (Δ : Set Formula_)
  (h1_Δ : ∀ U' : Formula_, U' ∈ Δ → U'.is_prime)
  (h1_U : U.is_prime)
  (h2 : U ∉ Δ)
  (h3 : ∀ V : VarBoolAssignment, is_deduct_v1 (Δ.image (evalPrimeFfToNot V) ∪ {evalPrimeFfToNot V U}) P) :
  ∀ V : VarBoolAssignment, is_deduct_v1 (Δ.image (evalPrimeFfToNot V)) P :=
  by
  intro V
  apply T_14_9_Deduct P U (Δ.image (evalPrimeFfToNot V))
  · specialize h3 (Function.updateITE V U true)
    simp only [image_of_evalPrimeFfToNot_of_function_updateIte U Δ V true h1_Δ h1_U h2] at h3
    simp only [evalPrimeFfToNot_of_function_updateIte_true U U V h1_U] at h3
    simp only [Function.updateITE] at h3
    simp only [eq_self_iff_true, if_true] at h3
    exact h3
  · specialize h3 (Function.updateITE V U Bool.false)
    simp only [image_of_evalPrimeFfToNot_of_function_updateIte U Δ V false h1_Δ h1_U h2] at h3
    simp only [evalPrimeFfToNot_of_function_updateIte_false U U V h1_U] at h3
    simp only [Function.updateITE] at h3
    simp only [eq_self_iff_true, if_true] at h3
    exact h3


theorem propCompleteAux
  (P : Formula_)
  (Δ_U : Finset Formula_)
  (h1 : Δ_U ⊆ P.prime_set)
  (h2 : ∀ V : VarBoolAssignment, is_deduct_v1 (Δ_U.image (evalPrimeFfToNot V)) P) :
  is_deduct_v1 ∅ P :=
  by
  induction Δ_U using Finset.induction_on
  case empty =>
    simp at h2
    exact h2
  case insert U Δ_U Δ_U_1 Δ_U_2 =>
    apply Δ_U_2
    · simp only [Finset.insert_subset_iff] at h1
      cases h1
      case intro h1_left h1_right =>
        exact h1_right
    · simp only [Finset.insert_subset_iff] at h1

      simp at h2

      cases h1
      case intro h1_left h1_right =>
        simp
        apply propCompleteAuxAux P U Δ_U
        · intro U' a1
          apply mem_prime_set_isPrime P U'
          apply h1_right
          exact a1
        · apply mem_prime_set_isPrime P U
          exact h1_left
        · exact Δ_U_1
        · simp
          exact h2


/-
  Proof of the completeness of classical propositional logic.
-/
theorem prop_complete
  (P : Formula_)
  (h1 : P.IsTautoPrime) :
  is_proof_v1 P :=
  by
  simp only [is_proof_v1]
  apply propCompleteAux P P.prime_set
  · rfl
  · intro V
    apply L_15_7 P P P.prime_set V (P.prime_set.image (evalPrimeFfToNot V))
    · rfl
    · simp only [Finset.coe_image]
    · simp only [Formula_.IsTautoPrime] at h1
      simp only [evalPrimeFfToNot]
      specialize h1 V
      simp only [if_pos h1]


macro "SC" : tactic => `(tactic|(
  apply proof_imp_deduct
  apply prop_complete
  simp only [Formula_.IsTautoPrime]
  simp only [eval_not, eval_imp]
  tauto))


--#lint
