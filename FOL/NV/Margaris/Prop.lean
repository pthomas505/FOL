import MathlibExtra.FunctionUpdateITE
import FOL.NV.Margaris.Deduct


set_option autoImplicit false


namespace FOL.NV

open Formula

open Margaris


axiom def_false_ : false_ = not_ true_

/--
  phi ∨ psi := ¬ phi → psi
-/
axiom def_or_ (phi psi : Formula) : or_ phi psi = (not_ phi).imp_ psi

/--
phi ∧ psi := ¬ ( phi → ¬ psi )
-/
axiom def_and_ (phi psi : Formula) : and_ phi psi = not_ (phi.imp_ (not_ psi))

/--
  phi ↔ psi := ( phi → psi ) ∧ ( psi → phi )
-/
axiom def_iff_ (phi psi : Formula) : iff_ phi psi = (phi.imp_ psi).and_ (psi.imp_ phi)

/--
  ∃ x phi := ¬ ∀ x ¬ phi
-/
axiom def_exists_ (x : VarName) (phi : Formula) : exists_ x phi = not_ (forall_ x (not_ phi))

def def_eq_ (x y : VarName) : Formula :=
  pred_const_ (PredName.mk "=") [x, y]


/--
  Used for the soundness and completeness proofs of classical propositional logic.
-/
def Formula.IsPrime : Formula → Prop
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


def Formula.primeSet : Formula → Finset Formula
  | pred_const_ X xs => {pred_const_ X xs}
  | pred_var_ X xs => {pred_var_ X xs}
  | eq_ x y => {eq_ x y}
  | true_ => ∅
  | false_ => ∅
  | not_ phi => phi.primeSet
  | imp_ phi psi => phi.primeSet ∪ psi.primeSet
  | and_ phi psi => phi.primeSet ∪ psi.primeSet
  | or_ phi psi => phi.primeSet ∪ psi.primeSet
  | iff_ phi psi => phi.primeSet ∪ psi.primeSet
  | forall_ x phi => {forall_ x phi}
  | exists_ x phi => {exists_ x phi}
  | def_ X xs => {def_ X xs}


def Formula.substPrime (σ : Formula → Formula) : Formula → Formula
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


def VarBoolAssignment := Formula → Bool
  deriving Inhabited


def Formula.evalPrime (V : VarBoolAssignment) : Formula → Prop
  | pred_const_ X xs => V (pred_const_ X xs)
  | pred_var_ X xs => V (pred_var_ X xs)
  | eq_ x y => V (eq_ x y)
  | true_ => True
  | false_ => False
  | not_ phi => ¬ Formula.evalPrime V phi
  | imp_ phi psi => Formula.evalPrime V phi → Formula.evalPrime V psi
  | and_ phi psi => Formula.evalPrime V phi ∧ Formula.evalPrime V psi
  | or_ phi psi => Formula.evalPrime V phi ∨ Formula.evalPrime V psi
  | iff_ phi psi => Formula.evalPrime V phi ↔ Formula.evalPrime V psi
  | forall_ x phi => V (forall_ x phi)
  | exists_ x phi => V (exists_ x phi)
  | def_ X xs => V (def_ X xs)


instance
  (V : VarBoolAssignment)
  (F : Formula) :
  Decidable (Formula.evalPrime V F) :=
  by
  induction F generalizing V
  all_goals
    simp only [Formula.evalPrime]
    infer_instance


def Formula.IsTautoPrime (P : Formula) : Prop :=
  ∀ V : VarBoolAssignment, P.evalPrime V


def evalPrimeFfToNot
  (V : VarBoolAssignment)
  (P : Formula) :
  Formula :=
  if Formula.evalPrime V P
  then P
  else P.not_


theorem evalPrime_prime
  (F : Formula)
  (V : VarBoolAssignment)
  (h1 : F.IsPrime) :
  F.evalPrime V = V F :=
  by
  induction F
  case true_ | false_ | not_ | imp_ | and_ | or_ | iff_ =>
    simp only [Formula.IsPrime] at h1
  case pred_const_ | pred_var_ | eq_ | forall_ | exists_ | def_ =>
    rfl


example
  (F : Formula)
  (V V' : VarBoolAssignment)
  (h1 : ∀ H : Formula, H ∈ F.primeSet → V H = V' H) :
  F.evalPrime V ↔ F.evalPrime V' :=
  by
  induction F
  case pred_const_ | pred_var_ | eq_ | forall_ | exists_ | def_ =>
    simp only [Formula.primeSet] at h1

    simp only [Formula.evalPrime]
    congr! 1
    apply h1
    simp
  case true_ | false_ =>
    simp only [Formula.evalPrime]
  case not_ phi phi_ih =>
    simp only [Formula.primeSet] at h1

    simp only [Formula.evalPrime]
    congr! 1
    exact phi_ih h1
  case
    imp_ phi psi phi_ih psi_ih
  | and_ phi psi phi_ih psi_ih
  | or_ phi psi phi_ih psi_ih
  | iff_ phi psi phi_ih psi_ih =>
    simp only [Formula.primeSet] at h1
    simp at h1

    simp only [Formula.evalPrime]
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
  (F : Formula)
  (σ : Formula → Formula)
  (V : VarBoolAssignment) :
  (F.substPrime σ).evalPrime V ↔
    F.evalPrime fun H : Formula => (σ H).evalPrime V :=
  by
  induction F
  case pred_const_ | pred_var_ | eq_ | forall_ | exists_ | def_ =>
    simp only [Formula.substPrime]
    simp only [Formula.evalPrime]
    simp
  case true_ | false_ =>
    rfl
  case not_ phi phi_ih =>
    simp only [Formula.substPrime]
    simp only [Formula.evalPrime]
    congr! 1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [Formula.substPrime]
    simp only [Formula.evalPrime]
    congr! 1


theorem isTautoPrime_imp_isTautoPrime_substPrime
  (P : Formula)
  (h1 : P.IsTautoPrime)
  (σ : Formula → Formula) :
  (Formula.substPrime σ P).IsTautoPrime :=
  by
  simp only [Formula.IsTautoPrime] at h1

  simp only [Formula.IsTautoPrime]
  intro V
  simp only [evalPrime_substPrime_eq_evalPrime_evalPrime P σ V]
  apply h1


example
  (P Q R S : Formula)
  (V : VarBoolAssignment)
  (σ : Formula → Formula)
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
  (P : Formula) :
  IsProof (P.imp_ P) :=
  by
  simp only [IsProof]
  apply IsDeduct.mp_ (P.imp_ (P.imp_ P))
  · apply IsDeduct.mp_ (P.imp_ ((P.imp_ P).imp_ P))
    · apply IsDeduct.axiom_
      exact IsAxiom.prop_2_ P (P.imp_ P) P
    · apply IsDeduct.axiom_
      exact IsAxiom.prop_1_ P (P.imp_ P)
  · apply IsDeduct.axiom_
    exact IsAxiom.prop_1_ P P

alias prop_id := T_13_5


theorem T_13_6_no_deduct
  (P Q : Formula) :
  IsProof (P.not_.imp_ (P.imp_ Q)) :=
  by
  apply IsDeduct.mp_ (P.not_.imp_ (Q.not_.imp_ P.not_))
  · apply IsDeduct.mp_ (P.not_.imp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)))
    · apply IsDeduct.axiom_
      apply IsAxiom.prop_2_
    · apply IsDeduct.mp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q))
      · apply IsDeduct.axiom_
        apply IsAxiom.prop_1_
      · apply IsDeduct.axiom_
        apply IsAxiom.prop_3_
  · apply IsDeduct.axiom_
    apply IsAxiom.prop_1_


theorem T_14_10
  (F : Formula)
  (Δ : Set Formula)
  (h1 : IsDeduct Δ F) :
  ∀ Γ : Set Formula, IsDeduct (Δ ∪ Γ) F :=
  by
  intro Γ
  induction h1
  case axiom_ h1_phi h1_1 =>
    apply IsDeduct.axiom_
    exact h1_1
  case assume_ h1_phi h1_1 =>
    apply IsDeduct.assume_
    simp
    left
    exact h1_1
  case mp_ h1_phi h1_psi _ _ h1_ih_1 h1_ih_2 =>
    apply IsDeduct.mp_ h1_phi
    · exact h1_ih_1
    · exact h1_ih_2


theorem T_14_10_comm
  (Q : Formula)
  (Δ : Set Formula)
  (h1 : IsDeduct Δ Q) :
  ∀ Γ : Set Formula, IsDeduct (Γ ∪ Δ) Q :=
  by
  simp only [Set.union_comm]
  exact T_14_10 Q Δ h1


theorem C_14_11
  (P : Formula)
  (h1 : IsProof P) :
  ∀ Δ : Set Formula, IsDeduct Δ P :=
  by
  intro Δ
  obtain s1 := T_14_10 P ∅ h1 Δ
  simp at s1
  exact s1

alias proof_imp_deduct := C_14_11


-- Deduction Theorem
theorem T_14_3
  (P Q : Formula)
  (Δ : Set Formula)
  (h1 : IsDeduct (Δ ∪ {P}) Q) :
  IsDeduct Δ (P.imp_ Q) :=
  by
  induction h1
  case axiom_ h1_phi h1_1 =>
    apply IsDeduct.mp_ h1_phi
    · apply IsDeduct.axiom_
      exact IsAxiom.prop_1_ h1_phi P
    · apply IsDeduct.axiom_
      exact h1_1
  case assume_ h1_phi h1_1 =>
    simp at h1_1
    cases h1_1
    case inl h1_1 =>
      subst h1_1
      apply proof_imp_deduct
      exact prop_id h1_phi
    case inr h1_1 =>
      apply IsDeduct.mp_ h1_phi
      · apply IsDeduct.axiom_
        exact IsAxiom.prop_1_ h1_phi P
      · apply IsDeduct.assume_
        exact h1_1
  case mp_ h1_phi h1_psi _ _ h1_ih_1
    h1_ih_2 =>
    apply IsDeduct.mp_ (P.imp_ h1_phi)
    · apply IsDeduct.mp_ (P.imp_ (h1_phi.imp_ h1_psi))
      · apply IsDeduct.axiom_
        exact IsAxiom.prop_2_ P h1_phi h1_psi
      · exact h1_ih_1
    · exact h1_ih_2

alias deduction_theorem := T_14_3


theorem T_13_6
  (P Q : Formula) :
  IsProof (P.not_.imp_ (P.imp_ Q)) :=
  by
  simp only [IsProof]
  apply deduction_theorem
  apply IsDeduct.mp_ (Q.not_.imp_ P.not_)
  · apply IsDeduct.axiom_
    exact IsAxiom.prop_3_ Q P
  · apply IsDeduct.mp_ P.not_
    · apply IsDeduct.axiom_
      exact IsAxiom.prop_1_ P.not_ Q.not_
    · apply IsDeduct.assume_
      simp


theorem T_14_5
  (P : Formula) :
  IsProof (P.not_.not_.imp_ P) :=
  by
  simp only [IsProof]
  apply deduction_theorem
  apply IsDeduct.mp_ P.not_.not_
  · apply IsDeduct.mp_ (P.not_.imp_ P.not_.not_.not_)
    · apply IsDeduct.axiom_
      apply IsAxiom.prop_3_
    · apply IsDeduct.mp_ P.not_.not_
      · apply proof_imp_deduct
        apply T_13_6
      · apply IsDeduct.assume_
        simp
  · apply IsDeduct.assume_
    simp


theorem T_14_6
  (P : Formula) :
  IsProof (P.imp_ P.not_.not_) :=
  by
  simp only [IsProof]
  apply IsDeduct.mp_ (P.not_.not_.not_.imp_ P.not_)
  · apply IsDeduct.axiom_
    exact IsAxiom.prop_3_ P.not_.not_ P
  · apply proof_imp_deduct
    exact T_14_5 P.not_


theorem T_14_7
  (P Q : Formula) :
  IsProof ((P.imp_ Q).imp_ (Q.not_.imp_ P.not_)) :=
  by
  simp only [IsProof]
  apply deduction_theorem
  apply IsDeduct.mp_ (P.not_.not_.imp_ Q.not_.not_)
  · apply IsDeduct.axiom_
    apply IsAxiom.prop_3_
  · apply deduction_theorem
    apply IsDeduct.mp_ Q
    · apply proof_imp_deduct
      apply T_14_6
    · apply IsDeduct.mp_ P
      · apply IsDeduct.assume_
        simp
      · apply IsDeduct.mp_ P.not_.not_
        · apply proof_imp_deduct
          apply T_14_5
        · apply IsDeduct.assume_
          simp


theorem T_14_8
  (Q R : Formula) :
  IsProof (Q.imp_ (R.not_.imp_ (Q.imp_ R).not_)) :=
  by
  simp only [IsProof]
  apply deduction_theorem
  apply IsDeduct.mp_ ((Q.imp_ R).imp_ R)
  · apply proof_imp_deduct
    apply T_14_7
  · apply deduction_theorem
    apply IsDeduct.mp_ Q
    · apply IsDeduct.assume_
      simp
    · apply IsDeduct.assume_
      simp


theorem T_14_9
  (P S : Formula) :
  IsProof ((S.imp_ P).imp_ ((S.not_.imp_ P).imp_ P)) :=
  by
  simp only [IsProof]
  apply deduction_theorem
  apply IsDeduct.mp_ (P.not_.imp_ (S.not_.imp_ P).not_)
  · apply IsDeduct.axiom_
    apply IsAxiom.prop_3_
  · apply deduction_theorem
    apply IsDeduct.mp_ P.not_
    · apply IsDeduct.mp_ S.not_
      · apply proof_imp_deduct
        apply T_14_8
      · apply IsDeduct.mp_ P.not_
        · apply IsDeduct.mp_ (S.imp_ P)
          · apply proof_imp_deduct
            apply T_14_7
          · apply IsDeduct.assume_
            simp
        · apply IsDeduct.assume_
          simp
    · apply IsDeduct.assume_
      simp


theorem deductionTheoremConverse
  (P Q : Formula)
  (Δ : Set Formula)
  (h1 : IsDeduct Δ (P.imp_ Q)) :
  IsDeduct (Δ ∪ {P}) Q :=
  by
  apply IsDeduct.mp_ P
  · exact T_14_10 (P.imp_ Q) Δ h1 {P}
  · apply IsDeduct.assume_
    simp


theorem T_14_12
  (P Q : Formula)
  (Δ Γ : Set Formula)
  (h1 : IsDeduct Δ P)
  (h2 : IsDeduct Γ (P.imp_ Q)) :
  IsDeduct (Δ ∪ Γ) Q := by
  apply IsDeduct.mp_ P
  · apply T_14_10_comm
    exact h2
  · apply T_14_10
    exact h1


theorem C_14_14
  (P Q : Formula)
  (Γ : Set Formula)
  (h1 : IsProof P)
  (h2 : IsDeduct Γ (P.imp_ Q)) :
  IsDeduct Γ Q := by
  apply IsDeduct.mp_ P
  · exact h2
  · apply proof_imp_deduct
    exact h1

alias mp_proof_deduct := C_14_14


theorem C_14_15
  (P Q : Formula)
  (Δ : Set Formula)
  (h1 : IsDeduct Δ P)
  (h2 : IsProof (P.imp_ Q)) :
  IsDeduct Δ Q := by
  apply IsDeduct.mp_ P
  · apply proof_imp_deduct
    exact h2
  · exact h1

alias mp_deduct_proof := C_14_15


theorem T_14_16
  (F : Formula)
  (Δ Γ : Set Formula)
  (h1 : IsDeduct Γ F)
  (h2 : ∀ H : Formula, H ∈ Γ → IsDeduct Δ H) :
  IsDeduct Δ F :=
  by
  induction h1
  case axiom_ h1_phi h1_1 =>
    apply IsDeduct.axiom_
    exact h1_1
  case assume_ h1_phi h1_1 => exact h2 h1_phi h1_1
  case mp_ h1_phi h1_psi _ _ h1_ih_1 h1_ih_2 =>
    exact IsDeduct.mp_ h1_phi h1_psi h1_ih_1 h1_ih_2


theorem C_14_17
  (Q : Formula)
  (Γ : Set Formula)
  (h1 : IsDeduct Γ Q)
  (h2 : ∀ P : Formula, P ∈ Γ → IsProof P) :
  IsProof Q :=
  by
  simp only [IsProof] at h2

  simp only [IsProof]
  exact T_14_16 Q ∅ Γ h1 h2


theorem eval_not
  (P : Formula)
  (V : VarBoolAssignment) :
  Formula.evalPrime V (not_ P) ↔
    ¬ Formula.evalPrime V P :=
  by
  simp only [Formula.evalPrime]


theorem eval_imp
  (P Q : Formula)
  (V : VarBoolAssignment) :
  Formula.evalPrime V (imp_ P Q) ↔
    (Formula.evalPrime V P → Formula.evalPrime V Q) :=
  by
  simp only [Formula.evalPrime]


theorem eval_false
  (V : VarBoolAssignment) :
  Formula.evalPrime V false_ ↔
    False :=
  by
  simp only [Formula.evalPrime]


theorem eval_and
  (P Q : Formula)
  (V : VarBoolAssignment) :
  Formula.evalPrime V (and_ P Q) ↔
    (Formula.evalPrime V P ∧ Formula.evalPrime V Q) :=
  by
  simp only [Formula.evalPrime]


theorem eval_or
  (P Q : Formula)
  (V : VarBoolAssignment) :
  Formula.evalPrime V (or_ P Q) ↔
    (Formula.evalPrime V P ∨ Formula.evalPrime V Q) :=
  by
  simp only [Formula.evalPrime]


theorem eval_iff
  (P Q : Formula)
  (V : VarBoolAssignment) :
  Formula.evalPrime V (iff_ P Q) ↔
    (Formula.evalPrime V P ↔ Formula.evalPrime V Q) :=
  by
  simp only [Formula.evalPrime]


theorem is_tauto_prop_true :
  true_.IsTautoPrime :=
  by
  simp only [Formula.IsTautoPrime]
  simp only [Formula.evalPrime]
  simp


theorem is_tauto_prop_1
  (P Q : Formula) :
  (P.imp_ (Q.imp_ P)).IsTautoPrime :=
  by
  simp only [Formula.IsTautoPrime]
  tauto


theorem is_tauto_prop_2
  (P Q R : Formula) :
  ((P.imp_ (Q.imp_ R)).imp_ ((P.imp_ Q).imp_ (P.imp_ R))).IsTautoPrime :=
  by
  simp only [Formula.IsTautoPrime]
  tauto


theorem is_tauto_prop_3
  (P Q : Formula) :
  (((not_ P).imp_ (not_ Q)).imp_ (Q.imp_ P)).IsTautoPrime :=
  by
  simp only [Formula.IsTautoPrime]
  simp only [eval_not, eval_imp]
  tauto


theorem is_tauto_mp
  (P Q : Formula)
  (h1 : (P.imp_ Q).IsTautoPrime)
  (h2 : P.IsTautoPrime) :
  Q.IsTautoPrime :=
  by
  simp only [Formula.IsTautoPrime] at h1
  simp only [eval_imp] at h1

  simp only [Formula.IsTautoPrime] at h2

  tauto


theorem is_tauto_def_false :
  (false_.iff_ (not_ true_)).IsTautoPrime :=
  by
  simp only [Formula.IsTautoPrime]
  simp only [eval_not, eval_iff]
  tauto

theorem is_tauto_def_and
  (P Q : Formula) :
  ((P.and_ Q).iff_ (not_ (P.imp_ (not_ Q)))).IsTautoPrime :=
  by
  simp only [Formula.IsTautoPrime]
  simp only [eval_and, eval_not, eval_imp, eval_iff]
  tauto

theorem is_tauto_def_or
  (P Q : Formula) :
  ((P.or_ Q).iff_ ((not_ P).imp_ Q)).IsTautoPrime :=
  by
  simp only [Formula.IsTautoPrime]
  simp only [eval_or, eval_not, eval_imp, eval_iff]
  tauto

theorem is_tauto_def_iff
  (P Q : Formula) :
  (not_ (((P.iff_ Q).imp_ (not_ ((P.imp_ Q).imp_ (not_ (Q.imp_ P))))).imp_ (not_ ((not_ ((P.imp_ Q).imp_ (not_ (Q.imp_ P)))).imp_ (P.iff_ Q))))).IsTautoPrime :=
  by
  simp only [Formula.IsTautoPrime]
  simp only [eval_iff, eval_not, eval_imp]
  tauto


/-
  Proof of the soundness of classical propositional logic.
-/
example
  (F : Formula)
  (h1 : IsPropProof F) :
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


theorem mem_primeSet_isPrime
  (F F' : Formula)
  (h1 : F' ∈ F.primeSet) :
  F'.IsPrime :=
  by
  induction F
  case pred_const_ | pred_var_ =>
    simp only [Formula.primeSet] at h1
    simp at h1
    subst h1
    simp only [Formula.IsPrime]
  case true_ | false_ =>
    simp only [Formula.primeSet] at h1
    simp at h1
  case eq_ x y =>
    simp only [Formula.primeSet] at h1
    simp at h1
    subst h1
    simp only [Formula.IsPrime]
  case not_ phi phi_ih =>
    simp only [Formula.primeSet] at h1
    exact phi_ih h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [Formula.primeSet] at h1
    simp at h1
    tauto
  case forall_ x phi | exists_ x phi =>
    simp only [Formula.primeSet] at h1
    simp at h1
    subst h1
    simp only [Formula.IsPrime]
  case def_ =>
    simp only [Formula.primeSet] at h1
    simp at h1
    subst h1
    simp only [Formula.IsPrime]


theorem L_15_7
  (F F' : Formula)
  (Δ_U : Set Formula)
  (V : VarBoolAssignment)
  (Δ_U' : Set Formula)
  (h1 : F.primeSet.toSet ⊆ Δ_U)
  (h2 : Δ_U' = Δ_U.image (evalPrimeFfToNot V))
  (h3 : F' = evalPrimeFfToNot V F) :
  IsDeduct Δ_U' F' :=
  by
  subst h2
  subst h3
  induction F
  case pred_const_ X xs =>
    let F := pred_const_ X xs
    simp only [Formula.primeSet] at h1
    simp at h1

    simp only [evalPrimeFfToNot]
    simp only [Formula.evalPrime]
    apply IsDeduct.assume_
    simp
    apply Exists.intro F
    tauto
  case pred_var_ X xs =>
    let F := pred_var_ X xs
    simp only [Formula.primeSet] at h1
    simp at h1

    simp only [evalPrimeFfToNot]
    simp only [Formula.evalPrime]
    apply IsDeduct.assume_
    simp
    apply Exists.intro F
    tauto
  case eq_ x y =>
    let F := eq_ x y
    simp only [Formula.primeSet] at h1
    simp at h1

    simp only [evalPrimeFfToNot]
    simp only [Formula.evalPrime]
    apply IsDeduct.assume_
    simp
    apply Exists.intro F
    tauto
  case true_ =>
    apply IsDeduct.axiom_
    apply IsAxiom.prop_true_
  case false_ =>
    simp only [Formula.primeSet] at h1
    simp at h1

    simp only [evalPrimeFfToNot]
    simp only [Formula.evalPrime]
    simp
    sorry
  case not_ phi phi_ih =>
    simp only [Formula.primeSet] at h1

    simp only [evalPrimeFfToNot] at phi_ih

    simp only [evalPrimeFfToNot]
    simp only [evalPrime]
    simp
    split_ifs
    case _ c1 =>
      simp only [c1] at phi_ih
      simp at phi_ih
      apply IsDeduct.mp_ phi
      apply proof_imp_deduct
      apply T_14_6
      exact phi_ih h1
    case _ c1 =>
      simp only [c1] at phi_ih
      simp at phi_ih
      exact phi_ih h1
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.primeSet] at h1
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
          apply IsDeduct.mp_ (not_ phi)
          apply proof_imp_deduct
          apply T_13_6
          apply phi_ih h1_left
        case _ c1 =>
          simp only [if_pos c1] at psi_ih
          apply IsDeduct.mp_ psi
          apply IsDeduct.axiom_
          apply IsAxiom.prop_1_
          apply psi_ih
          exact h1_right
      case _ c1 =>
        simp only [evalPrime] at c1
        simp at c1
        cases c1
        case intro c1_left c1_right =>
          simp only [if_pos c1_left] at phi_ih
          simp only [if_neg c1_right] at psi_ih
          apply IsDeduct.mp_ psi.not_
          · apply IsDeduct.mp_ phi
            · apply proof_imp_deduct
              apply T_14_8
            · exact phi_ih h1_left
          · exact psi_ih h1_right
  case forall_ x phi phi_ih =>
    let F := forall_ x phi

    simp only [Formula.primeSet] at h1
    simp at h1

    simp only [evalPrimeFfToNot]
    simp only [Formula.evalPrime]
    apply IsDeduct.assume_
    simp
    apply Exists.intro F
    tauto
  case def_ X xs =>
    let F := def_ X xs
    simp only [Formula.primeSet] at h1
    simp at h1

    simp only [evalPrimeFfToNot]
    simp only [Formula.evalPrime]
    apply IsDeduct.assume_
    simp
    apply Exists.intro F
    tauto
  case and_ | or_ | iff_ | exists_ =>
    sorry


theorem T_14_9_Deduct
  (P U : Formula)
  (Δ : Set Formula)
  (h1 : IsDeduct (Δ ∪ {U}) P)
  (h2 : IsDeduct (Δ ∪ {U.not_}) P) :
  IsDeduct Δ P :=
  by
  apply IsDeduct.mp_ (U.not_.imp_ P)
  · apply IsDeduct.mp_ (U.imp_ P)
    · apply proof_imp_deduct
      apply T_14_9
    · apply deduction_theorem
      exact h1
  · apply deduction_theorem
    exact h2


theorem evalPrimeFfToNot_of_function_updateIte_true
  (F F' : Formula)
  (V : VarBoolAssignment)
  (h1 : F.IsPrime) :
  evalPrimeFfToNot (Function.updateITE V F' true) F =
    Function.updateITE (evalPrimeFfToNot V) F' F F :=
  by
  induction F
  case pred_const_ | pred_var_ | eq_ | forall_ | exists_ | def_ =>
    unfold Function.updateITE
    simp only [evalPrimeFfToNot]
    simp only [Formula.evalPrime]
    split_ifs <;> tauto
  case true_ | false_ | not_ | imp_ | and_ | or_ | iff_ =>
    simp only [Formula.IsPrime] at h1


theorem evalPrimeFfToNot_of_function_updateIte_false
  (F F' : Formula)
  (V : VarBoolAssignment)
  (h1 : F.IsPrime) :
  evalPrimeFfToNot (Function.updateITE V F' false) F =
    Function.updateITE (evalPrimeFfToNot V) F' F.not_ F :=
  by
  induction F
  case pred_const_ | pred_var_ | eq_ | forall_ | exists_ | def_ =>
    unfold Function.updateITE
    simp only [evalPrimeFfToNot]
    simp only [Formula.evalPrime]
    split_ifs <;> tauto
  case true_ | false_ | not_ | imp_ | and_ | or_ | iff_ =>
    simp only [Formula.IsPrime] at h1


theorem image_of_evalPrimeFfToNot_of_function_updateIte
  (U : Formula)
  (Δ : Set Formula)
  (V : VarBoolAssignment)
  (b : Bool)
  (h1_Δ : ∀ U' : Formula, U' ∈ Δ → U'.IsPrime)
  (h1_U : U.IsPrime)
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
  (P U : Formula)
  (Δ : Set Formula)
  (h1_Δ : ∀ U' : Formula, U' ∈ Δ → U'.IsPrime)
  (h1_U : U.IsPrime)
  (h2 : U ∉ Δ)
  (h3 : ∀ V : VarBoolAssignment, IsDeduct (Δ.image (evalPrimeFfToNot V) ∪ {evalPrimeFfToNot V U}) P) :
  ∀ V : VarBoolAssignment, IsDeduct (Δ.image (evalPrimeFfToNot V)) P :=
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
  (P : Formula)
  (Δ_U : Finset Formula)
  (h1 : Δ_U ⊆ P.primeSet)
  (h2 : ∀ V : VarBoolAssignment, IsDeduct (Δ_U.image (evalPrimeFfToNot V)) P) :
  IsDeduct ∅ P :=
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
          apply mem_primeSet_isPrime P U'
          apply h1_right
          exact a1
        · apply mem_primeSet_isPrime P U
          exact h1_left
        · exact Δ_U_1
        · simp
          exact h2


/-
  Proof of the completeness of classical propositional logic.
-/
theorem prop_complete
  (P : Formula)
  (h1 : P.IsTautoPrime) :
  IsProof P :=
  by
  simp only [IsProof]
  apply propCompleteAux P P.primeSet
  · rfl
  · intro V
    apply L_15_7 P P P.primeSet V (P.primeSet.image (evalPrimeFfToNot V))
    · rfl
    · simp only [Finset.coe_image]
    · simp only [Formula.IsTautoPrime] at h1
      simp only [evalPrimeFfToNot]
      specialize h1 V
      simp only [if_pos h1]


macro "SC" : tactic => `(tactic|(
  apply proof_imp_deduct
  apply prop_complete
  simp only [Formula.IsTautoPrime]
  simp only [eval_not, eval_imp]
  tauto))


--#lint
