import MathlibExtra.FunctionUpdateITE
import FOL.NV.Formula

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/--
  `is_prop_axiom_v1 F` := True if and only if `F` is an axiom of classical propositional logic.
-/
inductive is_prop_axiom_v1 : Formula_ → Prop
  -- `⊢ ⊤`
  | prop_true_ :
    is_prop_axiom_v1 true_

  -- `⊢ phi → (psi → phi)`
  | prop_1_
    (phi psi : Formula_) :
    is_prop_axiom_v1 (phi.imp_ (psi.imp_ phi))

  -- `⊢ (phi → (psi → chi)) → ((phi → psi) → (phi → chi))`
  | prop_2_
    (phi psi chi : Formula_) :
    is_prop_axiom_v1 ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi)))

  -- `⊢ (¬ phi → ¬ psi) → (psi → phi)`
  | prop_3_
    (phi psi : Formula_) :
    is_prop_axiom_v1 (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi))

  | def_false_ :
    is_prop_axiom_v1 (false_.iff_ (not_ true_))

  | def_and_
    (phi psi : Formula_) :
    is_prop_axiom_v1 ((phi.and_ psi).iff_ (not_ (phi.imp_ (not_ psi))))

  | def_or_
    (phi psi : Formula_) :
    is_prop_axiom_v1 ((phi.or_ psi).iff_ ((not_ phi).imp_ psi))

  | def_iff_
    (phi psi : Formula_) :
    is_prop_axiom_v1 (not_ (((phi.iff_ psi).imp_ (not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi))))).imp_ (not_ ((not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi)))).imp_ (phi.iff_ psi)))))


/--
  `is_prop_deduct_v1 Δ F` := True if and only if there is a deduction of `F` from `Δ` in classical propositional logic.
-/
inductive is_prop_deduct_v1 (Δ : Set Formula_) : Formula_ → Prop
  | axiom_
    (phi : Formula_) :
    is_prop_axiom_v1 phi →
    is_prop_deduct_v1 Δ phi

  | assume_
    (phi : Formula_) :
    phi ∈ Δ →
    is_prop_deduct_v1 Δ phi

  | mp_
    (phi psi : Formula_) :
    is_prop_deduct_v1 Δ (phi.imp_ psi) →
    is_prop_deduct_v1 Δ phi →
    is_prop_deduct_v1 Δ psi


/--
  `is_prop_proof_v1 F` := True if and only if there is a proof of `F` in classical propositional logic.
-/
def is_prop_proof_v1 (phi : Formula_) : Prop :=
  is_prop_deduct_v1 ∅ phi


-------------------------------------------------------------------------------


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


def replace_prime (σ : Formula_ → Formula_) : Formula_ → Formula_
  | pred_const_ X xs => σ (pred_const_ X xs)
  | pred_var_ X xs => σ (pred_var_ X xs)
  | eq_ x y => σ (eq_ x y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replace_prime σ phi)
  | imp_ phi psi => imp_ (replace_prime σ phi) (replace_prime σ psi)
  | and_ phi psi => and_ (replace_prime σ phi) (replace_prime σ psi)
  | or_ phi psi => or_ (replace_prime σ phi) (replace_prime σ psi)
  | iff_ phi psi => iff_ (replace_prime σ phi) (replace_prime σ psi)
  | forall_ x phi => σ (forall_ x phi)
  | exists_ x phi => σ (exists_ x phi)
  | def_ X xs => σ (def_ X xs)


def PropValuation_ : Type := Formula_ → Bool
  deriving Inhabited


def eval_prime (V : PropValuation_) : Formula_ → Prop
  | pred_const_ X xs => V (pred_const_ X xs)
  | pred_var_ X xs => V (pred_var_ X xs)
  | eq_ x y => V (eq_ x y)
  | true_ => True
  | false_ => False
  | not_ phi => ¬ eval_prime V phi
  | imp_ phi psi => eval_prime V phi → eval_prime V psi
  | and_ phi psi => eval_prime V phi ∧ eval_prime V psi
  | or_ phi psi => eval_prime V phi ∨ eval_prime V psi
  | iff_ phi psi => eval_prime V phi ↔ eval_prime V psi
  | forall_ x phi => V (forall_ x phi)
  | exists_ x phi => V (exists_ x phi)
  | def_ X xs => V (def_ X xs)

instance
  (V : PropValuation_)
  (F : Formula_) :
  Decidable (eval_prime V F) :=
  by
  induction F
  all_goals
    simp only [eval_prime]
    infer_instance


def Formula_.is_tauto (F : Formula_) : Prop :=
  ∀ (V : PropValuation_), eval_prime V F


def eval_prime_ff_to_not
  (V : PropValuation_)
  (F : Formula_) :
  Formula_ :=
  if eval_prime V F
  then F
  else not_ F


theorem eval_prime_prime
  (V : PropValuation_)
  (F : Formula_)
  (h1 : F.is_prime) :
  eval_prime V F = V F :=
  by
  induction F
  any_goals
    simp only [Formula_.is_prime] at h1
  all_goals
    rfl


example
  (V V' : PropValuation_)
  (F : Formula_)
  (h1 : ∀ (H : Formula_), H ∈ F.prime_set → V H = V' H) :
  eval_prime V F ↔ eval_prime V' F :=
  by
  induction F
  any_goals
    simp only [Formula_.prime_set] at h1
  all_goals
    simp only [eval_prime]
  case
      pred_const_ X xs
    | pred_var_ X xs
    | eq_ x y
    | forall_ x phi ih
    | exists_ x phi ih
    | def_ X xs =>
    congr! 1
    apply h1
    simp
  case not_ phi phi_ih =>
    congr! 1
    exact phi_ih h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
      simp at h1

      have s1 : eval_prime V phi ↔ eval_prime V' phi :=
      by
        apply phi_ih
        intro H a1
        apply h1
        tauto

      have s2 : eval_prime V psi ↔ eval_prime V' psi :=
      by
        apply psi_ih
        intro H a1
        apply h1
        tauto

      rw [s1]
      rw [s2]


theorem eval_prime_replace_prime_iff_eval_prime_eval_prime
  (V : PropValuation_)
  (σ : Formula_ → Formula_)
  (F : Formula_) :
  eval_prime V (replace_prime σ F) ↔
    eval_prime (fun (H : Formula_) => eval_prime V (σ H)) F :=
  by
  induction F
  all_goals
    simp only [replace_prime]
    simp only [eval_prime]
  case
      pred_const_ X xs
    | pred_var_ X xs
    | eq_ x y
    | forall_ x phi ih
    | exists_ x phi ih
    | def_ X xs =>
    simp only [decide_eq_true_eq]
  case not_ phi phi_ih =>
    rw [phi_ih]
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    rw [phi_ih]
    rw [psi_ih]


example
  (σ : Formula_ → Formula_)
  (F : Formula_)
  (h1 : F.is_tauto) :
  (replace_prime σ F).is_tauto :=
  by
  simp only [Formula_.is_tauto] at h1

  simp only [Formula_.is_tauto]
  intro V
  simp only [eval_prime_replace_prime_iff_eval_prime_eval_prime]
  apply h1


example
  (V : PropValuation_)
  (σ : Formula_ → Formula_)
  (P Q R S : Formula_)
  (h1 : eval_prime V P ↔ eval_prime V Q) :
  eval_prime V (replace_prime (Function.updateITE σ R P) S) ↔
    eval_prime V (replace_prime (Function.updateITE σ R Q) S) :=
  by
  simp only [eval_prime_replace_prime_iff_eval_prime_eval_prime]
  congr! 1
  funext Q'
  simp only [Function.updateITE]
  split_ifs
  · simp
    exact h1
  · rfl


theorem T_13_5
  (P : Formula_) :
  is_prop_proof_v1 (P.imp_ P) :=
  by
  simp only [is_prop_proof_v1]
  apply is_prop_deduct_v1.mp_ (P.imp_ (P.imp_ P))
  · apply is_prop_deduct_v1.mp_ (P.imp_ ((P.imp_ P).imp_ P))
    · apply is_prop_deduct_v1.axiom_
      apply is_prop_axiom_v1.prop_2_
    · apply is_prop_deduct_v1.axiom_
      apply is_prop_axiom_v1.prop_1_
  · apply is_prop_deduct_v1.axiom_
    apply is_prop_axiom_v1.prop_1_

alias prop_id := T_13_5


theorem T_13_6_no_deduct
  (P Q : Formula_) :
  is_prop_proof_v1 (P.not_.imp_ (P.imp_ Q)) :=
  by
  apply is_prop_deduct_v1.mp_ (P.not_.imp_ (Q.not_.imp_ P.not_))
  · apply is_prop_deduct_v1.mp_ (P.not_.imp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)))
    · apply is_prop_deduct_v1.axiom_
      apply is_prop_axiom_v1.prop_2_
    · apply is_prop_deduct_v1.mp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q))
      · apply is_prop_deduct_v1.axiom_
        apply is_prop_axiom_v1.prop_1_
      · apply is_prop_deduct_v1.axiom_
        apply is_prop_axiom_v1.prop_3_
  · apply is_prop_deduct_v1.axiom_
    apply is_prop_axiom_v1.prop_1_


theorem T_14_10
  (Δ : Set Formula_)
  (F : Formula_)
  (h1 : is_prop_deduct_v1 Δ F) :
  ∀ (Γ : Set Formula_), is_prop_deduct_v1 (Δ ∪ Γ) F :=
  by
  intro Γ
  induction h1
  case axiom_ h1_phi h1_1 =>
    apply is_prop_deduct_v1.axiom_
    exact h1_1
  case assume_ h1_phi h1_1 =>
    apply is_prop_deduct_v1.assume_
    simp
    left
    exact h1_1
  case mp_ h1_phi h1_psi _ _ h1_ih_1 h1_ih_2 =>
    apply is_prop_deduct_v1.mp_ h1_phi
    · exact h1_ih_1
    · exact h1_ih_2


theorem T_14_10_comm
  (Δ : Set Formula_)
  (F : Formula_)
  (h1 : is_prop_deduct_v1 Δ F) :
  ∀ (Γ : Set Formula_), is_prop_deduct_v1 (Γ ∪ Δ) F :=
  by
  simp only [Set.union_comm]
  apply T_14_10
  exact h1


theorem C_14_11
  (F : Formula_)
  (h1 : is_prop_proof_v1 F) :
  ∀ (Δ : Set Formula_), is_prop_deduct_v1 Δ F :=
  by
  intro Δ
  obtain s1 := T_14_10 ∅ F h1 Δ
  simp at s1
  exact s1

alias proof_imp_deduct := C_14_11


-- Deduction Theorem
theorem T_14_3
  (Δ : Set Formula_)
  (P Q : Formula_)
  (h1 : is_prop_deduct_v1 (Δ ∪ {P}) Q) :
  is_prop_deduct_v1 Δ (P.imp_ Q) :=
  by
  induction h1
  case axiom_ h1_phi h1_1 =>
    apply is_prop_deduct_v1.mp_ h1_phi
    · apply is_prop_deduct_v1.axiom_
      apply is_prop_axiom_v1.prop_1_
    · apply is_prop_deduct_v1.axiom_
      exact h1_1
  case assume_ h1_phi h1_1 =>
    simp at h1_1
    cases h1_1
    case inl h1_1 =>
      rw [h1_1]
      apply proof_imp_deduct
      apply prop_id
    case inr h1_1 =>
      apply is_prop_deduct_v1.mp_ h1_phi
      · apply is_prop_deduct_v1.axiom_
        apply is_prop_axiom_v1.prop_1_
      · apply is_prop_deduct_v1.assume_
        exact h1_1
  case mp_ h1_phi h1_psi _ _ h1_ih_1
    h1_ih_2 =>
    apply is_prop_deduct_v1.mp_ (P.imp_ h1_phi)
    · apply is_prop_deduct_v1.mp_ (P.imp_ (h1_phi.imp_ h1_psi))
      · apply is_prop_deduct_v1.axiom_
        apply is_prop_axiom_v1.prop_2_
      · exact h1_ih_1
    · exact h1_ih_2

alias deduction_theorem := T_14_3


theorem T_13_6
  (P Q : Formula_) :
  is_prop_proof_v1 (P.not_.imp_ (P.imp_ Q)) :=
  by
  simp only [is_prop_proof_v1]
  apply deduction_theorem
  apply is_prop_deduct_v1.mp_ (Q.not_.imp_ P.not_)
  · apply is_prop_deduct_v1.axiom_
    apply is_prop_axiom_v1.prop_3_
  · apply is_prop_deduct_v1.mp_ P.not_
    · apply is_prop_deduct_v1.axiom_
      apply is_prop_axiom_v1.prop_1_
    · apply is_prop_deduct_v1.assume_
      simp


theorem T_14_5
  (P : Formula_) :
  is_prop_proof_v1 (P.not_.not_.imp_ P) :=
  by
  simp only [is_prop_proof_v1]
  apply deduction_theorem
  apply is_prop_deduct_v1.mp_ P.not_.not_
  · apply is_prop_deduct_v1.mp_ (P.not_.imp_ P.not_.not_.not_)
    · apply is_prop_deduct_v1.axiom_
      apply is_prop_axiom_v1.prop_3_
    · apply is_prop_deduct_v1.mp_ P.not_.not_
      · apply proof_imp_deduct
        apply T_13_6
      · apply is_prop_deduct_v1.assume_
        simp
  · apply is_prop_deduct_v1.assume_
    simp


theorem T_14_6
  (P : Formula_) :
  is_prop_proof_v1 (P.imp_ P.not_.not_) :=
  by
  simp only [is_prop_proof_v1]
  apply is_prop_deduct_v1.mp_ (P.not_.not_.not_.imp_ P.not_)
  · apply is_prop_deduct_v1.axiom_
    apply is_prop_axiom_v1.prop_3_
  · apply proof_imp_deduct
    apply T_14_5


theorem T_14_7
  (P Q : Formula_) :
  is_prop_proof_v1 ((P.imp_ Q).imp_ (Q.not_.imp_ P.not_)) :=
  by
  simp only [is_prop_proof_v1]
  apply deduction_theorem
  apply is_prop_deduct_v1.mp_ (P.not_.not_.imp_ Q.not_.not_)
  · apply is_prop_deduct_v1.axiom_
    apply is_prop_axiom_v1.prop_3_
  · apply deduction_theorem
    apply is_prop_deduct_v1.mp_ Q
    · apply proof_imp_deduct
      apply T_14_6
    · apply is_prop_deduct_v1.mp_ P
      · apply is_prop_deduct_v1.assume_
        simp
      · apply is_prop_deduct_v1.mp_ P.not_.not_
        · apply proof_imp_deduct
          apply T_14_5
        · apply is_prop_deduct_v1.assume_
          simp


theorem T_14_8
  (Q R : Formula_) :
  is_prop_proof_v1 (Q.imp_ (R.not_.imp_ (Q.imp_ R).not_)) :=
  by
  simp only [is_prop_proof_v1]
  apply deduction_theorem
  apply is_prop_deduct_v1.mp_ ((Q.imp_ R).imp_ R)
  · apply proof_imp_deduct
    apply T_14_7
  · apply deduction_theorem
    apply is_prop_deduct_v1.mp_ Q
    · apply is_prop_deduct_v1.assume_
      simp
    · apply is_prop_deduct_v1.assume_
      simp


theorem T_14_9
  (P S : Formula_) :
  is_prop_proof_v1 ((S.imp_ P).imp_ ((S.not_.imp_ P).imp_ P)) :=
  by
  simp only [is_prop_proof_v1]
  apply deduction_theorem
  apply is_prop_deduct_v1.mp_ (P.not_.imp_ (S.not_.imp_ P).not_)
  · apply is_prop_deduct_v1.axiom_
    apply is_prop_axiom_v1.prop_3_
  · apply deduction_theorem
    apply is_prop_deduct_v1.mp_ P.not_
    · apply is_prop_deduct_v1.mp_ S.not_
      · apply proof_imp_deduct
        apply T_14_8
      · apply is_prop_deduct_v1.mp_ P.not_
        · apply is_prop_deduct_v1.mp_ (S.imp_ P)
          · apply proof_imp_deduct
            apply T_14_7
          · apply is_prop_deduct_v1.assume_
            simp
        · apply is_prop_deduct_v1.assume_
          simp
    · apply is_prop_deduct_v1.assume_
      simp


-- https://us.metamath.org/mpeuni/mmtheorems.html#dtl:1.2


lemma mp2
  (phi psi chi : Formula_)
  (h1 : is_prop_proof_v1 phi)
  (h2 : is_prop_proof_v1 psi)
  (h3 : is_prop_proof_v1 (phi.imp_ (psi.imp_ chi))) :
  is_prop_proof_v1 chi :=
  by
  apply is_prop_deduct_v1.mp_ psi
  · apply is_prop_deduct_v1.mp_ phi
    · exact h3
    · exact h1
  · exact h2


lemma mp2b
  (phi psi chi : Formula_)
  (h1 : is_prop_proof_v1 phi)
  (h2 : is_prop_proof_v1 (phi.imp_ psi))
  (h3 : is_prop_proof_v1 (psi.imp_ chi)) :
  is_prop_proof_v1 chi :=
  by
  apply is_prop_deduct_v1.mp_ psi
  · exact h3
  · apply is_prop_deduct_v1.mp_ phi
    · exact h2
    · exact h1


lemma a1i
  (phi psi : Formula_)
  (h1 : is_prop_proof_v1 phi) :
  is_prop_proof_v1 (psi.imp_ phi) :=
  by
  apply is_prop_deduct_v1.mp_ phi
  · apply is_prop_deduct_v1.axiom_
    apply is_prop_axiom_v1.prop_1_
  · exact h1


lemma _2a1i
  (phi psi chi : Formula_)
  (h1 : is_prop_proof_v1 phi) :
  is_prop_proof_v1 (psi.imp_ (chi.imp_ phi)) :=
  by
  apply a1i
  apply a1i
  exact h1


lemma mp1i
  (phi psi chi : Formula_)
  (h1 : is_prop_proof_v1 phi)
  (h2 : is_prop_proof_v1 (phi.imp_ psi)) :
  is_prop_proof_v1 (chi.imp_ psi) :=
  by
  apply a1i
  apply is_prop_deduct_v1.mp_ phi
  · exact h2
  · exact h1


lemma a2i
  (phi psi chi : Formula_)
  (h1 : is_prop_proof_v1 (phi.imp_ (psi.imp_ chi))) :
  is_prop_proof_v1 ((phi.imp_ psi).imp_ (phi.imp_ chi)) :=
  by
  apply is_prop_deduct_v1.mp_ (phi.imp_ (psi.imp_ chi))
  · apply is_prop_deduct_v1.axiom_
    apply is_prop_axiom_v1.prop_2_
  · exact h1


lemma mpd
  (phi psi chi : Formula_)
  (h1 : is_prop_proof_v1 (phi.imp_ psi))
  (h2 : is_prop_proof_v1 (phi.imp_ (psi.imp_ chi))) :
  is_prop_proof_v1 (phi.imp_ chi) :=
  by
  apply is_prop_deduct_v1.mp_ (phi.imp_ psi)
  · apply a2i
    exact h2
  · exact h1


lemma imim2i
  (phi psi chi : Formula_)
  (h1 : is_prop_proof_v1 (phi.imp_ psi)) :
  is_prop_proof_v1 ((chi.imp_ phi).imp_ (chi.imp_ psi)) :=
  by
  apply a2i
  apply a1i
  exact h1


lemma syl
  (phi psi chi : Formula_)
  (h1 : is_prop_proof_v1 (phi.imp_ psi))
  (h2 : is_prop_proof_v1 (psi.imp_ chi)) :
  is_prop_proof_v1 (phi.imp_ chi) :=
  by
  apply mpd phi psi chi
  · exact h1
  · apply a1i
    exact h2


lemma sylcom
  (phi psi chi theta : Formula_)
  (h1 : is_prop_proof_v1 (phi.imp_ (psi.imp_ chi)))
  (h2 : is_prop_proof_v1 (psi.imp_ (chi.imp_ theta))) :
  is_prop_proof_v1 (phi.imp_ (psi.imp_ theta)) :=
  by
  apply syl phi (psi.imp_ chi)
  · exact h1
  · apply a2i
    exact h2


lemma syl6
  (phi psi chi theta : Formula_)
  (h1 : is_prop_proof_v1 (phi.imp_ (psi.imp_ chi)))
  (h2 : is_prop_proof_v1 (chi.imp_ theta)) :
  is_prop_proof_v1 (phi.imp_ (psi.imp_ theta)) :=
  by
  apply sylcom
  · exact h1
  · apply a1i
    exact h2


lemma expi
  (phi psi chi : Formula_)
  (h1 : is_prop_proof_v1 ((not_ (phi.imp_ (not_ psi))).imp_ chi)) :
  is_prop_proof_v1 (phi.imp_ (psi.imp_ chi)) :=
  by
  apply syl6
  · sorry
  · apply h1

lemma impbi
  (phi psi : Formula_) :
  is_prop_proof_v1 ((phi.imp_ psi).imp_ ((psi.imp_ phi).imp_ (phi.iff_ psi))) :=
  by
  sorry

lemma idd
  (phi psi : Formula_) :
  is_prop_proof_v1 (phi.imp_ (psi.imp_ psi)) :=
  by
  apply a1i
  apply prop_id




theorem deduction_theorem_converse
  (Δ : Set Formula_)
  (P Q : Formula_)
  (h1 : is_prop_deduct_v1 Δ (P.imp_ Q)) :
  is_prop_deduct_v1 (Δ ∪ {P}) Q :=
  by
  apply is_prop_deduct_v1.mp_ P
  · apply T_14_10
    exact h1
  · apply is_prop_deduct_v1.assume_
    simp


theorem T_14_12
  (Δ Γ : Set Formula_)
  (P Q : Formula_)
  (h1 : is_prop_deduct_v1 Δ P)
  (h2 : is_prop_deduct_v1 Γ (P.imp_ Q)) :
  is_prop_deduct_v1 (Δ ∪ Γ) Q :=
  by
  apply is_prop_deduct_v1.mp_ P
  · apply T_14_10_comm
    exact h2
  · apply T_14_10
    exact h1


theorem C_14_14
  (Γ : Set Formula_)
  (P Q : Formula_)
  (h1 : is_prop_proof_v1 P)
  (h2 : is_prop_deduct_v1 Γ (P.imp_ Q)) :
  is_prop_deduct_v1 Γ Q :=
  by
  apply is_prop_deduct_v1.mp_ P
  · exact h2
  · apply proof_imp_deduct
    exact h1

alias mp_proof_deduct := C_14_14


theorem C_14_15
  (Δ : Set Formula_)
  (P Q : Formula_)
  (h1 : is_prop_deduct_v1 Δ P)
  (h2 : is_prop_proof_v1 (P.imp_ Q)) :
  is_prop_deduct_v1 Δ Q :=
  by
  apply is_prop_deduct_v1.mp_ P
  · apply proof_imp_deduct
    exact h2
  · exact h1

alias mp_deduct_proof := C_14_15


theorem T_14_16
  (Δ Γ : Set Formula_)
  (F : Formula_)
  (h1 : is_prop_deduct_v1 Γ F)
  (h2 : ∀ (H : Formula_), H ∈ Γ → is_prop_deduct_v1 Δ H) :
  is_prop_deduct_v1 Δ F :=
  by
  induction h1
  case axiom_ h1_phi h1_1 =>
    apply is_prop_deduct_v1.axiom_
    exact h1_1
  case assume_ h1_phi h1_1 =>
    apply h2
    exact h1_1
  case mp_ h1_phi h1_psi _ _ h1_ih_1 h1_ih_2 =>
    exact is_prop_deduct_v1.mp_ h1_phi h1_psi h1_ih_1 h1_ih_2


theorem C_14_17
  (Γ : Set Formula_)
  (Q : Formula_)
  (h1 : is_prop_deduct_v1 Γ Q)
  (h2 : ∀ (P : Formula_), P ∈ Γ → is_prop_proof_v1 P) :
  is_prop_proof_v1 Q :=
  by
  simp only [is_prop_proof_v1] at h2

  simp only [is_prop_proof_v1]
  exact T_14_16 ∅ Γ Q h1 h2


/-
theorem eval_not
  (V : PropValuation_)
  (P : Formula_) :
  eval_prime V (not_ P) ↔
    ¬ eval_prime V P :=
  by
  simp only [eval_prime]


theorem eval_imp
  (V : PropValuation_)
  (P Q : Formula_) :
  eval_prime V (imp_ P Q) ↔
    (eval_prime V P → eval_prime V Q) :=
  by
  simp only [eval_prime]


theorem eval_false
  (V : PropValuation_) :
  eval_prime V false_ ↔
    False :=
  by
  simp only [eval_prime]


theorem eval_and
  (V : PropValuation_)
  (P Q : Formula_) :
  eval_prime V (and_ P Q) ↔
    (eval_prime V P ∧ eval_prime V Q) :=
  by
  simp only [eval_prime]


theorem eval_or
  (V : PropValuation_)
  (P Q : Formula_) :
  eval_prime V (or_ P Q) ↔
    (eval_prime V P ∨ eval_prime V Q) :=
  by
  simp only [eval_prime]


theorem eval_iff
  (V : PropValuation_)
  (P Q : Formula_) :
  eval_prime V (iff_ P Q) ↔
    (eval_prime V P ↔ eval_prime V Q) :=
  by
  simp only [eval_prime]


theorem is_tauto_prop_true :
  true_.is_tauto :=
  by
  simp only [is_tauto]
  simp only [eval_prime]
  simp


theorem is_tauto_prop_1
  (P Q : Formula_) :
  (P.imp_ (Q.imp_ P)).is_tauto :=
  by
  simp only [is_tauto]
  tauto


theorem is_tauto_prop_2
  (P Q R : Formula_) :
  ((P.imp_ (Q.imp_ R)).imp_ ((P.imp_ Q).imp_ (P.imp_ R))).is_tauto :=
  by
  simp only [is_tauto]
  tauto


theorem is_tauto_prop_3
  (P Q : Formula_) :
  (((not_ P).imp_ (not_ Q)).imp_ (Q.imp_ P)).is_tauto :=
  by
  simp only [is_tauto]
  simp only [eval_not, eval_imp]
  tauto


theorem is_tauto_mp
  (P Q : Formula_)
  (h1 : (P.imp_ Q).is_tauto)
  (h2 : P.is_tauto) :
  Q.is_tauto :=
  by
  simp only [is_tauto] at h1
  simp only [eval_imp] at h1

  simp only [is_tauto] at h2

  tauto


theorem is_tauto_def_false :
  (false_.iff_ (not_ true_)).is_tauto :=
  by
  simp only [is_tauto]
  simp only [eval_not, eval_iff]
  tauto

theorem is_tauto_def_and
  (P Q : Formula_) :
  ((P.and_ Q).iff_ (not_ (P.imp_ (not_ Q)))).is_tauto :=
  by
  simp only [is_tauto]
  simp only [eval_and, eval_not, eval_imp, eval_iff]
  tauto

theorem is_tauto_def_or
  (P Q : Formula_) :
  ((P.or_ Q).iff_ ((not_ P).imp_ Q)).is_tauto :=
  by
  simp only [is_tauto]
  simp only [eval_or, eval_not, eval_imp, eval_iff]
  tauto

theorem is_tauto_def_iff
  (P Q : Formula_) :
  (not_ (((P.iff_ Q).imp_ (not_ ((P.imp_ Q).imp_ (not_ (Q.imp_ P))))).imp_ (not_ ((not_ ((P.imp_ Q).imp_ (not_ (Q.imp_ P)))).imp_ (P.iff_ Q))))).is_tauto :=
  by
  simp only [is_tauto]
  simp only [eval_iff, eval_not, eval_imp]
  tauto
-/


/-
  Proof of the soundness of classical propositional logic.
-/
example
  (F : Formula_)
  (h1 : is_prop_proof_v1 F) :
  F.is_tauto :=
  by
  induction h1
  case axiom_ h1_phi h1_1 =>
    induction h1_1
    all_goals
      simp only [is_tauto]
      simp only [eval_prime]
      tauto
  case assume_ h1_phi h1_1 =>
    simp at h1_1
  case mp_ h1_phi h1_psi _ _ h1_ih_1 h1_ih_2 =>
    simp only [is_tauto] at h1_ih_1
    simp only [eval_prime] at h1_ih_1

    simp only [is_tauto] at h1_ih_2

    simp only [is_tauto]
    tauto


theorem mem_prime_set_is_prime
  (F F' : Formula_)
  (h1 : F' ∈ F.prime_set) :
  F'.is_prime :=
  by
  induction F
  all_goals
    simp only [Formula_.prime_set] at h1
  case pred_const_ X xs | pred_var_ X xs =>
    simp at h1
    rw [h1]
    simp only [Formula_.is_prime]
  case true_ | false_ =>
    simp at h1
  case eq_ x y =>
    simp at h1
    rw [h1]
    simp only [Formula_.is_prime]
  case not_ phi phi_ih =>
    exact phi_ih h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp at h1
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp at h1
    rw [h1]
    simp only [Formula_.is_prime]
  case def_ =>
    simp at h1
    rw [h1]
    simp only [Formula_.is_prime]


theorem L_15_7
  (Δ : Set Formula_)
  (V : PropValuation_)
  (F : Formula_)
  (h1 : F.prime_set.toSet ⊆ Δ) :
  is_prop_deduct_v1 (Δ.image (eval_prime_ff_to_not V)) (eval_prime_ff_to_not V F) :=
  by
  induction F
  any_goals
    simp only [Formula_.prime_set] at h1
    simp only [Finset.coe_singleton, Set.singleton_subset_iff] at h1

    apply is_prop_deduct_v1.assume_
    simp only [Set.mem_image]
  case pred_const_ X xs =>
    apply Exists.intro (pred_const_ X xs)
    tauto
  case pred_var_ X xs =>
    apply Exists.intro (pred_var_ X xs)
    tauto
  case eq_ x y =>
    apply Exists.intro (eq_ x y)
    tauto
  case true_ =>
    apply is_prop_deduct_v1.axiom_
    apply is_prop_axiom_v1.prop_true_
  case false_ =>
    simp only [eval_prime_ff_to_not]
    simp only [eval_prime]
    simp

    obtain s1 := is_prop_axiom_v1.def_false_
    sorry
  case not_ phi phi_ih =>
    simp only [Formula_.prime_set] at h1
    specialize phi_ih h1

    simp only [eval_prime_ff_to_not] at phi_ih

    simp only [eval_prime_ff_to_not]
    simp only [eval_prime]
    simp
    split_ifs
    case _ c1 =>
      simp only [if_pos c1] at phi_ih

      apply is_prop_deduct_v1.mp_ phi
      · apply proof_imp_deduct
        apply T_14_6
      · exact phi_ih
    case _ c1 =>
      simp only [if_neg c1] at phi_ih

      exact phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula_.prime_set] at h1
    simp at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    specialize phi_ih h1_left
    specialize psi_ih h1_right

    simp only [eval_prime_ff_to_not] at phi_ih
    simp only [eval_prime_ff_to_not] at psi_ih

    simp only [eval_prime_ff_to_not]
    simp only [eval_prime]

    by_cases c1 : eval_prime V phi
    case pos =>
      simp only [if_pos c1] at phi_ih
      by_cases c2 : eval_prime V psi
      case pos =>
        simp only [if_pos c2] at psi_ih
        have s1 : eval_prime V phi → eval_prime V psi :=
        by
          tauto
        simp only [if_pos s1]

        apply is_prop_deduct_v1.mp_ psi
        · apply is_prop_deduct_v1.axiom_
          apply is_prop_axiom_v1.prop_1_
        · exact psi_ih
      case neg =>
        simp only [if_neg c2] at psi_ih
        have s1 : ¬ (eval_prime V phi → eval_prime V psi) :=
        by
          tauto
        simp only [if_neg s1]

        apply is_prop_deduct_v1.mp_ psi.not_
        · apply is_prop_deduct_v1.mp_ phi
          · apply proof_imp_deduct
            apply T_14_8
          · exact phi_ih
        · exact psi_ih
    case neg =>
      simp only [if_neg c1] at phi_ih
      by_cases c2 : eval_prime V psi
      case pos =>
        simp only [if_pos c2] at psi_ih
        have s1 : eval_prime V phi → eval_prime V psi :=
        by
          tauto
        simp only [if_pos s1]

        apply is_prop_deduct_v1.mp_ phi.not_
        · apply proof_imp_deduct
          apply T_13_6
        · exact phi_ih
      case neg =>
        simp only [if_neg c2] at psi_ih
        have s1 : (eval_prime V phi → eval_prime V psi) :=
        by
          tauto
        simp only [if_pos s1]

        apply is_prop_deduct_v1.mp_ phi.not_
        · apply proof_imp_deduct
          apply T_13_6
        · exact phi_ih
  case forall_ x phi phi_ih =>
    apply Exists.intro (forall_ x phi)
    tauto
  case def_ X xs =>
    apply Exists.intro (def_ X xs)
    tauto
  case and_ | or_ | iff_ | exists_ =>
    sorry


theorem T_14_9_Deduct
  (P U : Formula_)
  (Δ : Set Formula_)
  (h1 : is_prop_deduct_v1 (Δ ∪ {U}) P)
  (h2 : is_prop_deduct_v1 (Δ ∪ {U.not_}) P) :
  is_prop_deduct_v1 Δ P :=
  by
  apply is_prop_deduct_v1.mp_ (U.not_.imp_ P)
  · apply is_prop_deduct_v1.mp_ (U.imp_ P)
    · apply proof_imp_deduct
      apply T_14_9
    · apply deduction_theorem
      exact h1
  · apply deduction_theorem
    exact h2


theorem eval_prime_ff_to_not_of_function_updateITE_true
  (F F' : Formula_)
  (V : PropValuation_)
  (h1 : F.is_prime) :
  eval_prime_ff_to_not (Function.updateITE V F' true) F =
    Function.updateITE (eval_prime_ff_to_not V) F' F F :=
  by
  induction F
  case pred_const_ | pred_var_ | eq_ | forall_ | exists_ | def_ =>
    unfold Function.updateITE
    simp only [eval_prime_ff_to_not]
    simp only [eval_prime]
    split_ifs <;> tauto
  case true_ | false_ | not_ | imp_ | and_ | or_ | iff_ =>
    simp only [Formula_.is_prime] at h1


theorem eval_prime_ff_to_not_of_function_updateITE_false
  (F F' : Formula_)
  (V : PropValuation_)
  (h1 : F.is_prime) :
  eval_prime_ff_to_not (Function.updateITE V F' false) F =
    Function.updateITE (eval_prime_ff_to_not V) F' F.not_ F :=
  by
  induction F
  case pred_const_ | pred_var_ | eq_ | forall_ | exists_ | def_ =>
    unfold Function.updateITE
    simp only [eval_prime_ff_to_not]
    simp only [eval_prime]
    split_ifs <;> tauto
  case true_ | false_ | not_ | imp_ | and_ | or_ | iff_ =>
    simp only [Formula_.is_prime] at h1


theorem image_of_eval_prime_ff_to_not_of_function_updateITE
  (U : Formula_)
  (Δ : Set Formula_)
  (V : PropValuation_)
  (b : Bool)
  (h1 : ∀ U' : Formula_, U' ∈ Δ → U'.is_prime)
  (h2 : U ∉ Δ) :
  Δ.image (eval_prime_ff_to_not (Function.updateITE V U b)) =
    Δ.image (eval_prime_ff_to_not V) :=
  by
  apply Set.image_congr
  intro U' a1
  specialize h1 U' a1
  cases b
  · simp only [eval_prime_ff_to_not_of_function_updateITE_false U' U V h1]
    simp only [Function.updateITE]
    simp
    intro a2
    rw [← a2] at h2
    contradiction
  · simp only [eval_prime_ff_to_not_of_function_updateITE_true U' U V h1]
    simp only [Function.updateITE]
    simp
    intro a2
    rw [← a2] at h2
    contradiction


theorem prop_complete_aux_aux
  (P U : Formula_)
  (Δ : Set Formula_)
  (h1_Δ : ∀ (U' : Formula_), U' ∈ Δ → U'.is_prime)
  (h1_U : U.is_prime)
  (h2 : U ∉ Δ)
  (h3 : ∀ (V : PropValuation_), is_prop_deduct_v1 (Δ.image (eval_prime_ff_to_not V) ∪ {eval_prime_ff_to_not V U}) P) :
  ∀ (V : PropValuation_), is_prop_deduct_v1 (Δ.image (eval_prime_ff_to_not V)) P :=
  by
  intro V
  apply T_14_9_Deduct P U (Δ.image (eval_prime_ff_to_not V))
  · specialize h3 (Function.updateITE V U true)
    simp only [image_of_eval_prime_ff_to_not_of_function_updateITE U Δ V true h1_Δ h2] at h3
    simp only [eval_prime_ff_to_not_of_function_updateITE_true U U V h1_U] at h3
    simp only [Function.updateITE] at h3
    simp only [if_true] at h3
    exact h3
  · specialize h3 (Function.updateITE V U false)
    simp only [image_of_eval_prime_ff_to_not_of_function_updateITE U Δ V false h1_Δ h2] at h3
    simp only [eval_prime_ff_to_not_of_function_updateITE_false U U V h1_U] at h3
    simp only [Function.updateITE] at h3
    simp only [if_true] at h3
    exact h3


theorem prop_complete_aux
  (P : Formula_)
  (Δ_U : Finset Formula_)
  (h1 : Δ_U ⊆ P.prime_set)
  (h2 : ∀ V : PropValuation_, is_prop_deduct_v1 (Δ_U.image (eval_prime_ff_to_not V)) P) :
  is_prop_deduct_v1 ∅ P :=
  by
  induction Δ_U using Finset.induction_on
  case empty =>
    simp at h2
    exact h2
  case insert U Δ_U Δ_U_1 Δ_U_2 =>
    apply Δ_U_2
    · simp only [Finset.insert_subset_iff] at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      exact h1_right
    · simp only [Finset.insert_subset_iff] at h1

      simp at h2

      obtain ⟨h1_left, h1_right⟩ := h1
      simp
      apply prop_complete_aux_aux P U Δ_U
      · intro U' a1
        apply mem_prime_set_is_prime P U'
        apply h1_right
        exact a1
      · apply mem_prime_set_is_prime P U
        exact h1_left
      · exact Δ_U_1
      · simp
        exact h2


/-
  Proof of the completeness of classical propositional logic.
-/
theorem prop_complete
  (P : Formula_)
  (h1 : P.is_tauto) :
  is_prop_proof_v1 P :=
  by
  simp only [Formula_.is_tauto] at h1

  simp only [is_prop_proof_v1]
  apply prop_complete_aux P P.prime_set
  · rfl
  · intro V
    obtain s1 := L_15_7 P.prime_set V (eval_prime_ff_to_not V P)
    simp only [eval_prime_ff_to_not] at s1
    simp only [if_pos (h1 V)] at s1

    simp only [Finset.coe_image]
    simp only [eval_prime_ff_to_not]
    apply s1
    exact fun ⦃a⦄ a => a


macro "SC" : tactic => `(tactic|(
  apply proof_imp_deduct
  apply prop_complete
  simp only [Formula_.is_tauto]
  simp only [eval_prime]
  tauto))


--#lint
