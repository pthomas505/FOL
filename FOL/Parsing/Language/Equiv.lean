import FOL.Parsing.Language.Derivative


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577


namespace Languages


/-
Definition 16 (Distinguishing extension). Let L ⊆ Σ∗ be a language, and
s, t ∈ Σ∗ strings. A distinguishing extension is a string u ∈ Σ∗ such that
either su ∈ L or tu ∈ L, but not both.
-/
def is_dist_ext
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (u : Str α) :
  Prop :=
  (s ++ u ∈ L ∧ t ++ u ∉ L) ∨ (s ++ u ∉ L ∧ t ++ u ∈ L)


/-
Definition 17. Define the relation ≡L, “L-equivalent”, or “equivalent with
respect to L”, on strings by the rule
s ≡L t ⇔ {u : su ∈ L} = {u : tu ∈ L} , (1.66)
i.e. s ≡L t if there is no distinguishing extension for s and t.
-/
def L_equiv
  {α : Type}
  (L : Language α)
  (s t : Str α) :
  Prop :=
  {u | s ++ u ∈ L} = {u | t ++ u ∈ L}


lemma L_equiv_iff_deriv_eq
  {α : Type}
  (L : Language α)
  (s t : Str α) :
  L_equiv L s t ↔ derivative L s = derivative L t :=
  by
    rfl


theorem thm_15_refl
  {α : Type}
  (L : Language α)
  (s : Str α) :
  L_equiv L s s :=
  by
    rfl


theorem thm_15_symm
  {α : Type}
  (L : Language α)
  (s t : Str α) :
  L_equiv L s t → L_equiv L t s :=
  by
    simp only [L_equiv]
    intro a1
    symm
    exact a1


theorem thm_15_trans
  {α : Type}
  (L : Language α)
  (r s t : Str α)
  (h1 : L_equiv L r s)
  (h2 : L_equiv L s t) :
  L_equiv L r t :=
  by
    simp only [L_equiv] at *
    trans {u | s ++ u ∈ L}
    · exact h1
    · exact h2


instance (α : Type) (L : Language α) : IsEquiv (Str α) (L_equiv L) :=
  {
    symm := thm_15_symm L
    refl := thm_15_refl L
    trans := thm_15_trans L
  }

theorem L_equivalence
  {α : Type}
  (L : Language α) :
  Equivalence (L_equiv L) :=
  ⟨ thm_15_refl L, thm_15_symm L _ _, thm_15_trans L _ _ _ ⟩


def Str.equiv_class
  {α : Type}
  (L : Language α)
  (s : Str α) :
  Set (Str α) :=
  {t | L_equiv L s t}


example
  {α : Type}
  (L : Language α)
  (s : Str α) :
  Str.equiv_class L s = { t | derivative L s = derivative L t } :=
  by
    rfl


example
  {α : Type}
  (L : Language α)
  (a : α) :
  Str.equiv_class L [a] ∩ {s : Str α | s.length = 1} =
    { b | derivative L [a] = derivative L b ∧ b.length = 1 } :=
  by
    rfl


theorem thm_16_2
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (s t : Str α)
  (h1 : L_equiv L1 s t)
  (h2 : L_equiv L2 s t) :
  L_equiv (L1 ∪ L2) s t :=
  by
    simp only [L_equiv_iff_deriv_eq] at *
    rw [derivative_of_union_wrt_str L1 L2 s]
    rw [derivative_of_union_wrt_str L1 L2 t]
    rw [h1]
    rw [h2]


theorem thm_16_3
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (s t : Str α)
  (h1 : L_equiv L1 s t)
  (h2 : L_equiv L2 s t) :
  L_equiv (L1 ∩ L2) s t :=
  by
    simp only [L_equiv_iff_deriv_eq] at *
    rw [derivative_of_intersection_wrt_str L1 L2 s]
    rw [derivative_of_intersection_wrt_str L1 L2 t]
    rw [h1]
    rw [h2]
