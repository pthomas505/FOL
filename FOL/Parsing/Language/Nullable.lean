import FOL.Parsing.Language.Kleene


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577


namespace Languages


/-
Definition 14 (Nullable). A language L is said to be nullable if ε ∈ L, and we define the nullify function ν by ν(L) =
{ε} if ε ∈ L
∅ if ε ∉ L
-/


def Language.is_nullable
  {α : Type}
  (L : Language α) :
  Prop :=
  [] ∈ L


def Language.nullify
  {α : Type}
  [DecidableEq α]
  (L : Language α) :
  Language α :=
  open Classical in
  if [] ∈ L
  then {[]}
  else ∅


lemma nullify_empty
  {α : Type}
  [DecidableEq α] :
  Language.nullify (∅ : Language α) = ∅ :=
  by
    simp only [Language.nullify]
    simp


example
  {α : Type}
  [DecidableEq α] :
  Language.nullify ({[]} : Language α) = {[]} :=
  by
    simp only [Language.nullify]
    simp


example
  {α : Type}
  [DecidableEq α]
  (L : Language α) :
  Language.nullify (kleene_closure α L) = {[]} :=
  by
    simp only [Language.nullify]
    simp only [eps_mem_kleene_closure]
    simp


example
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α) :
  (L1 ∪ L2).nullify = L1.nullify ∪ L2.nullify :=
  by
    simp only [Language.nullify]
    ext cs
    constructor
    · intro a1
      simp at a1
      simp
      tauto
    · intro a1
      simp at a1
      simp
      tauto


example
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α) :
  (L1 ∩ L2).nullify = L1.nullify ∩ L2.nullify :=
  by
    simp only [Language.nullify]
    ext cs
    constructor
    · intro a1
      simp at a1
      simp
      tauto
    · intro a1
      simp at a1
      simp
      tauto


example
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α) :
  (concat L1 L2).nullify = concat L1.nullify L2.nullify :=
  by
    simp only [Language.nullify]
    ext cs
    constructor
    · intro a1
      simp at a1
      cases a1
      case _ a1_left a2_right =>
        simp only [concat] at a1_left
        simp at a1_left

        simp only [a2_right]
        simp only [concat]
        simp
        exact a1_left
    · intro a1
      simp only [concat] at a1
      simp at a1
      obtain ⟨s, ⟨hs_left, hs_right⟩, t, ⟨ht_left, ht_right⟩, eq⟩ := a1
      rw [← eq]
      simp only [hs_right]
      simp only [ht_right]
      simp
      simp only [concat]
      simp
      constructor
      · exact hs_left
      · exact ht_left


example
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (h1 : L.nullify = ∅) :
  (Lᶜ).nullify = {[]} :=
  by
    simp only [Language.nullify] at h1
    simp at h1
    simp only [Language.nullify]
    simp
    intro a1
    contradiction


example
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (h1 : L.nullify = {[]}) :
  (Lᶜ).nullify = ∅ :=
  by
    simp only [Language.nullify] at h1
    simp at h1
    simp only [Language.nullify]
    simp
    by_contra contra
    specialize h1 contra
    apply Set.singleton_ne_empty []
    · symm
      exact h1


lemma nullify_idempotent
  {α : Type}
  [DecidableEq α]
  (L : Language α) :
  L.nullify.nullify = L.nullify :=
  by
    simp only [Language.nullify]
    split_ifs
    case _ c1 c2 =>
      rfl
    case _ c1 c2 =>
      simp at c2
    case _ c1 c2 =>
      simp at c2
    case _ c1 c2 =>
      rfl
