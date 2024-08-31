import FOL.Parsing.Language.Kleene


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577


namespace Language


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


def Language.nullify_list
  {α : Type}
  [DecidableEq α]
  (L : List (Str α)) :
  List (Str α) :=
  open Classical in
  if [] ∈ L
  then [[]]
  else []

#eval Language.nullify_list [[0], []]
#eval Language.nullify_list [[0]]


lemma is_nullable_iff_nullify_eq_eps_singleton
  {α : Type}
  [DecidableEq α]
  (L : Language α) :
  L.is_nullable ↔ L.nullify = {[]} :=
  by
    simp only [Language.is_nullable]
    simp only [Language.nullify]
    constructor
    · intro a1
      simp only [a1]
      simp
    · intro a1
      split_ifs at a1
      case pos c1 =>
        exact c1
      case neg c1 =>
        have s1 : ¬ ({[]} : Language α) = ∅ := Set.singleton_ne_empty []
        rw [a1] at s1
        contradiction


lemma nullify_char
  {α : Type}
  [DecidableEq α]
  (c : α) :
  ({[c]} : Language α).nullify = ∅ :=
  by
    simp only [Language.nullify]
    simp


lemma nullify_eps
  {α : Type}
  [DecidableEq α] :
  ({[]} : Language α).nullify = {[]} :=
  by
    simp only [Language.nullify]
    simp


lemma nullify_empty
  {α : Type}
  [DecidableEq α] :
  (∅ : Language α).nullify = ∅ :=
  by
    simp only [Language.nullify]
    simp


lemma nullify_union
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


lemma nullify_intersection
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


lemma nullify_concat
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


lemma nullify_kleene_closure
  {α : Type}
  [DecidableEq α]
  (L : Language α) :
  (kleene_closure α L).nullify = {[]} :=
  by
    simp only [Language.nullify]
    simp only [eps_mem_kleene_closure]
    simp


lemma nullify_complement_empty
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


lemma nullify_complement_eps
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


lemma nullify_concat_nullify_left
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α) :
  (concat L1.nullify L2).nullify = (concat L1 L2).nullify :=
  by
    simp only [nullify_concat]
    simp only [nullify_idempotent]


lemma nullify_concat_nullify_right
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α) :
  (concat L1 L2.nullify).nullify = (concat L1 L2).nullify :=
  by
    simp only [nullify_concat]
    simp only [nullify_idempotent]


/-
  If [] ∈ L1 then let L0 be L1 \ {[]}. If [] ∉ L1 then let L0 be L1.
-/
lemma lang_as_union_of_nullify_and_not_nullable
  {α : Type}
  [DecidableEq α]
  (L1 : Language α) :
  ∃ (L0 : Language α), L0.nullify = ∅ ∧ L1 = L1.nullify ∪ L0 :=
  by
    simp only [Language.nullify]
    split_ifs
    case pos c1 =>
      simp
      apply Exists.intro (L1 \ {[]})
      simp
      symm
      exact Set.insert_eq_of_mem c1
    case neg c1 =>
      simp
      exact c1


lemma mem_concat_nullify_left_iff
  {α : Type}
  [DecidableEq α]
  (L M : Language α)
  (cs : Str α) :
  cs ∈ concat L.nullify M ↔ [] ∈ L ∧ cs ∈ M :=
  by
    constructor
    intro a1
    · simp only [concat] at a1
      simp only [Language.nullify] at a1
      simp at a1
      obtain ⟨s, ⟨hs_left, hs_right⟩, t, ht, eq⟩ := a1
      rw [← eq]
      simp only [hs_right]
      simp
      exact ⟨hs_left, ht⟩
    · intro a1
      simp only [concat]
      simp only [Language.nullify]
      simp
      apply Exists.intro []
      simp
      exact a1
