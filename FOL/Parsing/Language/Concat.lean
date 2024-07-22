import Mathlib.Data.Nat.Lattice

import FOL.Parsing.Language.String


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577


namespace Languages


/-
Definition 10 (Language). A language L over some alphabet Σ is a subset of Σ∗, i.e. L ⊆ Σ∗.
-/

abbrev Language (α : Type) : Type := Set (Str α)


example
  (α : Type)
  (L : Language α) :
  L ⊆ Strings.kleene_closure α :=
  by
    simp only [Set.subset_def]
    intro cs _
    exact Strings.str_mem_kleene_closure cs


lemma eps_not_mem_str_length_gt_zero
  {α : Type}
  (L : Language α)
  (s : Str α)
  (h1 : [] ∉ L)
  (h2 : s ∈ L) :
  s.length > 0 :=
  by
    simp
    exact ne_of_mem_of_not_mem h2 h1


/-
Definition 11 (Concatenation). Let L1 and L2 be languages. The concatenation of L1 and L2, written L1 · L2, or L1L2 is defined by
L1L2 = {s · t = st : s ∈ L1, t ∈ L2} .
-/
def concat
  {α : Type}
  (L1 L2 : Language α) :
  Language α :=
  { s ++ t | (s ∈ L1) (t ∈ L2) }


lemma append_mem_concat
  {α : Type}
  (L M : Language α)
  (s t : Str α)
  (h1 : s ∈ L)
  (h2 : t ∈ M) :
  s ++ t ∈ concat L M :=
  by
    simp only [concat]
    simp
    exact ⟨s, h1, t, h2, rfl⟩

-------------------------------------------------------------------------------

lemma concat_empty_left
  {α : Type}
  (L : Language α) :
  concat ∅ L = ∅ :=
  by
    simp only [concat]
    simp


lemma concat_empty_right
  {α : Type}
  (L : Language α) :
  concat L ∅ = ∅ :=
  by
    simp only [concat]
    simp

-------------------------------------------------------------------------------

lemma concat_nonempty_iff
  {α : Type}
  (L M : Language α) :
  (concat L M).Nonempty ↔ L.Nonempty ∧ M.Nonempty :=
  by
    simp only [Set.Nonempty]
    simp only [concat]
    simp
    constructor
    · intro a1
      obtain ⟨x, s, hs, t, ht, _⟩ := a1
      exact ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    · intro a1
      obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := a1
      exact ⟨s ++ t, s, hs, t, ht, rfl⟩


lemma concat_empty_iff
  {α : Type}
  (L M : Language α) :
  (concat L M) = ∅ ↔ L = ∅ ∨ M = ∅ :=
  by
    simp only [← Set.not_nonempty_iff_eq_empty]
    rw [← not_and_or]
    apply not_congr
    exact concat_nonempty_iff L M

-------------------------------------------------------------------------------

lemma concat_eps_left
  {α : Type}
  (L : Language α) :
  concat {[]} L = L :=
  by
    simp only [concat]
    simp


lemma concat_eps_right
  {α : Type}
  (L : Language α) :
  concat L {[]} = L :=
  by
    simp only [concat]
    simp

-------------------------------------------------------------------------------

lemma eps_mem_concat_iff
  {α : Type}
  (L M : Language α) :
  [] ∈ concat L M ↔ [] ∈ L ∧ [] ∈ M :=
  by
    simp only [concat]
    simp


lemma eps_not_mem_concat_iff
  {α : Type}
  (L M : Language α) :
  [] ∉ concat L M ↔ ([] ∉ L ∨ [] ∉ M) :=
  by
    rw [← not_and_or]
    apply not_congr
    exact eps_mem_concat_iff L M


example
  {α : Type}
  (L M : Language α)
  (s : Str α)
  (h1 : [] ∉ L ∨ [] ∉ M)
  (h2 : s ∈ concat L M) :
  s.length > 0 :=
  by
    rw [← eps_not_mem_concat_iff] at h1
    exact eps_not_mem_str_length_gt_zero (concat L M) s h1 h2

-------------------------------------------------------------------------------

lemma append_mem_concat_eps_left
  {α : Type}
  (L M : Language α)
  (x : Str α)
  (h1 : [] ∈ L)
  (h2 : x ∈ M) :
  x ∈ concat L M :=
  by
    have s1 : x = [] ++ x := by rfl
    rw [s1]
    exact append_mem_concat L M [] x h1 h2


lemma eps_mem_left_right_subset_concat
  {α : Type}
  (L M : Language α)
  (h1 : [] ∈ L) :
  M ⊆ concat L M :=
  by
    simp only [Set.subset_def]
    intro x a1
    exact append_mem_concat_eps_left L M x h1 a1


lemma append_mem_concat_eps_right
  {α : Type}
  (L M : Language α)
  (x : Str α)
  (h1 : x ∈ L)
  (h2 : [] ∈ M) :
  x ∈ concat L M :=
  by
    have s1 : x = x ++ [] := by rw [List.append_nil];
    rw [s1]
    exact append_mem_concat L M x [] h1 h2


lemma eps_mem_right_left_subset_concat
  {α : Type}
  (L M : Language α)
  (h1 : [] ∈ M) :
  L ⊆ concat L M :=
  by
    simp only [Set.subset_def]
    intro x a1
    exact append_mem_concat_eps_right L M x a1 h1

-------------------------------------------------------------------------------

theorem concat_assoc
  {α : Type}
  (L1 L2 L3 : Language α) :
  concat L1 (concat L2 L3) =
    concat (concat L1 L2) L3 :=
  by
    simp only [concat]
    simp

-------------------------------------------------------------------------------

theorem concat_distrib_s_union_left
  {α : Type}
  (L : Language α)
  (S : Set (Language α)) :
  concat L (⋃₀ S) = ⋃ (s ∈ S), (concat L s) :=
  by
    simp only [concat]
    ext cs
    constructor
    · intro a1
      simp at a1
      obtain ⟨s, hs, t, ⟨M, hM, ht⟩, eq⟩ := a1
      simp
      exact ⟨M, hM, s, hs, t, ht, eq⟩
    · intro a1
      simp at a1
      obtain ⟨M, hM, s, hs, t, ht, eq⟩ := a1
      simp
      exact ⟨s, hs, t, ⟨M, hM, ht⟩, eq⟩


theorem concat_distrib_s_union_right
  {α : Type}
  (S : Set (Language α))
  (L : Language α) :
  concat (⋃₀ S) L = ⋃ (s ∈ S), (concat s L) :=
  by
    simp only [concat]
    ext cs
    constructor
    · intro a1
      simp at a1
      obtain ⟨s, ⟨M, hM, hs⟩, t, ht, eq⟩ := a1
      simp
      exact ⟨M, hM, s, hs, t, ht, eq⟩
    · intro a1
      simp at a1
      obtain ⟨M, hM, s, hs, t, ht, eq⟩ := a1
      simp
      exact ⟨s, ⟨M, hM, hs⟩, t, ht, eq⟩


theorem concat_distrib_union_left
  {α : Type}
  (L1 L2 L3 : Language α) :
  concat L1 (L2 ∪ L3) =
    concat L1 L2 ∪ concat L1 L3 :=
  by
    obtain s1 := concat_distrib_s_union_left L1 {L2, L3}
    simp at s1
    exact s1


theorem concat_distrib_union_right
  {α : Type}
  (L1 L2 L3 : Language α) :
  concat (L1 ∪ L2) L3 =
    concat L1 L3 ∪ concat L2 L3 :=
  by
    obtain s1 := concat_distrib_s_union_right {L1, L2} L3
    simp at s1
    exact s1

-------------------------------------------------------------------------------

lemma concat_subset
  {α : Type}
  (L1 L2 M1 M2 : Language α)
  (h1 : L1 ⊆ M1)
  (h2 : L2 ⊆ M2) :
  concat L1 L2 ⊆ concat M1 M2 :=
  by
    simp only [Set.subset_def]
    intro x a1
    simp only [concat] at a1
    simp at a1
    obtain ⟨s, hs, t, ht, eq⟩ := a1
    simp only [concat]
    simp
    have s1 : s ∈ M1 := h1 hs
    have s2 : t ∈ M2 := h2 ht
    exact ⟨s, s1, t, s2, eq⟩


lemma concat_subset_left
  {α : Type}
  (L1 L2 L3 : Language α)
  (h1 : L2 ⊆ L3) :
  concat L1 L2 ⊆ concat L1 L3 :=
  by
    apply concat_subset
    · rfl
    · exact h1


lemma concat_subset_right
  {α : Type}
  (L1 L2 L3 : Language α)
  (h1 : L2 ⊆ L3) :
  concat L2 L1 ⊆ concat L3 L1 :=
  by
    apply concat_subset
    · exact h1
    · rfl

-------------------------------------------------------------------------------

lemma exists_mem_concat_str_length_gt_mem_left
  {α : Type}
  (L M : Language α)
  (s : Str α)
  (h1 : s ∈ L)
  (h2 : M.Nonempty)
  (h3 : [] ∉ M) :
  ∃ (t : Str α), t ∈ concat L M ∧ s.length < t.length :=
  by
    obtain ⟨t, a1⟩ := h2
    apply Exists.intro (s ++ t)
    constructor
    · apply append_mem_concat L M s t h1 a1
    · have s1 : ¬ t = [] := ne_of_mem_of_not_mem a1 h3
      exact Strings.str_append_length_right s t s1


lemma exists_mem_concat_str_length_gt_mem_right
  {α : Type}
  (L M : Language α)
  (t : Str α)
  (h1 : t ∈ M)
  (h2 : L.Nonempty)
  (h3 : [] ∉ L) :
  ∃ (s : Str α), s ∈ concat L M ∧ t.length < s.length :=
  by
    obtain ⟨s, a1⟩ := h2
    apply Exists.intro (s ++ t)
    constructor
    · apply append_mem_concat L M s t a1 h1
    · have s1 : ¬ s = [] := ne_of_mem_of_not_mem a1 h3
      exact Strings.str_append_length_left s t s1


lemma exists_mem_left_str_length_lt_concat
  {α : Type}
  (L M : Language α)
  (s : Str α)
  (h1 : s ∈ concat L M)
  (h2 : [] ∉ M) :
  ∃ (t : Str α), t ∈ L ∧ t.length < s.length :=
  by
    simp only [concat] at h1
    simp at h1
    obtain ⟨u, hu, v, hv, eq⟩ := h1
    rw [← eq]
    apply Exists.intro u
    constructor
    · exact hu
    · simp
      exact ne_of_mem_of_not_mem hv h2


lemma exists_mem_right_str_length_lt_concat
  {α : Type}
  (L M : Language α)
  (s : Str α)
  (h1 : s ∈ concat L M)
  (h2 : [] ∉ L) :
  ∃ (t : Str α), t ∈ M ∧ t.length < s.length :=
  by
    simp only [concat] at h1
    simp at h1
    obtain ⟨u, hu, v, hv, eq⟩ := h1
    rw [← eq]
    apply Exists.intro v
    constructor
    · exact hv
    · simp
      exact ne_of_mem_of_not_mem hu h2


lemma set_list_inf_length_exists
  {α : Type}
  (S : Set (List α))
  (h1 : S.Nonempty) :
  ∃ (xs : List α), xs ∈ S ∧
    ∀ (ys : List α), ys ∈ S → xs.length <= ys.length :=
  by
    let length_set : Set ℕ := Set.image List.length S
    let length_set_inf := sInf length_set
    have s1 : length_set.Nonempty := Set.Nonempty.image List.length h1
    have s2 : length_set_inf ∈ length_set := Nat.sInf_mem s1
    have s3 : ∃ (list_set_inf : List α), list_set_inf ∈ S ∧ list_set_inf.length = length_set_inf :=
    by
      rw [← Set.mem_image List.length S length_set_inf]
      exact s2
    obtain ⟨list_set_inf, list_set_inf_mem, list_set_inf_length⟩ := s3
    apply Exists.intro list_set_inf
    constructor
    · exact list_set_inf_mem
    · intro ys hy
      rw [list_set_inf_length]
      have s4 : ys.length ∈ length_set := Set.mem_image_of_mem List.length hy
      exact Nat.sInf_le s4


lemma left_nonempty_subset_concat_eps_mem_right
  {α : Type}
  (L M : Language α)
  (h1 : L.Nonempty)
  (h2 : L ⊆ concat L M) :
  [] ∈ M :=
  by
    obtain s1 := set_list_inf_length_exists L h1
    obtain ⟨min, mem, le⟩ := s1
    simp only [Set.subset_def] at h2
    specialize h2 min mem
    by_contra contra
    obtain s2 := exists_mem_left_str_length_lt_concat L M min h2 contra
    obtain ⟨t, ht, lt⟩ := s2
    specialize le t ht
    have s3 : ¬ min.length ≤ t.length := Nat.not_le_of_lt lt
    contradiction


lemma right_nonempty_subset_concat_eps_mem_left
  {α : Type}
  (L M : Language α)
  (h1 : M.Nonempty)
  (h2 : M ⊆ concat L M) :
  [] ∈ L :=
  by
    obtain s1 := set_list_inf_length_exists M h1
    obtain ⟨min, mem, le⟩ := s1
    simp only [Set.subset_def] at h2
    specialize h2 min mem
    by_contra contra
    obtain s2 := exists_mem_right_str_length_lt_concat L M min h2 contra
    obtain ⟨t, ht, lt⟩ := s2
    specialize le t ht
    have s3 : ¬ min.length ≤ t.length := Nat.not_le_of_lt lt
    contradiction
