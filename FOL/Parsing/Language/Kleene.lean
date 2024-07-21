import FOL.Parsing.Language.Exp


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577


namespace Languages


/-
Definition 13 (Kleene closure). Let L be a language. L∗ is defined by
1. ε ∈ L∗
2. For any s ∈ L∗ and t ∈ L, st ∈ L∗
3. Nothing else is in L∗
-/
inductive kleene_closure
  (α : Type) :
  Language α → Language α
  | eps
    (L : Language α) :
    kleene_closure α L []
  | succ
    (L : Language α)
    (s t : Str α) :
    s ∈ kleene_closure α L →
    t ∈ L →
    kleene_closure α L (s ++ t)


lemma eps_mem_kleene_closure
  {α : Type}
  (L : Language α) :
  [] ∈ kleene_closure α L :=
  by
    exact kleene_closure.eps L


lemma kleene_closure_empty
  {α : Type} :
  kleene_closure α ∅ = {[]} :=
  by
    ext cs
    simp
    constructor
    · intro a1
      induction a1
      case _ =>
        rfl
      case _ s t ih_1 ih_2 _ =>
        simp at ih_2
    · intro a1
      rw [a1]
      exact kleene_closure.eps ∅


lemma kleene_closure_eps
  {α : Type} :
  kleene_closure α {[]} = {[]} :=
  by
    ext cs
    simp
    constructor
    · intro a1
      induction a1
      case _ =>
        rfl
      case _ s t ih_1 ih_2 ih_3 =>
        simp at ih_2
        rw [ih_3, ih_2]
        simp
    · intro a1
      rw [a1]
      exact kleene_closure.eps {[]}


-- Theorem 4
theorem exp_subset_kleene_closure
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  exp L n ⊆ kleene_closure α L :=
  by
    simp only [Set.subset_def]
    intro cs a1

    induction n generalizing cs
    case zero =>
      simp only [exp] at a1
      simp at a1

      simp only [a1]
      exact kleene_closure.eps L
    case succ n ih =>
      simp only [exp] at a1
      simp only [concat] at a1
      simp at a1

      obtain ⟨s, hs, t, ht, eq⟩ := a1
      simp only [← eq]
      apply kleene_closure.succ L
      · exact ih s hs
      · exact ht

-------------------------------------------------------------------------------

lemma language_subset_kleene_closure
  {α : Type}
  (L : Language α) :
  L ⊆ kleene_closure α L :=
  by
    conv => left; rw [← exp_one L]
    exact exp_subset_kleene_closure L 1


lemma mem_language_mem_kleene_closure
  {α : Type}
  (L : Language α)
  (x : Str α)
  (h1 : x ∈ L) :
  x ∈ kleene_closure α L :=
  by
    obtain s1 := language_subset_kleene_closure L
    exact Set.mem_of_subset_of_mem s1 h1

-------------------------------------------------------------------------------

lemma union_exp_subset_kleene_closure
  {α : Type}
  (L : Language α) :
  ⋃ (n : ℕ), exp L n ⊆ kleene_closure α L :=
  by
    simp only [Set.subset_def]
    intro cs a1
    simp at a1
    obtain ⟨n, a2⟩ := a1
    exact Set.mem_of_subset_of_mem (exp_subset_kleene_closure L n) a2


lemma kleene_closure_subset_union_exp
  {α : Type}
  (L : Language α) :
  kleene_closure α L ⊆ ⋃ (n : ℕ), exp L n :=
  by
    simp only [Set.subset_def]
    intro cs a1
    induction a1
    case eps =>
      simp
      apply Exists.intro 0
      simp only [exp]
      simp
    case succ s t _ ih_2 ih_3 =>
      simp at ih_3
      obtain ⟨i, hs⟩ := ih_3

      simp
      apply Exists.intro (i + 1)
      simp only [exp]
      simp only [concat]
      simp
      exact ⟨s, hs, t, ih_2, rfl⟩


-- Theorem 5
theorem kleene_closure_eq_union_exp
  {α : Type}
  (L : Language α) :
  kleene_closure α L = ⋃ (n : ℕ), exp L n :=
    Set.eq_of_subset_of_subset (kleene_closure_subset_union_exp L) (union_exp_subset_kleene_closure L)

-------------------------------------------------------------------------------

theorem concat_kleene_closure_closed
  {α : Type}
  (L : Language α) :
  concat (kleene_closure α L) (kleene_closure α L) ⊆ kleene_closure α L :=
  by
    simp only [kleene_closure_eq_union_exp]
    simp only [Set.subset_def]
    intro cs a1
    simp only [concat] at a1
    simp at a1
    obtain ⟨s, ⟨i, hs⟩, t, ⟨j, ht⟩, eq⟩ := a1
    simp
    apply Exists.intro (i + j)
    rw [← eq]
    exact append_exp_sum L s t i j hs ht


theorem append_kleene_closure_closed
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (h1 : s ∈ kleene_closure α L)
  (h2 : t ∈ kleene_closure α L) :
  s ++ t ∈ kleene_closure α L :=
  by
    simp only [kleene_closure_eq_union_exp] at *
    simp at *
    obtain ⟨m, hs⟩ := h1
    obtain ⟨n, ht⟩ := h2
    apply Exists.intro (m + n)
    exact append_exp_sum L s t m n hs ht


-- Each l is the concatenation of a list of strings, each of which is in L.
def kleene_closure_set
  (α : Type)
  (L : Language α) :=
  { l | ∃ M : List (Str α), (∀ (r : Str α), r ∈ M → r ∈ L) ∧ l = M.join }


lemma kleene_closure_set_eq_kleene_closure_left
  {α : Type}
  (L : Language α) :
  kleene_closure_set α L ⊆ kleene_closure α L :=
  by
    simp only [Set.subset_def]
    intro cs a1
    simp only [kleene_closure_set] at a1
    simp at a1
    obtain ⟨M, a2_left, a2_right⟩ := a1
    simp only [a2_right]
    clear a2_right
    simp only [kleene_closure_eq_union_exp]
    simp
    induction M
    case nil =>
      apply Exists.intro 0
      simp only [exp]
      simp
    case cons hd tl ih =>
      simp at a2_left
      cases a2_left
      case _ a2_left_left a2_left_right =>
        specialize ih a2_left_right
        simp
        obtain ⟨i, a3⟩ := ih
        apply Exists.intro (i + 1)
        exact append_mem_exp_right L hd tl.join i a2_left_left a3


lemma kleene_closure_set_eq_kleene_closure_right
  {α : Type}
  [DecidableEq α]
  (L : Language α) :
  kleene_closure α L ⊆ kleene_closure_set α L :=
  by
    simp only [Set.subset_def]
    intro cs a1
    simp only [kleene_closure_set]
    simp

    induction a1
    case eps =>
      apply Exists.intro []
      simp
    case succ s t _ ih_2 ih_3 =>
      obtain ⟨M, a2, a3⟩ := ih_3
      rw [a3]
      apply Exists.intro (M ++ [t])
      constructor
      · intro r a4
        simp at a4
        cases a4
        case _ a4_left =>
          exact a2 r a4_left
        case _ a4_right =>
          simp only [a4_right]
          exact ih_2
      · simp


theorem kleene_closure_set_eq_kleene_closure
  (α : Type)
  [DecidableEq α]
  (L : Language α) :
  kleene_closure_set α L = kleene_closure α L :=
    Set.eq_of_subset_of_subset (kleene_closure_set_eq_kleene_closure_left L) (kleene_closure_set_eq_kleene_closure_right L)


theorem thm_6
  {α : Type}
  (L : Language α) :
  (kleene_closure α L) = {[]} ∪ (concat L (kleene_closure α L)) :=
  by
    ext cs
    constructor
    · intro a1
      simp only [kleene_closure_eq_union_exp] at a1
      simp at a1
      obtain ⟨i, a2⟩ := a1
      simp
      cases i
      case _ =>
        simp only [exp] at a2
        simp at a2
        left
        exact a2
      case _ k =>
        simp only [exp_succ_concat_left] at a2
        simp only [concat] at a2
        simp at a2
        obtain ⟨s, hs, t, ht, eq⟩ := a2
        right
        simp only [← eq]
        apply append_mem_concat
        · exact hs
        · exact Set.mem_of_mem_of_subset ht (exp_subset_kleene_closure L k)
    · intro a1
      simp at a1
      cases a1
      case _ a1_left =>
        simp only [a1_left]
        exact kleene_closure.eps L
      case _ a1_right =>
        simp only [kleene_closure_eq_union_exp L] at a1_right
        simp only [concat] at a1_right
        simp at a1_right
        obtain ⟨s, hs, t, ⟨i, ht⟩, eq⟩ := a1_right
        simp only [← eq]
        obtain s1 := append_mem_exp_right L s t i hs ht
        exact exp_subset_kleene_closure L (i + 1) s1


theorem corollary_1
  {α : Type}
  (L : Language α)
  (h1 : [] ∈ L) :
  kleene_closure α L = concat L (kleene_closure α L) :=
  by
    have s1 : {[]} ∪ concat L (kleene_closure α L) = concat L (kleene_closure α L) :=
    by
      apply Set.union_eq_self_of_subset_left
      simp
      simp only [concat]
      simp
      constructor
      · exact h1
      · exact kleene_closure.eps L

    obtain s2 := thm_6 L
    simp only [s1] at s2
    exact s2


lemma concat_kleene_closure_succ_left
  {α : Type}
  (L : Language α) :
  concat L (⋃ (n : ℕ), exp L n) = ⋃ (n : ℕ), exp L (n + 1) :=
  by
    ext cs
    constructor
    · intro a1
      simp only [concat] at a1
      simp at a1
      obtain ⟨s, hs, t, ⟨i, ht⟩, eq⟩ := a1
      rw [← eq]
      simp only [exp]
      simp
      apply Exists.intro i
      exact append_mem_exp_right L s t i hs ht
    · intro a1
      simp at a1
      obtain ⟨i, a2⟩ := a1
      simp only [exp] at a2
      simp only [concat_exp_comm] at a2
      simp only [concat] at a2
      simp at a2
      obtain ⟨s, hs, t, ht, eq⟩ := a2
      simp only [concat]
      simp
      exact ⟨s, hs, t, ⟨i, ht⟩, eq⟩


lemma concat_kleene_closure_succ_right
  {α : Type}
  (L : Language α) :
  concat (⋃ (n : ℕ), exp L n) L = ⋃ (n : ℕ), exp L (n + 1) :=
  by
    ext cs
    constructor
    · intro a1
      simp only [concat] at a1
      simp at a1
      obtain ⟨s, ⟨i, hs⟩,  t, ht, eq⟩ := a1
      simp
      rw [← eq]
      simp only [exp]
      apply Exists.intro i
      exact append_mem_exp_left L s t i hs ht
    · intro a1
      simp at a1
      obtain ⟨i, a2⟩ := a1
      simp only [exp] at a2
      simp only [concat] at a2
      simp at a2
      obtain ⟨s, hs, t, ht, eq⟩ := a2
      simp only [concat]
      simp
      exact ⟨s, ⟨i, hs⟩, t, ht, eq⟩


theorem thm_7
  {α : Type}
  (L : Language α) :
  concat L (kleene_closure α L) = concat (kleene_closure α L) L :=
  by
    simp only [kleene_closure_eq_union_exp]
    simp only [concat_kleene_closure_succ_left]
    simp only [concat_kleene_closure_succ_right]


theorem thm_8
  {α : Type}
  (L : Language α) :
  kleene_closure α L = kleene_closure α (kleene_closure α L) :=
  by
    apply Set.eq_of_subset_of_subset
    · exact language_subset_kleene_closure (kleene_closure α L)
    · simp only [Set.subset_def]
      intro cs a1
      induction a1
      case _ =>
        apply kleene_closure.eps L
      case _ s t _ ih_2 ih_3 =>
        exact append_kleene_closure_closed L s t ih_3 ih_2


theorem corollary_2
  {α : Type}
  (L : Language α) :
  kleene_closure α L =
    concat (kleene_closure α L) (kleene_closure α L) :=
  by
    have s1 : {[]} ∪ concat (kleene_closure α L) (kleene_closure α (kleene_closure α L)) = concat (kleene_closure α L) (kleene_closure α (kleene_closure α L)) :=
      by
        apply Set.union_eq_self_of_subset_left
        simp
        simp only [concat]
        simp
        constructor
        · exact kleene_closure.eps L
        · exact kleene_closure.eps (kleene_closure α L)

    calc
      kleene_closure α L = kleene_closure α (kleene_closure α L) := thm_8 L

      _ = {[]} ∪ (concat (kleene_closure α L) (kleene_closure α (kleene_closure α L))) := thm_6 (kleene_closure α L)

      _ = concat (kleene_closure α L) (kleene_closure α (kleene_closure α L)) := s1

      _ = concat (kleene_closure α L) (kleene_closure α L) :=
        by simp only [← thm_8]


theorem thm_9
  {α : Type}
  (L1 L2 X : Language α)
  (h1 : X = concat (kleene_closure α L1) L2) :
  X = (concat L1 X) ∪ L2 :=
  by
    calc
      X = concat (kleene_closure α L1) L2 := h1

      _ = concat ({[]} ∪ concat L1 (kleene_closure α L1)) L2 :=
        by simp only [← thm_6]

      _ = concat ((concat L1 (kleene_closure α L1)) ∪ {[]}) L2 :=
        by
          simp only [Set.union_comm (concat L1 (kleene_closure α L1))]

      _ = concat L1 (concat (kleene_closure α L1) L2) ∪ L2 :=
        by
          simp only [concat_distrib_union_right]
          simp only [concat_eps_left]
          simp only [concat_assoc]

      _ = (concat L1 X) ∪ L2 :=
        by simp only [h1]


lemma thm_9_unique_left_aux
  {α : Type}
  (L1 L2 X : Language α)
  (h1 : X = (concat L1 X) ∪ L2) :
  ∀ (n : ℕ), concat (exp L1 n) L2 ⊆ X :=
  by
    intro n
    induction n
    case zero =>
      simp only [exp]
      simp only [concat_eps_left]
      rw [h1]
      exact Set.subset_union_right (concat L1 X) L2
    case succ n ih =>
      have s1 : concat L1 (concat (exp L1 n) L2) ⊆ concat L1 X :=
      by
        apply concat_subset_left
        exact ih

      simp only [concat_assoc] at s1
      simp only [← exp_succ_concat_left] at s1

      have s2 : concat L1 X ⊆ X :=
      by
        conv => right; rw [h1]
        exact Set.subset_union_left (concat L1 X) L2

      trans (concat L1 X)
      · exact s1
      · exact s2


theorem thm_9_unique_left
  {α : Type}
  (L1 L2 X : Language α)
  (h1 : X = (concat L1 X) ∪ L2) :
  concat (kleene_closure α L1) L2 ⊆ X :=
  by
    simp only [kleene_closure_eq_union_exp]
    simp only [Set.subset_def]
    intro cs a1
    simp only [concat] at a1
    simp at a1
    obtain ⟨s, ⟨i, hs⟩, t, ht, eq⟩ := a1
    rw [← eq]
    obtain s1 := thm_9_unique_left_aux L1 L2 X h1 i
    apply Set.mem_of_subset_of_mem s1
    simp only [concat]
    simp
    exact ⟨s, hs, t, ht, rfl⟩


theorem thm_9_unique_right
  {α : Type}
  (L1 L2 X : Language α)
  (h1 : X = (concat L1 X) ∪ L2)
  (h2 : [] ∉ L1) :
  X ⊆ concat (kleene_closure α L1) L2
  | x, a1 => by
    rw [h1] at a1
    simp only [concat] at a1
    simp at a1
    obtain ⟨s, hs, t, ht, eq⟩ | hx := a1
    · simp only [← eq]
      simp only [concat]
      simp
      have ht' := ht
      rw [h1] at ht'
      simp at ht'
      obtain _ | ht1 := ht'
      · have : t.length < x.length :=
        by
          simp only [← eq]
          apply Strings.str_append_length_left
          intro contra
          simp only [contra] at hs
          contradiction
        have IH := thm_9_unique_right L1 L2 X h1 h2 ht
        simp only [concat] at IH
        simp at IH
        obtain ⟨s', hs', t', ht', eq'⟩ := IH
        apply Exists.intro (s ++ s')
        constructor
        · apply append_kleene_closure_closed
          · apply mem_language_mem_kleene_closure
            exact hs
          · exact hs'
        · apply Exists.intro t'
          constructor
          · exact ht'
          · simp
            exact eq'
      · apply Exists.intro s
        constructor
        · apply mem_language_mem_kleene_closure L1 s hs
        · apply Exists.intro t
          tauto
    · apply append_mem_concat_eps_left
      · apply eps_mem_kleene_closure
      · exact hx
termination_by x => x.length


theorem thm_9_unique
  {α : Type}
  (L1 L2 X : Language α)
  (h1 : X = (concat L1 X) ∪ L2)
  (h2 : [] ∉ L1) :
  concat (kleene_closure α L1) L2 = X :=
  Set.eq_of_subset_of_subset (thm_9_unique_left L1 L2 X h1) (thm_9_unique_right L1 L2 X h1 h2)
