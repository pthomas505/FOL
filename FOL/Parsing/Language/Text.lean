import FOL.Parsing.Language.Exp


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577


-------------------------------------------------------------------------------

namespace Languages



-------------------------------------------------------------------------------

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


example
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
    simp only [a1]
    exact kleene_closure.eps ∅


theorem thm_4
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


lemma lang_sub_kleene_closure
  {α : Type}
  (L : Language α) :
  L ⊆ kleene_closure α L :=
  by
    conv => left; rw [← exp_one L]
    exact thm_4 L 1


lemma mem_lang_imp_mem_kleene_closure
  {α : Type}
  (L : Language α)
  (x : Str α)
  (h1 : x ∈ L) :
  x ∈ kleene_closure α L :=
  by
    obtain s1 := lang_sub_kleene_closure L
    exact Set.mem_of_subset_of_mem s1 h1


theorem thm_5_left
  {α : Type}
  (L : Language α) :
  ⋃ (n : ℕ), exp L n ⊆ kleene_closure α L :=
  by
    simp only [Set.subset_def]
    intro cs a1
    simp at a1
    apply Exists.elim a1
    intro n a2
    exact Set.mem_of_subset_of_mem (thm_4 L n) a2


theorem thm_5_right
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


theorem thm_5
  {α : Type}
  (L : Language α) :
  kleene_closure α L = ⋃ (n : ℕ), exp L n :=
    Set.eq_of_subset_of_subset (thm_5_right L) (thm_5_left L)


theorem kleene_closure_closed_concat
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (h1 : s ∈ kleene_closure α L)
  (h2 : t ∈ kleene_closure α L) :
  s ++ t ∈ kleene_closure α L :=
  by
    simp only [thm_5] at *
    simp at *
    obtain ⟨m, hs⟩ := h1
    obtain ⟨n, ht⟩ := h2
    apply Exists.intro (m + n)
    exact exp_sum L s t m n hs ht


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
    simp only [thm_5]
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
      simp only [thm_5] at a1
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
        · exact Set.mem_of_mem_of_subset ht (thm_4 L k)
    · intro a1
      simp at a1
      cases a1
      case _ a1_left =>
        simp only [a1_left]
        exact kleene_closure.eps L
      case _ a1_right =>
        simp only [thm_5 L] at a1_right
        simp only [concat] at a1_right
        simp at a1_right
        obtain ⟨s, hs, t, ⟨i, ht⟩, eq⟩ := a1_right
        simp only [← eq]
        obtain s1 := append_mem_exp_right L s t i hs ht
        exact thm_4 L (i + 1) s1


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
    simp only [thm_5]
    simp only [concat_kleene_closure_succ_left]
    simp only [concat_kleene_closure_succ_right]


theorem thm_8
  {α : Type}
  (L : Language α) :
  kleene_closure α L = kleene_closure α (kleene_closure α L) :=
  by
    apply Set.eq_of_subset_of_subset
    · exact lang_sub_kleene_closure (kleene_closure α L)
    · simp only [Set.subset_def]
      intro cs a1
      induction a1
      case _ =>
        apply kleene_closure.eps L
      case _ s t _ ih_2 ih_3 =>
        exact kleene_closure_closed_concat L s t ih_3 ih_2


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
    simp only [thm_5]
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
        · apply kleene_closure_closed_concat
          · apply mem_lang_imp_mem_kleene_closure
            exact hs
          · exact hs'
        · apply Exists.intro t'
          constructor
          · exact ht'
          · simp
            exact eq'
      · apply Exists.intro s
        constructor
        · apply mem_lang_imp_mem_kleene_closure L1 s hs
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


/-
Definition 15 (String derivative). The derivative of a language L ⊆ Σ∗ with respect to a string s ∈ Σ∗ is defined to be ∂sL = {t : s · t ∈ L}.
-/

def derivative
  {α : Type}
  (L : Language α)
  (s : Str α) :
  Language α :=
  { t : Str α | s ++ t ∈ L }


theorem thm_11_a
  {α : Type}
  (L : Language α) :
  derivative L [] = L :=
  by
    simp only [derivative]
    simp

theorem thm_11_b
  {α : Type}
  (L : Language α)
  (s t : Str α) :
  derivative L (s ++ t) = derivative (derivative L s) t :=
  by
    simp only [derivative]
    simp


-- [a] ∈ Σ^1

-- 1.50
theorem thm_12_1
  {α : Type}
  (a : α) :
  derivative ∅ [a] = ∅ :=
  by
    simp only [derivative]
    simp


theorem thm_12_1_str
  {α : Type}
  (s : Str α) :
  derivative ∅ s = ∅ :=
  by
    simp only [derivative]
    simp


-- 1.51
theorem thm_12_2
  {α : Type}
  (a : α) :
  derivative {[]} [a] = ∅ :=
  by
    simp only [derivative]
    simp


-- 1.52
theorem thm_12_3
  {α : Type}
  (a : α) :
  derivative {[a]} [a] = {[]} :=
  by
    simp only [derivative]
    simp


theorem thm_12_3_str
  {α : Type}
  (s : Str α) :
  derivative {s} s = {[]} :=
  by
    simp only [derivative]
    simp


-- 1.53
theorem thm_12_4
  {α : Type}
  (a b : α)
  (h1 : ¬ a = b) :
  derivative {[b]} [a] = ∅ :=
  by
    simp only [derivative]
    simp
    simp only [h1]
    simp


-- 1.54
theorem thm_12_5
  {α : Type}
  (L1 L2 : Language α)
  (a : α) :
  derivative (L1 ∪ L2) [a] =
    (derivative L1 [a]) ∪ (derivative L2 [a]) :=
  by
    simp only [derivative]
    rfl


theorem thm_12_5_str
  {α : Type}
  (L1 L2 : Language α)
  (s : Str α) :
  derivative (L1 ∪ L2) s =
    (derivative L1 s) ∪ (derivative L2 s) :=
  by
    simp only [derivative]
    rfl


-- 1.55
theorem thm_12_6
  {α : Type}
  (L1 L2 : Language α)
  (a : α) :
  derivative (L1 ∩ L2) [a] =
    (derivative L1 [a]) ∩ (derivative L2 [a]) :=
  by
    simp only [derivative]
    rfl


theorem thm_12_6_str
  {α : Type}
  (L1 L2 : Language α)
  (s : Str α) :
  derivative (L1 ∩ L2) s =
    (derivative L1 s) ∩ (derivative L2 s) :=
  by
    simp only [derivative]
    rfl


/-
  If [] ∈ L1 then let L0 be L1 \ {[]}. If [] ∉ L1 then let L0 be L1.
-/
lemma thm_12_7_1
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


lemma thm_12_7_2
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (a : α) :
  {s | a :: s ∈ (concat L1.nullify L2)} = concat L1.nullify (derivative L2 [a]) :=
  by
    simp only [derivative]
    simp only [concat]
    simp
    ext cs
    simp
    constructor
    · intro a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1
      cases s
      case nil =>
        simp at eq
        rw [eq] at ht
        exact ⟨[], hs, cs, ⟨ht, by simp⟩⟩
      case cons s_hd s_tl =>
        simp only [Language.nullify] at hs
        simp at hs
    · intro a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1
      cases s
      case nil =>
        simp at eq
        rw [eq] at ht
        exact ⟨[], hs, (a :: cs), ht, by simp⟩
      case cons s_hd s_tl s_ih =>
        simp only [Language.nullify] at hs
        simp at hs


lemma thm_12_7_2_str
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (a : Str α) :
  {s | a ++ s ∈ (concat L1.nullify L2)} = concat L1.nullify (derivative L2 a) :=
  by
    simp only [derivative]
    simp only [concat]
    simp
    ext cs
    simp
    constructor
    · intro a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1
      cases s
      case nil =>
        simp at eq
        rw [eq] at ht
        exact ⟨[], hs, cs, ⟨ht, by simp⟩⟩
      case cons s_hd s_tl =>
        simp only [Language.nullify] at hs
        simp at hs
    · intro a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1
      cases s
      case nil =>
        simp at eq
        rw [eq] at ht
        exact ⟨[], hs, (a ++ cs), ht, by simp⟩
      case cons s_hd s_tl s_ih =>
        simp only [Language.nullify] at hs
        simp at hs


lemma thm_12_7_3
  {α : Type}
  [DecidableEq α]
  (L0 L2 : Language α)
  (a : α)
  (h1 : L0.nullify = ∅) :
  {t | a :: t ∈ concat L0 L2} = {t | ∃ t0 t2, a :: t0 ∈ L0 ∧ t2 ∈ L2 ∧ t0 ++ t2 = t} :=
  by
    simp only [Language.nullify] at h1
    simp at h1

    simp only [concat]
    simp
    ext cs
    constructor
    · simp
      intro s a1 t a2 a3
      cases s
      case nil =>
        contradiction
      case cons s_hd s_tl =>
        simp at a3
        cases a3
        case _ a3_left a3_right =>
          simp only [a3_left] at a1
          exact ⟨s_tl, a1, t, ⟨a2, a3_right⟩⟩
    · simp
      intro s a1 t a2 a3
      rw [← a3]
      exact ⟨a :: s, a1, t, a2, by simp⟩


-- 1.56
theorem thm_12_7
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (a : α) :
  derivative (concat L1 L2) [a] =
    (concat (derivative L1 [a]) L2) ∪ (concat L1.nullify (derivative L2 [a])) :=
  by
    have s1 : ∀ (L0 : Language α), L0.nullify = ∅ →
      derivative (concat (L1.nullify ∪ L0) L2) [a] =
        (concat L1.nullify (derivative L2 [a])) ∪ (concat (derivative L0 [a]) L2) :=
    by
      intro L0 a1
      calc
      derivative (concat (L1.nullify ∪ L0) L2) [a] =
        {s | a :: s ∈ concat (L1.nullify ∪ L0) L2} :=
      by
        simp only [derivative]
        rfl

      _ = {s | a :: s ∈ concat L1.nullify L2} ∪ {t | a :: t ∈ concat L0 L2} :=
      by
        obtain s3 := concat_distrib_union_right L1.nullify L0 L2
        simp only [s3]
        rfl

      _ = (concat L1.nullify (derivative L2 [a])) ∪ {t | ∃ t0 t2, a :: t0 ∈ L0 ∧ t2 ∈ L2 ∧ t0 ++ t2 = t} :=
      by
        obtain s3_1 := thm_12_7_2 L1 L2 a
        simp only [s3_1]
        obtain s3_2 := thm_12_7_3 L0 L2 a a1
        simp only [s3_2]

      _ = (concat L1.nullify (derivative L2 [a])) ∪ concat {t0 | a :: t0 ∈ L0} L2 :=
      by
        simp only [concat]
        simp

      _ = (concat L1.nullify (derivative L2 [a])) ∪ (concat (derivative L0 [a]) L2) :=
      by
        simp only [derivative]
        rfl

    have s2 : ∀ (L0 : Language α), derivative (L1.nullify ∪ L0) [a] = derivative L0 [a] :=
    by
      intro L0
      simp only [derivative]
      simp only [Language.nullify]
      simp

    obtain s3 := thm_12_7_1 L1
    cases s3
    case _ L0 a1 =>
      cases a1
      case _ a1_left a1_right =>
        specialize s1 L0 a1_left
        specialize s2 L0
        simp only [← a1_right] at s1
        simp only [← a1_right] at s2
        simp only [s2]
        simp only [s1]
        exact Set.union_comm (concat L1.nullify (derivative L2 [a])) (concat (derivative L0 [a]) L2)


theorem thm_12_7_str
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (s : Str α) :
  let B := { M | ∃ (u : Str α) (v : Str α), u ++ v = s ∧ v.length > 0 ∧ M = concat (derivative L1 u).nullify (derivative L2 v) }
  derivative (concat L1 L2) s = (concat (derivative L1 s) L2) ∪ ⋃₀ B :=
  by
    ext t
    simp [derivative, concat, Language.nullify]
    constructor
    · rintro ⟨u, hu, v, hv, eq⟩
      obtain ⟨w, rfl, rfl⟩ | ⟨w, rfl, rfl⟩ := List.append_eq_append_iff.1 eq
      · by_cases hw : w = []
        · subst w; simp at *
          exact .inl ⟨[], by simpa, _, hv, rfl⟩
        · exact .inr ⟨_, ⟨u, _, rfl, hw, rfl⟩, _, ⟨hu, rfl⟩, _, hv, rfl⟩
      · exact .inl ⟨_, hu, _, hv, rfl⟩
    · rintro (⟨u, hu, v, hv, rfl⟩ | ⟨_, ⟨u, v, rfl, _, rfl⟩, _, ⟨hu, rfl⟩, _, hv, rfl⟩) <;>
        exact ⟨_, hu, _, hv, by simp⟩


-- 1.59
lemma derivative_exp_succ
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a : α)
  (k : ℕ) :
  derivative (exp L (k + 1)) [a] =
    concat (derivative L [a]) (exp L k) :=
  by
    induction k
    case zero =>
      simp
      simp only [exp]
      simp only [concat]
      simp
    case succ k ih =>
      rw [exp]
      simp only [concat_exp_comm]
      simp only [thm_12_7]
      simp only [Language.nullify]
      split_ifs
      case pos c1 =>
        simp only [concat_eps_left]
        simp only [ih]
        simp

        obtain s1 := eps_mem_exp_subset_exp_add_nat L k 1 c1

        exact concat_subset_left (derivative L [a]) (exp L k) (exp L (k + 1)) s1
      case neg c1 c2 =>
        simp only [concat]
        simp


lemma aux_1
  {α : Type}
  [DecidableEq α]
  (a : α)
  (f : ℕ → Language α) :
  ⋃ n, derivative (f n) [a] = derivative (⋃ n, f n) [a] :=
  by
    simp only [derivative]
    ext cs
    simp


lemma aux_1_str
  {α : Type}
  [DecidableEq α]
  (s : Str α)
  (f : ℕ → Language α) :
  ⋃ n, derivative (f n) s = derivative (⋃ n, f n) s :=
  by
    simp only [derivative]
    ext cs
    simp


lemma aux_2
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (f : ℕ → Language α) :
  ⋃ (n : ℕ), concat L (f n) = concat L (⋃ (n : ℕ), (f n)) :=
  by
    simp only [concat]
    ext cs
    simp
    constructor
    · intro a1
      obtain ⟨i, s, hs, t, ⟨ht, eq⟩⟩ := a1
      rw [← eq]
      exact ⟨s, hs, t, ⟨i, ht⟩, rfl⟩
    · intro a1
      obtain ⟨s, hs, t, ⟨i, ht⟩, eq⟩ := a1
      rw [← eq]
      exact ⟨i, s, hs, t, ht, rfl⟩


-- 1.57
theorem thm_12_8
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a : α) :
  derivative (kleene_closure α L) [a] = concat (derivative L [a]) (kleene_closure α L) :=
  by
    conv => left; simp only [thm_5]
    simp only [← Set.union_iUnion_nat_succ (exp L)]
    simp only [thm_12_5]
    simp only [exp_zero]
    simp only [thm_12_2]
    simp only [Set.empty_union]
    simp only [← aux_1]
    simp only [derivative_exp_succ]
    simp only [aux_2]
    simp only [thm_5]


-- 1.58
theorem thm_12_9
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a : α) :
  derivative Lᶜ [a] = (derivative L [a])ᶜ := rfl
  -- Why is this proof so short?


theorem thm_13
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (s : Str α) :
  s ∈ L ↔ [] ∈ derivative L s :=
  by
    simp only [derivative]
    simp


theorem corollary_3
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (s : Str α) :
  (derivative L s).nullify = {[]} ↔ s ∈ L :=
  by
    simp only [thm_13 L]
    simp only [Language.nullify]

    split_ifs
    case pos c1 =>
      simp
      exact c1
    case neg c1 =>
      simp only [c1]
      simp
      obtain s1 := Set.singleton_ne_empty []
      exact id (Ne.symm s1)


theorem thm_14
  {α : Type}
  [DecidableEq α]
  (L : Language α) :
  L = L.nullify ∪ ⋃ (a : α), concat {[a]} (derivative L [a]) :=
  by
    ext cs
    constructor
    · intro a1
      cases cs
      case _ =>
        simp
        left
        simp only [Language.nullify]
        simp only [a1]
        simp
      case _ hd tl =>
        simp
        right
        apply Exists.intro hd
        simp only [concat]
        simp
        simp only [derivative]
        simp
        exact a1
    · intro a1
      simp at a1
      cases a1
      case _ a1_left =>
        simp only [Language.nullify] at a1_left
        simp at a1_left
        cases a1_left
        case _ a1_left_left a1_left_right =>
          simp only [a1_left_right]
          exact a1_left_left
      case _ a1_right =>
        obtain ⟨i, a2⟩ := a1_right
        simp only [concat] at a2
        simp only [derivative] at a2
        simp at a2
        obtain ⟨t, ⟨a3_left, a3_right⟩⟩ := a2
        rw [← a3_right]
        exact a3_left


theorem thm_14_disjoint
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a b : α)
  (h1 : ¬ b = a) :
  concat {[a]} L ∩ concat {[b]} L = ∅ :=
  by
    ext cs
    simp only [concat]
    simp
    intro s _ a2 t _
    simp only [← a2]
    simp
    intro a4
    contradiction


lemma derivative_of_nullify
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a : α) :
  derivative (L.nullify) [a] = ∅ :=
  by
    simp only [derivative]
    simp
    simp only [Language.nullify]
    simp


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
    rw [thm_12_5_str L1 L2 s]
    rw [thm_12_5_str L1 L2 t]
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
    rw [thm_12_6_str L1 L2 s]
    rw [thm_12_6_str L1 L2 t]
    rw [h1]
    rw [h2]


-------------------------------------------------------------------------------


inductive IsRegLang (α : Type) : Language α → Prop
| char
  (a : α) :
  IsRegLang α {[a]}

| epsilon :
  IsRegLang α {[]}

| zero :
  IsRegLang α ∅

| union
  (R1 R2 : Language α) :
  IsRegLang α R1 →
  IsRegLang α R2 →
  IsRegLang α (R1 ∪ R2)

| concat
  (R1 R2 : Language α) :
  IsRegLang α R1 →
  IsRegLang α R2 →
  IsRegLang α (concat R1 R2)

| closure
  (R : Language α) :
  IsRegLang α R →
  IsRegLang α (kleene_closure α R)


theorem thm_17_aux
  {α : Type}
  [DecidableEq α]
  (R : Language α)
  (a : α)
  (h1 : IsRegLang α R) :
  IsRegLang α (derivative R [a]) :=
  by
    induction h1
    case char b =>
      by_cases c1 : a = b
      case pos =>
        rw [c1]
        simp only [thm_12_3]
        exact IsRegLang.epsilon
      case neg =>
        simp only [thm_12_4 a b c1]
        exact IsRegLang.zero
    case epsilon =>
      simp only [thm_12_2]
      exact IsRegLang.zero
    case zero =>
      simp only [thm_12_1]
      exact IsRegLang.zero
    case union R1 R2 ih_1 ih_2 ih_3 ih_4 =>
      simp only [thm_12_5]
      exact IsRegLang.union (derivative R1 [a]) (derivative R2 [a]) ih_3 ih_4
    case concat R1 R2 ih_1 ih_2 ih_3 ih_4 =>
      simp only [thm_12_7]
      apply IsRegLang.union
      · exact IsRegLang.concat (derivative R1 [a]) R2 ih_3 ih_2
      · apply IsRegLang.concat
        · simp only [Language.nullify]
          split_ifs
          case pos c1 =>
            exact IsRegLang.epsilon
          case neg c1 =>
            exact IsRegLang.zero
        · exact ih_4
    case closure R' ih_1 ih_2 =>
      simp only [thm_12_8]
      apply IsRegLang.concat
      · exact ih_2
      · exact IsRegLang.closure R' ih_1


theorem thm_17
  {α : Type}
  [DecidableEq α]
  (R : Language α)
  (s : Str α)
  (h1: IsRegLang α R) :
  IsRegLang α (derivative R s) :=
  by
    induction s generalizing R
    case nil =>
      simp only [derivative]
      simp
      exact h1
    case cons hd tl ih =>
      have s1 : hd :: tl = [hd] ++ tl := rfl
      rw [s1]
      clear s1

      rw [thm_11_b]
      apply ih
      apply thm_17_aux
      exact h1


example
  {α : Type}
  [DecidableEq α]
  (s : Str α) :
  derivative ∅ s = ∅ := rfl

example
  {α : Type}
  [DecidableEq α] :
  derivative {([] : Str α)} [] = {[]} := rfl

example
  {α : Type}
  [DecidableEq α]
  (s : Str α)
  (h1 : ¬ s = []) :
  derivative {([] : Str α)} s = ∅ :=
  by
    simp only [derivative]
    simp
    simp only [h1]
    simp

example
  {α : Type}
  [DecidableEq α]
  (a : α) :
  derivative {[a]} [] = {[a]} := rfl

example
  {α : Type}
  [DecidableEq α]
  (a : α) :
  derivative {[a]} [a] = {[]} :=
  by
    exact thm_12_3 a

example
  {α : Type}
  [DecidableEq α]
  (s : Str α)
  (a : α)
  (h1 : ¬ s = [])
  (h2 : ¬ s = [a]) :
  derivative {[a]} s = ∅ :=
  by
    cases s
    case nil =>
      simp at h1
    case cons hd tl =>
      simp at h2
      simp only [derivative]
      simp
      ext cs
      simp
      tauto


example
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (s : Str α) :
  derivative (L1 ∪ L2) s = derivative L1 s ∪ derivative L2 s := rfl


example
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a1 a2 : α) :
  derivative (kleene_closure α L) [a1, a2] =
    concat (derivative L [a1, a2]) (kleene_closure α L) ∪
      concat (derivative L [a1]).nullify (concat (derivative L [a2]) (kleene_closure α L)) :=
  by
    have s1 : [a1, a2] = [a1] ++ [a2] := rfl
    rw [s1]
    clear s1

    simp only [thm_11_b]
    rw [thm_12_8]
    rw [thm_12_7]
    rw [thm_12_8]


example
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a1 a2 a3 : α) :
  derivative (kleene_closure α L) [a1, a2, a3] =
    concat (derivative L [a1, a2, a3]) (kleene_closure α L) ∪
      concat (derivative L [a1, a2]).nullify (concat (derivative L [a3]) (kleene_closure α L)) ∪
        (concat (derivative L [a1]).nullify (concat (derivative L [a2, a3]) (kleene_closure α L) ∪
            concat (derivative L [a2]).nullify (concat (derivative L [a3]) (kleene_closure α L)))) :=
  by
    have s1 : [a1, a2, a3] = [a1] ++ [a2] ++ [a3] := rfl
    rw [s1]
    clear s1

    rw [thm_11_b]
    simp

    -----
    have s2 : [a1, a2] = [a1] ++ [a2] := rfl
    rw [s2]
    clear s2

    simp only [thm_11_b]
    rw [thm_12_8]
    rw [thm_12_7]
    rw [thm_12_8]
    -----

    rw [thm_12_5]
    simp only [thm_12_7]
    rw [thm_12_8]

    simp only [nullify_idempotent]
    simp only [derivative_of_nullify]
    simp only [concat_empty_left]
    simp
    simp only [← thm_11_b]
    simp


example
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a1 a2 a3 a4 : α) :
  derivative (kleene_closure α L) [a1, a2, a3, a4] =
    concat (derivative L [a1, a2, a3, a4]) (kleene_closure α L) ∪
      concat (concat (derivative L [a1, a2, a3]).nullify (derivative L [a4])) (kleene_closure α L) ∪
        (concat (concat (derivative L [a1, a2]).nullify (derivative L [a3, a4])) (kleene_closure α L) ∪
          concat (concat (concat (derivative L [a1, a2]).nullify (derivative L [a3]).nullify) (derivative L [a4])) (kleene_closure α L)) ∪
            (concat (concat (derivative L [a1]).nullify (derivative L [a2, a3, a4])) (kleene_closure α L) ∪
              concat (concat (concat (derivative L [a1]).nullify (derivative L [a2, a3]).nullify) (derivative L [a4])) (kleene_closure α L) ∪
                (concat (concat (concat (derivative L [a1]).nullify (derivative L [a2]).nullify) (derivative L [a3, a4])) (kleene_closure α L) ∪
                  concat (concat (concat (concat (derivative L [a1]).nullify (derivative L [a2]).nullify) (derivative L [a3]).nullify) (derivative L [a4])) (kleene_closure α L))) :=
  by
    have s1 : [a1, a2, a3, a4] = [a1] ++ [a2] ++ [a3] ++ [a4]:= rfl
    rw [s1]
    clear s1

    simp only [thm_11_b]
    simp only [thm_12_8, thm_12_7, thm_12_5]
    simp only [nullify_idempotent]
    simp only [derivative_of_nullify]
    simp only [thm_12_1]
    simp only [concat_empty_left]
    simp
    simp only [nullify_empty]
    simp only [concat_empty_left]
    simp
    simp only [← thm_11_b]
    simp
    simp only [concat_distrib_union_left]
    simp only [concat_assoc]


example
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (s : Str α)
  (h1 : ¬ s = []) :
  ∃ (T : List (List α)), T ⊆ s.tails ∧ [] ∉ T ∧
    derivative (kleene_closure α L) s =
    ⋃ t ∈ T, concat (derivative L t) (kleene_closure α L) :=
  by
    induction s generalizing L
    case nil =>
      simp at h1
    case cons hd tl ih =>
      have s1 : hd :: tl = [hd] ++ tl := rfl
      rw [s1]
      clear s1

      simp only [thm_11_b]
      simp
      simp only [thm_12_8]
      by_cases c1 : tl = []
      case pos =>
        subst c1
        simp
        apply Exists.intro [[hd]]
        simp
        rw [thm_11_a]
      case neg =>
        specialize ih L c1
        obtain ⟨T, ⟨a1, a2, a3⟩⟩ := ih
        sorry


theorem thm_18
  {α : Type}
  [DecidableEq α]
  (R : Language α)
  (h1: IsRegLang α R) :
  Finite { derivative R s | s : Str α } :=
  by
    sorry
