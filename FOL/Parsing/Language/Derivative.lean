import FOL.Parsing.Language.Nullable


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577


namespace Language


/-
Definition 15 (String derivative). The derivative of a language L ⊆ Σ∗ with respect to a string s ∈ Σ∗ is defined to be ∂sL = {t : s · t ∈ L}.
-/

def derivative
  {α : Type}
  (L : Language α)
  (s : Str α) :
  Language α :=
  { t : Str α | s ++ t ∈ L }


theorem derivative_wrt_eps
  {α : Type}
  (L : Language α) :
  derivative L [] = L :=
  by
    simp only [derivative]
    simp


theorem derivative_wrt_append
  {α : Type}
  (L : Language α)
  (s t : Str α) :
  derivative L (s ++ t) = derivative (derivative L s) t :=
  by
    simp only [derivative]
    simp


-- [a] ∈ Σ^1

-- 1.50
theorem derivative_of_empty_wrt_char
  {α : Type}
  (a : α) :
  derivative ∅ [a] = ∅ :=
  by
    simp only [derivative]
    simp


theorem derivative_of_empty_wrt_str
  {α : Type}
  (s : Str α) :
  derivative ∅ s = ∅ :=
  by
    simp only [derivative]
    simp


-- 1.51
theorem derivative_of_eps_wrt_char
  {α : Type}
  (a : α) :
  derivative {[]} [a] = ∅ :=
  by
    simp only [derivative]
    simp


-- 1.52
theorem derivative_of_char_wrt_same_char
  {α : Type}
  (a : α) :
  derivative {[a]} [a] = {[]} :=
  by
    simp only [derivative]
    simp


theorem derivative_of_str_wrt_same_str
  {α : Type}
  (s : Str α) :
  derivative {s} s = {[]} :=
  by
    simp only [derivative]
    simp


-- 1.53
theorem derivative_of_char_wrt_diff_char
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
theorem derivative_of_union_wrt_char
  {α : Type}
  (L1 L2 : Language α)
  (a : α) :
  derivative (L1 ∪ L2) [a] =
    (derivative L1 [a]) ∪ (derivative L2 [a]) :=
  by
    simp only [derivative]
    rfl


theorem derivative_of_union_wrt_str
  {α : Type}
  (L1 L2 : Language α)
  (s : Str α) :
  derivative (L1 ∪ L2) s =
    (derivative L1 s) ∪ (derivative L2 s) :=
  by
    simp only [derivative]
    rfl


-- 1.55
theorem derivative_of_intersection_wrt_char
  {α : Type}
  (L1 L2 : Language α)
  (a : α) :
  derivative (L1 ∩ L2) [a] =
    (derivative L1 [a]) ∩ (derivative L2 [a]) :=
  by
    simp only [derivative]
    rfl


theorem derivative_of_intersection_wrt_str
  {α : Type}
  (L1 L2 : Language α)
  (s : Str α) :
  derivative (L1 ∩ L2) s =
    (derivative L1 s) ∩ (derivative L2 s) :=
  by
    simp only [derivative]
    rfl


lemma concat_nullify_and_derivative_wrt_char
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


lemma concat_nullify_and_derivative_wrt_str
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


lemma derivative_of_concat_wrt_char_aux
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
theorem derivative_of_concat_wrt_char
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
        obtain s3_1 := concat_nullify_and_derivative_wrt_char L1 L2 a
        simp only [s3_1]
        obtain s3_2 := derivative_of_concat_wrt_char_aux L0 L2 a a1
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

    obtain s3 := lang_as_union_of_nullify_and_not_nullable L1
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


theorem derivative_of_concat_wrt_str
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
lemma derivative_of_exp_succ_wrt_char
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
      simp only [derivative_of_concat_wrt_char]
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


lemma derivative_distrib_union_of_countable_wrt_char
  {α : Type}
  [DecidableEq α]
  (a : α)
  (f : ℕ → Language α) :
  ⋃ n, derivative (f n) [a] = derivative (⋃ n, f n) [a] :=
  by
    simp only [derivative]
    ext cs
    simp


lemma derivative_distrib_union_of_countable_wrt_str
  {α : Type}
  [DecidableEq α]
  (s : Str α)
  (f : ℕ → Language α) :
  ⋃ n, derivative (f n) s = derivative (⋃ n, f n) s :=
  by
    simp only [derivative]
    ext cs
    simp


-- 1.57
theorem derivative_of_kleene_closure_wrt_char
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a : α) :
  derivative (kleene_closure α L) [a] = concat (derivative L [a]) (kleene_closure α L) :=
  by
    conv => left; simp only [kleene_closure_eq_union_exp]
    simp only [← Set.union_iUnion_nat_succ (exp L)]
    simp only [derivative_of_union_wrt_char]
    simp only [exp_zero]
    simp only [derivative_of_eps_wrt_char]
    simp only [Set.empty_union]
    simp only [← derivative_distrib_union_of_countable_wrt_char]
    simp only [derivative_of_exp_succ_wrt_char]
    simp only [concat_distrib_countable_union_left]
    simp only [kleene_closure_eq_union_exp]


-- 1.58
theorem derivative_of_complement_wrt_char
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a : α) :
  derivative Lᶜ [a] = (derivative L [a])ᶜ := rfl
  -- Why is this proof so short?


theorem str_mem_lang_iff_eps_mem_derivative
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (s : Str α) :
  s ∈ L ↔ [] ∈ derivative L s :=
  by
    simp only [derivative]
    simp


theorem str_mem_lang_iff_nullify_derivative_eq_eps
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (s : Str α) :
  s ∈ L ↔ (derivative L s).nullify = {[]} :=
  by
    simp only [str_mem_lang_iff_eps_mem_derivative L]
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


theorem lang_eq_union_nullify_union_concat_char_derivative_wrt_char
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


lemma derivative_of_nullify_wrt_char
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
