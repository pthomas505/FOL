import FOL.Parsing.Language.Concat


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577


namespace Languages


/-
Definition 12 (Exponentiation). Let L be a language. The exponentiation or powers of L is defined by
1. L^0 = {ε}
2. L^(n+1) = L^(n)L n ∈ N
-/
def exp
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  Language α :=
  match n with
  | 0 => {[]}
  | n + 1 => concat (exp L n) L


lemma exp_zero
  {α : Type}
  (L : Language α) :
  exp L 0 = {[]} :=
  by
    rfl


lemma exp_one
  {α : Type}
  (L : Language α) :
  exp L 1 = L :=
  by
    simp only [exp]
    simp only [concat]
    simp


lemma exp_succ_concat_right
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  exp L (n + 1) = concat (exp L n) L :=
  by
    rfl

-------------------------------------------------------------------------------

lemma nonempty_exp_nonempty
  {α : Type}
  (L : Language α)
  (n : ℕ)
  (h1 : L.Nonempty) :
  (exp L n).Nonempty :=
  by
    induction n
    case zero =>
      simp only [Set.Nonempty]
      simp only [exp]
      apply Exists.intro []
      simp
    case succ k ih =>
      simp only [exp]
      simp only [concat_nonempty_iff]
      exact ⟨ih, h1⟩


lemma exp_succ_nonempty_nonempty
  {α : Type}
  (L : Language α)
  (n : ℕ)
  (h1 : (exp L (n + 1)).Nonempty) :
  Set.Nonempty (exp L n) ∧ Set.Nonempty L :=
  by
    simp only [exp] at h1
    simp only [concat_nonempty_iff] at h1
    exact h1

-------------------------------------------------------------------------------

lemma eps_mem_eps_mem_exp
  {α : Type}
  (L : Language α)
  (n : ℕ)
  (h1 : [] ∈ L) :
  [] ∈ exp L n :=
  by
    induction n
    case zero =>
      simp only [exp]
      simp
    case succ k ih =>
      simp only [exp]
      simp only [eps_mem_concat_iff]
      exact ⟨ih, h1⟩


lemma eps_mem_exp_succ_eps_mem
  {α : Type}
  (L : Language α)
  (n : ℕ)
  (h1 : [] ∈ exp L (n + 1)) :
  [] ∈ exp L n ∧ [] ∈ L :=
  by
    simp only [exp] at h1
    simp only [eps_mem_concat_iff] at h1
    exact h1

-------------------------------------------------------------------------------

lemma concat_exp_comm
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  concat (exp L n) L = concat L (exp L n) :=
  by
    induction n
    case zero =>
      simp only [exp]
      simp only [concat]
      simp
    case succ k ih =>
      simp only [exp]
      conv => left; simp only [ih]
      simp only [concat_assoc]


lemma exp_succ_concat_left
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  exp L (n + 1) = concat L (exp L n) :=
  by
    simp only [exp]
    exact concat_exp_comm L n


lemma concat_exp_assoc
  {α : Type}
  (L : Language α)
  (m n : ℕ) :
  concat (exp L (m + 1)) (exp L n) = concat (exp L m) (exp L (n + 1)) :=
  by
    simp only [exp]
    rw [← concat_assoc]
    rw [concat_exp_comm]


lemma concat_exp_sum
  {α : Type}
  (L : Language α)
  (m n : ℕ) :
  concat (exp L m) (exp L n) = exp L (m + n) :=
  by
    induction m generalizing n
    case zero =>
      simp only [exp]
      simp
      exact concat_eps_left (exp L n)
    case succ k ih =>
      simp only [concat_exp_assoc]
      rw [Nat.succ_add_eq_add_succ]
      exact ih (n + 1)


lemma concat_exp_exp_comm
  {α : Type}
  (L : Language α)
  (m n : ℕ) :
  concat (exp L m) (exp L n) = concat (exp L n) (exp L m) :=
  by
    simp only [concat_exp_sum]
    rw [Nat.add_comm m n]

-------------------------------------------------------------------------------

lemma exp_sum
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (m n : ℕ)
  (h1 : s ∈ exp L m)
  (h2 : t ∈ exp L n) :
  s ++ t ∈ exp L (m + n) :=
  by
    obtain s1 := concat_exp_sum L m n
    rw [← s1]
    exact append_mem_concat (exp L m) (exp L n) s t h1 h2


lemma append_mem_exp_left
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (n : ℕ)
  (h1 : s ∈ exp L n)
  (h2 : t ∈ L) :
  s ++ t ∈ exp L (n + 1) :=
  by
    rw [← exp_one L] at h2
    exact exp_sum L s t n 1 h1 h2


lemma append_mem_exp_right
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (n : ℕ)
  (h1 : s ∈ L)
  (h2 : t ∈ exp L n) :
  s ++ t ∈ exp L (n + 1) :=
  by
    rw [← exp_one L] at h1
    rw [Nat.add_comm]
    exact exp_sum L s t 1 n h1 h2


lemma eps_mem_exp_subset_exp_add_nat
  {α : Type}
  (L : Language α)
  (m n : ℕ)
  (h1 : [] ∈ L) :
  exp L m ⊆ exp L (m + n) :=
  by
    obtain s1 := concat_exp_sum L m n
    rw [← s1]
    have s2 : [] ∈ exp L n := eps_mem_eps_mem_exp L n h1
    exact eps_mem_right_left_subset_concat (exp L m) (exp L n) s2

-------------------------------------------------------------------------------

lemma concat_exp_comm_union
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  concat (⋃ (k ≤ n), exp L k) L = concat L (⋃ (k ≤ n), exp L k) :=
  by
    induction n
    case zero =>
      simp
      simp only [exp]
      simp only [concat]
      simp
    case succ i ih =>
      simp only [Set.biUnion_le_succ (exp L)]
      simp only [concat_distrib_union_right]
      simp only [concat_distrib_union_left]
      simp only [ih]
      simp only [concat_exp_comm]


lemma exp_succ_concat_right_union
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  ⋃ (k ≤ n), exp L (k + 1) =
    concat (⋃ (k ≤ n), exp L k) L :=
  by
    ext cs
    constructor
    · intro a1
      simp only [exp] at a1
      simp only [concat] at a1
      simp at a1
      obtain ⟨i, hi, s, hs, t, ht, eq⟩ := a1
      simp only [concat]
      simp
      exact ⟨s, ⟨i, ⟨hi, hs⟩ ⟩, ⟨t, ht, eq⟩⟩
    · intro a1
      simp only [concat] at a1
      simp at a1
      obtain ⟨s, ⟨i, hi, hs⟩, t, ht, eq⟩ := a1
      simp only [exp]
      simp only [concat]
      simp
      exact ⟨i, hi, s, hs, t, ht, eq⟩


lemma exp_succ_concat_left_union
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  (⋃ (k ≤ n), exp L (k + 1)) =
    concat L (⋃ (k ≤ n), exp L k) :=
  by
    simp only [← concat_exp_comm_union]
    exact exp_succ_concat_right_union L n


example
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (n : ℕ)
  (h1 : s ∈ ⋃ (k ≤ n), exp L k)
  (h2 : t ∈ L) :
  s ++ t ∈ ⋃ (k ≤ n), exp L (k + 1) :=
  by
    simp at h1
    obtain ⟨i, hi, hs⟩ := h1
    simp
    obtain s1 := append_mem_exp_left L s t i hs h2
    exact ⟨i, hi, s1⟩


example
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (n : ℕ)
  (h1 : s ∈ L)
  (h2 : t ∈ ⋃ (k ≤ n), exp L k) :
  s ++ t ∈ ⋃ (k ≤ n), exp L (k + 1) :=
  by
    simp only [exp_succ_concat_right_union]
    simp only [concat_exp_comm_union]
    exact append_mem_concat L (⋃ k, ⋃ (_ : k ≤ n), exp L k) s t h1 h2


example
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (m n : ℕ)
  (h1 : s ∈ ⋃ (k ≤ m), exp L k)
  (h2 : t ∈ ⋃ (k ≤ n), exp L k) :
  s ++ t ∈ ⋃ (k ≤ m + n), exp L k :=
  by
    cases m
    case zero =>
      simp at h1
      simp only [exp] at h1
      simp at h1
      simp at h2
      simp only [h1]
      simp
      exact h2
    case succ k =>
      simp at *
      obtain ⟨i, hi, hs⟩ := h1
      obtain ⟨j, hj, ht⟩ := h2
      apply Exists.intro (i + j)
      constructor
      · exact Nat.add_le_add hi hj
      · exact exp_sum L s t i j hs ht


example
  {α : Type}
  (L : Language α)
  (m n : ℕ) :
  ⋃ (k ≤ m), exp L k ⊆ ⋃ (k ≤ m + n), exp L k :=
  by
    simp
    intro k a1
    simp only [Set.subset_def]
    intro cs a2
    simp
    apply Exists.intro k
    constructor
    · exact le_add_right a1
    · exact a2


example
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  [] ∈ ⋃ (k ≤ n), exp L k :=
  by
    induction n
    case zero =>
      simp
      simp only [exp]
      simp
    case succ k ih =>
      simp at ih
      obtain ⟨i, hi, a1⟩ := ih
      simp
      have s1 : i ≤ k + 1 := Nat.le_succ_of_le hi
      exact ⟨i, s1, a1⟩


-------------------------------------------------------------------------------

lemma eps_not_mem_imp_mem_len_ge_exp
  {α : Type}
  (L : Language α)
  (s : Str α)
  (n : ℕ)
  (h1 : [] ∉ L)
  (h2 : s ∈ exp L (n + 1)) :
  s.length > n :=
  by
    induction n generalizing s
    case zero =>
      simp only [exp] at h2
      simp only [concat] at h2
      simp at h2
      exact eps_not_mem_str_length_gt_zero L s h1 h2
    case succ k ih =>
      rw [exp] at h2
      simp only [concat] at h2
      simp at h2
      obtain ⟨s, hs, t, ht, eq⟩ := h2
      rw [← eq]
      simp
      specialize ih s hs
      have s1 : t.length > 0 := eps_not_mem_str_length_gt_zero L t h1 ht
      exact Nat.add_lt_add_of_lt_of_le ih s1


example
  {α : Type}
  (L : Language α)
  (x : Str α)
  (h1 : [] ∉ L) :
  x ∉ exp L (x.length + 1) :=
  by
    intro contra
    obtain s1 := eps_not_mem_imp_mem_len_ge_exp L x x.length h1 contra
    simp at s1


lemma eps_not_mem_imp_mem_concat_exp_ge_exp
  {α : Type}
  (L M : Language α)
  (x : Str α)
  (n : ℕ)
  (h1 : [] ∉ L)
  (h2 : x ∈ concat (exp L (n + 1)) M) :
  x.length > n :=
  by
    simp only [concat] at h2
    simp at h2
    obtain ⟨s, hs, t, _, eq⟩ := h2
    rw [← eq]
    simp
    have s1 : s.length > n := eps_not_mem_imp_mem_len_ge_exp L s n h1 hs
    exact Nat.lt_add_right (List.length t) s1


lemma eps_not_mem_imp_not_mem_concat_exp
  {α : Type}
  (L M : Language α)
  (x : Str α)
  (h1 : [] ∉ L) :
  x ∉ concat (exp L (x.length + 1)) M :=
  by
    intro contra
    obtain s1 := eps_not_mem_imp_mem_concat_exp_ge_exp L M x x.length h1 contra
    simp at s1
