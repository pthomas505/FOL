import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577

/-
  Definition 1 (Alphabet). An alphabet is any, possibly infinite, set of symbols. We will use Σ to denote an alphabet with a non-empty, finite set of symbols.

  Definition 2 (String). A string s over some alphabet Σ is a, possibly infinite, sequence of symbols s = a₁a₂...aᵢ..., with aᵢ ∈ Σ. We note the special case of a string with no symbols, called the empty string, and denote it by ε.
-/

/-
  This formalization uses the symbol α instead of Σ since Σ is reserved in Lean.
-/


-- Finite strings.
abbrev Str (α : Type) : Type := List α


namespace Strings


/-
Definition 3 (Exponentiation). For an alphabet Σ we define the exponenti-
ation, or powers of Σ by
1. Σ^{0} = {ε}
2. Σ^{n+1} = Σ^{n}Σ = {sa : s ∈ Σ^{n}, a ∈ Σ} n ∈ N
-/

/-
  exp α n is the set of all strings of length n.
-/
inductive exp (α : Type) : ℕ → Set (Str α)
  | zero : exp α 0 []
  | succ
    (n : ℕ)
    (a : α)
    (s : Str α) :
    s ∈ exp α n →
    exp α (n + 1) (s ++ [a])

example : [] ∈ exp Char 0 :=
  by
    exact exp.zero

example : ['a'] ∈ exp Char 1 :=
  by
    apply exp.succ 0 'a' []
    exact exp.zero

example : ['a', 'b'] ∈ exp Char 2 :=
  by
    apply exp.succ 1 'b' ['a']
    apply exp.succ 0 'a' []
    exact exp.zero


lemma rev_str_mem_exp_str_len
  {α : Type}
  (s : Str α) :
  s.reverse ∈ exp α s.length :=
  by
    induction s
    case nil =>
      simp
      exact exp.zero
    case cons hd tl ih =>
      simp
      exact exp.succ tl.length hd tl.reverse ih


theorem str_mem_exp_str_len
  {α : Type}
  (s : Str α) :
  s ∈ exp α s.length :=
  by
    obtain s1 := rev_str_mem_exp_str_len s.reverse
    simp at s1
    exact s1


theorem mem_exp_imp_str_len_eq
  {α : Type}
  (s : Str α)
  (n : ℕ)
  (h1 : s ∈ exp α n) :
  s.length = n :=
  by
    induction h1
    case zero =>
      simp
    case succ m a s ih_1 ih_2 =>
      simp
      exact ih_2


-- The set of all strings of length n.
def exp_set
  (α : Type)
  (n : ℕ) :
  Set (Str α) :=
  {s : Str α | s.length = n}


theorem exp_eq_exp_set
  (α : Type)
  (n : ℕ) :
  exp α n = exp_set α n :=
  by
    simp only [exp_set]
    ext s
    simp
    constructor
    · intro a1
      exact mem_exp_imp_str_len_eq s n a1
    · intro a1
      simp only [← a1]
      exact str_mem_exp_str_len s


/-
Definition 5 (Kleene closure). Let Σ be an alphabet, then we denote the set of all finite strings over Σ by Σ∗.
-/

def kleene_closure
  (α : Type) :
  Set (Str α) :=
  ⋃ (n : ℕ), exp α n


theorem all_str_mem_kleene_closure
  {α : Type}
  (s : Str α) :
  s ∈ kleene_closure α :=
  by
    simp only [kleene_closure]
    simp
    apply Exists.intro s.length
    exact str_mem_exp_str_len s


theorem kleene_closure_eq_univ
  (α : Type) :
  kleene_closure α = Set.univ :=
  by
    apply Set.eq_of_subset_of_subset
    · simp only [Set.subset_def]
      intro x _
      exact trivial
    · simp only [Set.subset_def]
      intro x _
      exact all_str_mem_kleene_closure x


example
  (α : Type)
  (s t : Str α)
  (m n : ℕ)
  (h1 : s.length = m)
  (h2 : t.length = n) :
  s ++ t ∈ exp α (m + n) :=
  by
    simp only [← h1]
    simp only [← h2]
    simp only [← List.length_append s t]
    exact str_mem_exp_str_len (s ++ t)


example
  (α : Type)
  (s t : Str α) :
  s ++ t ∈ kleene_closure α :=
  by
    exact all_str_mem_kleene_closure (s ++ t)


theorem thm_2
  (α : Type)
  (s t u : Str α) :
  s ++ (t ++ u) = (s ++ t) ++ u :=
  by
    symm
    exact (List.append_assoc s t u)


/-
Definition 7. (Substring) Suppose that s, t, u, v are strings such that s =
tuv, then u is called a substring of s. Further, if at least one of t and v is
not ε then u is called a proper substring of s.
-/
def is_substring_of
  (α : Type)
  (s u : Str α) :
  Prop :=
  ∃ (t v : Str α), s = t ++ u ++ v

def is_proper_substring_of
  (α : Type)
  (s u : Str α) :
  Prop :=
  ∃ (t v : Str α), s = t ++ u ++ v ∧ (¬ t.isEmpty ∨ ¬ v.isEmpty)

/-
Definition 8. (Prefix) Suppose that s, t, u are strings such that s = tu, then
t is called a prefix of s. Further, t is called a proper prefix of s if u ≠ ε,
-/
def is_prefix_of
  (α : Type)
  (s t : Str α) :
  Prop :=
  ∃ (u : Str α), s = t ++ u

def is_proper_prefix_of
  (α : Type)
  (s t : Str α) :
  Prop :=
  ∃ (u : Str α), s = t ++ u ∧ ¬ u.isEmpty

/-
Definition 9. (Suffix) Suppose that s, t, u are strings such that s = tu, then
u is called a suffix of s. Further, u is called a proper suffix of s if t ≠ ε
-/
def is_suffix_of
  (α : Type)
  (s u : Str α) :
  Prop :=
  ∃ (t : Str α), s = t ++ u

def is_proper_suffix_of
  (α : Type)
  (s u : Str α) :
  Prop :=
  ∃ (t : Str α), s = t ++ u ∧ ¬ t.isEmpty


end Strings


-------------------------------------------------------------------------------


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
    intro x _
    exact Strings.all_str_mem_kleene_closure x


/-
Definition 11 (Concatenation). Let L1 and L2 be languages. The concate-
nation of L1 and L2, written L1 · L2, or L1L2 is defined by
L1L2 = {s · t = st : s ∈ L1, t ∈ L2} .
-/
def concat
  {α : Type}
  (L1 L2 : Language α) :
  Language α :=
  { s ++ t | (s ∈ L1) (t ∈ L2) }


example
  {α : Type}
  (L M : Language α)
  (w : Str α)
  (h1 : w ∈ concat L M) :
  ∃ (s : Str α), s ∈ L ∧ ∃ (t : Str α), t ∈ M ∧ s ++ t = w:=
  by
    simp only [concat] at h1
    simp at h1
    exact h1


lemma concat_mem_concat
  {α : Type}
  (L M : Language α)
  (s t : Str α)
  (h1 : s ∈ L)
  (h2 : t ∈ M) :
  s ++ t ∈ concat L M :=
  by
    simp only [concat]
    simp
    apply Exists.intro s
    constructor
    · exact h1
    · apply Exists.intro t
      constructor
      · exact h2
      · rfl


lemma eps_concat_mem_concat
  {α : Type}
  (L M : Language α)
  (x : Str α)
  (h1 : [] ∈ L)
  (h2 : x ∈ M) :
  x ∈ concat L M :=
  by
    obtain s1 := concat_mem_concat L M [] x h1 h2
    simp at s1
    exact s1


theorem thm_3_a
  {α : Type}
  (L : Language α) :
  concat L ∅ = ∅ :=
  by
    simp only [concat]
    simp


theorem thm_3_b
  {α : Type}
  (L : Language α) :
  concat ∅ L = ∅ :=
  by
    simp only [concat]
    simp


theorem thm_3_c
  {α : Type}
  (L1 L2 L3 : Language α) :
  concat L1 (concat L2 L3) =
    concat (concat L1 L2) L3 :=
  by
    simp only [concat]
    simp


theorem thm_3_d
  {α : Type}
  (L1 L2 L3 : Language α) :
  concat L1 (L2 ∪ L3) =
    concat L1 L2 ∪ concat L1 L3 :=
  by
    simp only [concat]
    ext cs
    constructor
    · simp
      intro xs a1 ys a2 a3
      subst a3
      cases a2
      case _ c1 =>
        left
        apply Exists.intro xs
        constructor
        · exact a1
        · apply Exists.intro ys
          tauto
      case _ c1 =>
        right
        apply Exists.intro xs
        constructor
        · exact a1
        · apply Exists.intro ys
          tauto
    · simp
      intro a1
      cases a1
      all_goals
        case _ c1 =>
          apply Exists.elim c1
          intro xs a2
          clear c1
          cases a2
          case _ a2_left a2_right =>
            apply Exists.elim a2_right
            intro ys a3
            apply Exists.intro xs
            constructor
            · exact a2_left
            · apply Exists.intro ys
              tauto


theorem thm_3_d_comm
  {α : Type}
  (L1 L2 L3 : Language α) :
  concat (L1 ∪ L2) L3 =
    concat L1 L3 ∪ concat L2 L3 :=
  by
    simp only [concat]
    ext cs
    constructor
    · simp
      intro s a1 t a2 a3
      cases a1
      case _ a1_left =>
        left
        apply Exists.intro s
        constructor
        · exact a1_left
        · apply Exists.intro t
          tauto
      case _ a1_right =>
        right
        apply Exists.intro s
        constructor
        · exact a1_right
        · apply Exists.intro t
          tauto
    · simp
      intro a1
      cases a1
      case _ a1_left =>
        cases a1_left
        case _ s a2 =>
          cases a2
          case _ a2_left a2_right =>
            cases a2_right
            case _ t a3 =>
              cases a3
              case _ a3_left a3_right =>
                apply Exists.intro s
                constructor
                · left
                  exact a2_left
                · apply Exists.intro t
                  tauto
      case _ a1_right =>
        cases a1_right
        case _ s a2 =>
          cases a2
          case _ a2_left a2_right =>
            cases a2_right
            case _ t a3 =>
            cases a3
            case _ a3_left a3_right =>
              apply Exists.intro s
              constructor
              · right
                exact a2_left
              · apply Exists.intro t
                tauto


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


example
  {α : Type}
  (L M : Language α)
  (h1 : [] ∈ L)
  (h2 : L ⊆ M) :
  L ⊆ concat L M :=
  by
    simp only [Set.subset_def]
    intro x a1
    apply concat_mem_concat L M [] x h1
    exact Set.mem_of_subset_of_mem h2 a1


lemma concat_subset_left
  {α : Type}
  (L1 L2 L3 : Language α)
  (h1 : L2 ⊆ L3) :
  concat L2 L1 ⊆ concat L3 L1 :=
  by
    simp only [Set.subset_def]
    intro x a1
    simp only [concat] at a1
    simp at a1
    cases a1
    case _ s a2 =>
      cases a2
      case _ a2_left a2_right =>
        cases a2_right
        case _ t a3 =>
          cases a3
          case _ a3_left a3_right =>
            simp only [concat]
            simp
            apply Exists.intro s
            constructor
            · exact Set.mem_of_subset_of_mem h1 a2_left
            · apply Exists.intro t
              tauto


lemma concat_subset_right
  {α : Type}
  (L1 L2 L3 : Language α)
  (h1 : L2 ⊆ L3) :
  concat L1 L2 ⊆ concat L1 L3 :=
  by
    simp only [Set.subset_def]
    intro x a1
    simp only [concat] at a1
    simp at a1
    cases a1
    case _ s a2 =>
      cases a2
      case _ a2_left a2_right =>
        cases a2_right
        case _ t a3 =>
          cases a3
          case _ a3_left a3_right =>
            simp only [concat]
            simp
            apply Exists.intro s
            constructor
            · exact a2_left
            · apply Exists.intro t
              constructor
              · exact Set.mem_of_subset_of_mem h1 a3_left
              · exact a3_right

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


example
  {α : Type}
  (L : Language α) :
  exp L 1 = L :=
  by
    simp only [exp]
    simp only [concat]
    simp


theorem exp_union_sub_exp_succ_union
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  ⋃ (k ≤ n), exp L k ⊆ ⋃ (k ≤ n + 1), exp L k :=
  by
    simp
    intro k a1
    simp only [Set.subset_def]
    intro x a2
    simp
    apply Exists.intro k
    constructor
    · exact Nat.le_succ_of_le a1
    · exact a2


example
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  exp L (n + 1) = concat (exp L n) L :=
  by
    rfl


lemma exp_succ_union
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  ⋃ (k ≤ n), exp L (k + 1) =
    concat (⋃ (k ≤ n), exp L k) L :=
  by
    apply Set.eq_of_subset_of_subset
    · simp only [Set.subset_def]
      intro x a1
      simp at a1
      cases a1
      case _ i a2 =>
        cases a2
        case _ a2_left a2_right =>
          simp only [exp] at a2_right
          have s1 : concat (exp L i) L ⊆ concat (⋃ k, ⋃ (_ : k ≤ n), exp L k) L :=
          by
            apply concat_subset_left
            exact Set.subset_biUnion_of_mem a2_left
          apply Set.mem_of_subset_of_mem s1 a2_right
    · simp only [Set.subset_def]
      intro x a1
      simp only [concat] at a1
      simp at a1
      cases a1
      case _ s a2 =>
        cases a2
        case _ a2_left a2_right =>
          cases a2_left
          case _ i a3 =>
            cases a3
            case _ a3_left a3_right =>
              cases a2_right
              case _ t a4 =>
                cases a4
                case _ a4_left a4_right =>
                  simp
                  simp only [exp]
                  apply Exists.intro i
                  constructor
                  · exact a3_left
                  · simp only [concat]
                    simp
                    apply Exists.intro s
                    constructor
                    · exact a3_right
                    · apply Exists.intro t
                      tauto


lemma concat_mem_exp
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (n : ℕ)
  (h1 : s ∈ exp L n)
  (h2 : t ∈ L) :
  s ++ t ∈ exp L (n + 1) :=
  by
    simp only [exp]
    exact concat_mem_concat (exp L n) L s t h1 h2


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
    cases h1
    case _ i a1 =>
      cases a1
      case _ a1_left a1_right =>
        simp
        apply Exists.intro i
        constructor
        · exact a1_left
        · apply concat_mem_exp L s t i a1_right h2


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
      simp only [thm_3_c]


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
      simp only [thm_3_d_comm]
      simp only [thm_3_d]
      simp only [ih]
      simp only [concat_exp_comm]


lemma exp_succ_concat_left
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  exp L (n + 1) = concat L (exp L n) :=
  by
    simp only [← concat_exp_comm]
    rfl


lemma exp_succ_concat_left_union
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  (⋃ (k ≤ n), exp L (k + 1)) = concat L (⋃ (k ≤ n), exp L k) :=
  by
    simp only [← concat_exp_comm_union]
    exact exp_succ_union L n


lemma concat_mem_exp_comm
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (n : ℕ)
  (h1 : s ∈ L)
  (h2 : t ∈ exp L n) :
  s ++ t ∈ exp L (n + 1) :=
  by
    simp only [exp]
    simp only [concat_exp_comm]
    exact concat_mem_concat L (exp L n) s t h1 h2


lemma concat_mem_exp_comm_union
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (n : ℕ)
  (h1 : s ∈ L)
  (h2 : t ∈ (⋃ (k ≤ n), exp L k)) :
  s ++ t ∈ (⋃ (k ≤ n), exp L (k + 1)) :=
  by
    simp only [exp_succ_union]
    simp only [concat_exp_comm_union]
    exact concat_mem_concat L (⋃ k, ⋃ (_ : k ≤ n), exp L k) s t h1 h2


example
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
      simp only [concat]
      simp
      constructor
      · exact ih
      · exact h1


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
      cases ih
      case _ i a1 =>
        simp
        cases a1
        case _ a1_left a1_right =>
          apply Exists.intro i
          constructor
          · exact Nat.le_succ_of_le a1_left
          · exact a1_right


lemma eps_mem_imp_exp_subset_exp_succ
  {α : Type}
  (L : Language α)
  (n : ℕ)
  (h1 : [] ∈ L) :
  exp L n ⊆ exp L (n + 1) :=
  by
    simp only [Set.subset_def]
    intro x a1
    obtain s1 := concat_mem_exp_comm L [] x n h1 a1
    simp at s1
    exact s1


lemma exp_sum
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (m n : ℕ)
  (h1 : s ∈ exp L m)
  (h2 : t ∈ exp L n) :
  s ++ t ∈ exp L (m + n) :=
  by
    induction n generalizing t
    case zero =>
      simp only [exp] at h2
      simp at h2
      simp only [h2]
      simp
      exact h1
    case succ n ih =>
      simp only [exp] at h2
      simp only [concat] at h2
      simp at h2
      cases h2
      case _ s' a1 =>
        cases a1
        case _ a1_left a1_right =>
          cases a1_right
          case _ t' a2 =>
            cases a2
            case _ a2_left a2_right =>
              simp only [exp]
              simp only [concat]
              simp

              specialize ih s' a1_left
              apply Exists.intro (s ++ s')
              constructor
              · exact ih
              · simp only [← a2_right]
                apply Exists.intro t'
                constructor
                · exact a2_left
                · simp


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
    intro s a1

    induction n generalizing s
    case zero =>
      simp only [exp] at a1
      simp at a1

      simp only [a1]
      exact kleene_closure.eps L
    case succ n ih =>
      simp only [exp] at a1
      simp only [concat] at a1
      simp at a1

      apply Exists.elim a1
      intro xs a2
      clear a1

      cases a2
      case _ a2_left a2_right =>
        apply Exists.elim a2_right
        intro ys a3
        clear a2_right

        cases a3
        case _ a3_left a3_right =>
          simp only [← a3_right]
          apply kleene_closure.succ L
          apply ih xs a2_left
          exact a3_left


lemma lang_sub_kleene_closure
  {α : Type}
  (L : Language α) :
  L ⊆ kleene_closure α L :=
  by
    obtain s2 := thm_4 L 1
    simp only [exp] at s2
    simp only [concat] at s2
    simp at s2
    exact s2


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
    intro s a1
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
    intro s a1
    induction a1
    case eps =>
      simp
      apply Exists.intro 0
      simp only [exp]
      simp
    case succ xs ys _ ih_2 ih_3 =>
      simp at ih_3

      apply Exists.elim ih_3
      intro n a2
      clear ih_3

      simp
      apply Exists.intro (n + 1)
      simp only [exp]
      simp only [concat]
      simp
      apply Exists.intro xs
      constructor
      · exact a2
      · apply Exists.intro ys
        simp
        exact ih_2


theorem thm_5
  {α : Type}
  (L : Language α) :
  kleene_closure α L = ⋃ (n : ℕ), exp L n :=
  by
    apply Set.eq_of_subset_of_subset
    · exact thm_5_right L
    · exact thm_5_left L


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
    cases h1
    case _ m a1 =>
      cases h2
      case _ n a2 =>
        apply Exists.intro (m + n)
        apply exp_sum L s t m n a1 a2


-- Each l is the concatenation of a list of strings, each of which is in L.
def kleene_closure_set
  (α : Type)
  (L : Language α) :=
  { l | ∃ M : List (Str α), (∀ (r : Str α), r ∈ M → r ∈ L) ∧ M.join = l }


lemma kleene_closure_set_eq_kleene_closure_left
  {α : Type}
  (L : Language α) :
  kleene_closure_set α L ⊆ kleene_closure α L :=
  by
    simp only [Set.subset_def]
    intro x a1
    simp only [kleene_closure_set] at a1
    simp at a1
    cases a1
    case _ l a2 =>
      cases a2
      case _ a2_left a2_right =>
        simp only [← a2_right]
        clear a2_right

        simp only [thm_5]
        simp
        induction l
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
            cases ih
            case _ i a3 =>
              apply Exists.intro (i + 1)
              exact concat_mem_exp_comm L hd tl.join i a2_left_left a3


lemma kleene_closure_set_eq_kleene_closure_right
  {α : Type}
  [DecidableEq α]
  (L : Language α) :
  kleene_closure α L ⊆ kleene_closure_set α L :=
  by
    simp only [Set.subset_def]
    intro x a1
    simp only [kleene_closure_set]
    simp

    induction a1
    case eps =>
      simp
      apply Exists.intro []
      simp
    case succ s t ih_1 ih_2 ih_3 =>
      simp only [thm_5] at ih_1
      simp at ih_1
      cases ih_1
      case _ i a2 =>
        cases ih_3
        case _ M a3 =>
          cases a3
          case _ a3_left a3_right =>
            apply Exists.intro (M ++ [t])
            constructor
            · intro r a4
              simp at a4
              cases a4
              case _ a4_right =>
                exact a3_left r a4_right
              case _ a4_left =>
                simp only [a4_left]
                exact ih_2
            · simp
              exact a3_right


theorem kleene_closure_set_eq_kleene_closure
  (α : Type)
  [DecidableEq α]
  (L : Language α) :
  kleene_closure_set α L = kleene_closure α L :=
  by
    apply Set.eq_of_subset_of_subset
    · exact kleene_closure_set_eq_kleene_closure_left L
    · exact kleene_closure_set_eq_kleene_closure_right L


theorem thm_6
  {α : Type}
  (L : Language α) :
  (kleene_closure α L) = {[]} ∪ (concat L (kleene_closure α L)) :=
  by
    apply Set.eq_of_subset_of_subset
    · simp only [Set.subset_def]
      intro s a1
      simp only [thm_5] at a1
      simp at a1
      cases a1
      case _ i a2 =>
        simp
        cases i
        case zero =>
          simp only [exp] at a2
          simp at a2
          left
          exact a2
        case succ k =>
          simp only [exp_succ_concat_left] at a2
          simp only [concat] at a2
          simp at a2
          cases a2
          case _ s_1 a3 =>
            cases a3
            case _ a3_left a3_right =>
              cases a3_right
              case _ t a4 =>
                cases a4
                case _ a4_left a4_right =>
                  right
                  simp only [← a4_right]
                  apply concat_mem_concat
                  · exact a3_left
                  · exact Set.mem_of_mem_of_subset a4_left (thm_4 L k)
    · simp only [Set.subset_def]
      intro x a1
      simp at a1
      cases a1
      case _ a1_left =>
        simp only [a1_left]
        exact kleene_closure.eps L
      case _ a1_right =>
        simp only [thm_5 L] at a1_right
        simp only [concat] at a1_right
        simp at a1_right
        cases a1_right
        case _ s a2 =>
          cases a2
          case _ a2_left a2_right =>
            cases a2_right
            case _ t a3 =>
              cases a3
              case _ a3_left a3_right =>
                cases a3_left
                case _ i a4 =>
                  simp only [← a3_right]
                  obtain s1 := concat_mem_exp_comm L s t i a2_left a4
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
    apply Set.eq_of_subset_of_subset
    · simp only [Set.subset_def]
      intro x a1
      simp only [concat] at a1
      simp at a1
      cases a1
      case _ s a2 =>
        cases a2
        case _ a2_left a2_right =>
          cases a2_right
          case _ t a3 =>
            cases a3
            case _ a3_left a3_right =>
              cases a3_left
              case _ i a4 =>
                simp
                apply Exists.intro i
                simp only [← a3_right]
                simp only [exp]
                exact concat_mem_exp_comm L s t i a2_left a4
    · simp only [Set.subset_def]
      intro x a1
      simp at a1
      cases a1
      case _ i a2 =>
        simp only [exp] at a2
        simp only [concat_exp_comm] at a2
        simp only [concat] at a2
        simp at a2
        cases a2
        case _ s a3 =>
          cases a3
          case _ a3_left a3_right =>
            cases a3_right
            case _ t a4 =>
              cases a4
              case _ a4_left a4_right =>
                simp only [concat]
                simp
                apply Exists.intro s
                constructor
                · exact a3_left
                · apply Exists.intro t
                  constructor
                  · apply Exists.intro i
                    exact a4_left
                  · exact a4_right


lemma concat_kleene_closure_succ_right
  {α : Type}
  (L : Language α) :
  concat (⋃ (n : ℕ), exp L n) L = ⋃ (n : ℕ), exp L (n + 1) :=
  by
    apply Set.eq_of_subset_of_subset
    · simp only [Set.subset_def]
      intro x a1
      simp only [concat] at a1
      simp at a1
      cases a1
      case _ s a2 =>
        cases a2
        case _ a2_left a2_right =>
          cases a2_left
          case _ i a3 =>
            cases a2_right
            case _ t a4 =>
              cases a4
              case _ a4_left a4_right =>
                simp
                apply Exists.intro i
                simp only [← a4_right]
                simp only [exp]
                exact concat_mem_exp L s t i a3 a4_left
    · simp only [Set.subset_def]
      intro x a1
      simp at a1
      cases a1
      case _ i a2 =>
        simp only [exp] at a2
        simp only [concat] at a2
        simp at a2
        cases a2
        case _ s a3 =>
          cases a3
          case _ a3_left a3_right =>
            cases a3_right
            case _ t a4 =>
              cases a4
              case _ a4_left a4_right =>
                simp only [concat]
                simp
                apply Exists.intro s
                constructor
                · apply Exists.intro i
                  exact a3_left
                · apply Exists.intro t
                  constructor
                  · exact a4_left
                  · exact a4_right


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
      intro x a1
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
          simp only [thm_3_d_comm]
          simp only [concat_eps_left]
          simp only [thm_3_c]

      _ = (concat L1 X) ∪ L2 :=
        by simp only [h1]


lemma thm_9_unique_left_aux_1
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
        apply concat_subset_right
        exact ih

      simp only [thm_3_c] at s1
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
    intro x a1

    have s1 : ∃ (n : ℕ), x ∈ concat (exp L1 n) L2 :=
    by
      simp only [concat] at a1
      simp at a1
      cases a1
      case _ s a2 =>
        cases a2
        case _ a2_left a2_right =>
          cases a2_left
          case _ i a3 =>
            cases a2_right
            case _ t a4 =>
              cases a4
              case _ a4_left a4_right =>
                simp only [concat]
                simp
                apply Exists.intro i
                apply Exists.intro s
                constructor
                · exact a3
                · apply Exists.intro t
                  constructor
                  · exact a4_left
                  · exact a4_right

    cases s1
    case _ n a2 =>
      obtain s2 := thm_9_unique_left_aux_1 L1 L2 X h1 n
      apply Set.mem_of_subset_of_mem s2 a2


lemma eps_not_mem_imp_mem_len_gt_zero
  {α : Type}
  (L : Language α)
  (x : Str α)
  (h1 : [] ∉ L)
  (h2 : x ∈ L) :
  x.length > 0 :=
  by
    cases x
    case nil =>
      contradiction
    case cons hd tl =>
      simp


example
  {α : Type}
  (L M : Language α)
  (x : Str α)
  (h1 : [] ∉ L)
  (h2 : x ∈ concat L M) :
  x.length > 0 :=
  by
    cases x
    case nil =>
      simp only [concat] at h2
      simp at h2
      cases h2
      case _ h2_left h2_right =>
        contradiction
    case cons hd tl =>
      simp


example
  {α : Type}
  (L M : Language α)
  (h1 : [] ∉ L) :
  [] ∉ concat L M :=
  by
    simp only [concat]
    simp
    intro a1
    contradiction


example
  {α : Type}
  (L : Language α)
  (n : ℕ)
  (h1 : [] ∉ L) :
  [] ∉ exp L (n + 1) :=
  by
    simp only [exp]
    simp only [concat]
    simp
    intro _
    exact h1


lemma eps_not_mem_imp_mem_len_ge_exp
  {α : Type}
  (L : Language α)
  (x : Str α)
  (n : ℕ)
  (h1 : [] ∉ L)
  (h2 : x ∈ exp L (n + 1)) :
  x.length > n :=
  by
    induction n generalizing x
    case zero =>
      simp only [exp] at h2
      simp only [concat] at h2
      simp at h2
      apply eps_not_mem_imp_mem_len_gt_zero L x h1 h2
    case succ k ih =>
      rw [exp] at h2
      simp only [concat] at h2
      simp at h2
      cases h2
      case _ s a1 =>
        cases a1
        case _ a1_left a1_right =>
          cases a1_right
          case _ t a2 =>
            cases a2
            case _ a2_left a2_right =>
              simp only [← a2_right]
              simp
              specialize ih s a1_left
              have s1 : t.length > 0 := eps_not_mem_imp_mem_len_gt_zero L t h1 a2_left
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
    cases h2
    case _ s a1 =>
      cases a1
      case _ a1_left a1_right =>
        cases a1_right
        case _ t a2 =>
          cases a2
          case _ a2_left a2_right =>
            simp only [← a2_right]
            simp
            obtain s1 := eps_not_mem_imp_mem_len_ge_exp L s n h1 a1_left
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


theorem left_append_not_eps
  {α : Type}
  (s t : Str α)
  (h1 : ¬ s = []) :
  List.length t < List.length (s ++ t) :=
  by
    simp
    exact h1


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
          apply left_append_not_eps
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

    · apply eps_concat_mem_concat
      · apply eps_mem_kleene_closure
      · exact hx
termination_by x => x.length


theorem thm_9_unique
  {α : Type}
  (L1 L2 X : Language α)
  (h1 : X = (concat L1 X) ∪ L2)
  (h2 : [] ∉ L1) :
  concat (kleene_closure α L1) L2 = X :=
  by
    apply Set.eq_of_subset_of_subset
    · exact thm_9_unique_left L1 L2 X h1
    · exact thm_9_unique_right L1 L2 X h1 h2


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


example
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
    apply Set.eq_of_subset_of_subset
    · simp only [Set.subset_def]
      intro x a1
      simp at a1
      simp
      tauto
    · simp only [Set.subset_def]
      intro x a1
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
    apply Set.eq_of_subset_of_subset
    · simp only [Set.subset_def]
      intro x a1
      simp at a1
      simp
      tauto
    · simp only [Set.subset_def]
      intro x a1
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
    apply Set.eq_of_subset_of_subset
    · simp only [Set.subset_def]
      intro x a1
      simp at a1
      cases a1
      case _ a1_left a2_right =>
        simp only [concat] at a1_left
        simp at a1_left

        simp only [a2_right]
        simp only [concat]
        simp
        exact a1_left
    · simp only [Set.subset_def]
      intro x a1
      simp only [concat] at a1
      simp at a1
      cases a1
      case _ s a2 =>
        cases a2
        case _ a2_left a2_right =>
          cases a2_left
          case _ a2_left_left a2_left_right =>
            cases a2_right
            case _ t a3 =>
              cases a3
              case _ a3_left a3_right =>
                cases a3_left
                case _ a3_left_left a3_left_right =>
                  simp only [← a3_right]
                  simp only [a2_left_right]
                  simp only [a3_left_right]
                  simp
                  simp only [concat]
                  simp
                  tauto


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
  (s a : Str α) :
  derivative L (s ++ a) = derivative (derivative L s) a :=
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
  (a : Str α) :
  derivative (L1 ∪ L2) a =
    (derivative L1 a) ∪ (derivative L2 a) :=
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
      exact (Set.insert_eq_of_mem c1).symm
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
    ext xs
    simp
    constructor
    · intro a1
      cases a1
      case _ s a2 =>
        cases a2
        case _ a2_left a2_right =>
          cases a2_right
          case _ t a3 =>
            cases a3
            case _ a3_left a3_right =>
              cases s
              case nil =>
                simp at a3_right
                apply Exists.intro []
                constructor
                · exact a2_left
                · apply Exists.intro xs
                  simp
                  simp only [← a3_right]
                  exact a3_left
              case cons s_hd s_tl =>
                simp only [Language.nullify] at a2_left
                split_ifs at a2_left
                case pos c1 =>
                  simp at a2_left
                case neg c1 =>
                  simp at a2_left
    · intro a1
      cases a1
      case _ s a2 =>
        cases a2
        case _ a2_left a2_right =>
          cases a2_right
          case _ t a3 =>
            cases a3
            case _ a3_left a3_right =>
              cases s
              case nil =>
                simp at a3_right
                apply Exists.intro []
                constructor
                · exact a2_left
                · simp only [← a3_right]
                  simp
                  exact a3_left
              case cons s_hd s_tl s_ih =>
                simp only [Language.nullify] at a2_left
                split_ifs at a2_left
                case pos c1 =>
                  simp at a2_left
                case neg c1 =>
                  simp at a2_left


lemma thm_12_7_3
  {α : Type}
  [DecidableEq α]
  (L0 L2 : Language α)
  (a : α)
  (h1 : L0.nullify = ∅) :
  {t | a :: t ∈ concat L0 L2} = {t | ∃ t0 t2, a :: t0 ∈ L0 ∧ t2 ∈ L2 ∧ t0 ++ t2 = t} :=
  by
    have s1 : [] ∉ L0 :=
    by
      simp only [Language.nullify] at h1
      simp at h1
      exact h1

    simp only [concat]
    simp
    ext xs
    constructor
    · simp
      intro s a1 t a3 a4
      cases s
      case nil =>
        contradiction
      case cons s_hd s_tl =>
        simp at a4
        cases a4
        case _ a4_left a4_right =>
          simp only [a4_left] at a1
          apply Exists.intro s_tl
          constructor
          · exact a1
          · apply Exists.intro t
            constructor
            · exact a3
            · exact a4_right
    · simp
      intro s a1 t a2 a3
      apply Exists.intro (a :: s)
      constructor
      · exact a1
      · apply Exists.intro t
        constructor
        · exact a2
        · simp only [← a3]
          simp


-- 1.56
theorem thm_12_7
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (a : α) :
  derivative (concat L1 L2) [a] =
    (concat (derivative L1 [a]) L2) ∪ (concat L1.nullify ((derivative L2 [a]))) :=
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
        obtain s3 := thm_3_d_comm L1.nullify L0 L2
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

-------------------------------------------------------------------------------

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

        obtain s1 := eps_mem_imp_exp_subset_exp_succ L k c1

        exact concat_subset_right (derivative L [a]) (exp L k) (exp L (k + 1)) s1
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
      cases a1
      case _ i a2 =>
        cases a2
        case _ s a3 =>
          cases a3
          case _ a3_left a3_right =>
            cases a3_right
            case _ t a4 =>
              cases a4
              case _ a4_left a4_right =>
                apply Exists.intro s
                constructor
                · exact a3_left
                · apply Exists.intro t
                  constructor
                  · apply Exists.intro i
                    exact a4_left
                  · exact a4_right
    · intro a1
      cases a1
      case _ s a2 =>
        cases a2
        case _ a2_left a2_right =>
          cases a2_right
          case _ t a3 =>
            cases a3
            case _ a3_left a3_right =>
              cases a3_left
              case _ i a4 =>
                apply Exists.intro i
                apply Exists.intro s
                constructor
                · exact a2_left
                · apply Exists.intro t
                  tauto


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

/-
    have s1 : derivative L [a] ∪ derivative Lᶜ [a] = derivative (L ∪ Lᶜ) [a] :=
    by
      simp only [thm_12_5]

    have s2 : derivative (L ∪ Lᶜ) [a] = derivative Set.univ [a] :=
      by
        simp

    have s3 : derivative Set.univ [a] = derivative (concat (Strings.exp α 1) Set.univ) [a] :=
    by
      simp only [thm_12_7]
      simp only [Strings.exp_eq_exp_set]
      simp only [Strings.exp_set]
      simp only [Language.nullify]
      simp
      simp only [thm_3_b]
      simp

      simp only [derivative]
      simp
      simp only [concat]
      simp

    have s4 : derivative (concat (Strings.exp α 1) Set.univ) [a] = Strings.kleene_closure α :=
    by
      simp only [Strings.kleene_closure_eq_univ]
      apply Set.eq_of_subset_of_subset
      · simp only [Set.subset_univ]
      · simp only [Set.subset_def]
        intro x a1
        simp only [concat]
        simp
        simp only [derivative]
        simp
        apply Exists.intro [a]
        constructor
        · simp only [Strings.exp_eq_exp_set]
          simp only [Strings.exp_set]
          simp
        · apply Exists.intro x
          simp

    have s5 : derivative L [a] ∪ derivative Lᶜ [a] = Set.univ :=
      by
        simp only [s1]
        simp only [s2]
        simp only [s3]
        simp only [s4]
        simp only [Strings.kleene_closure_eq_univ]

    have s6 : derivative L [a] ∩ derivative Lᶜ [a] = ∅ :=
    by
      simp only [← thm_12_6 L Lᶜ a]
      simp
      simp only [thm_12_1]

    exact rfl
-/


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
    apply Set.eq_of_subset_of_subset
    · simp only [Set.subset_def]
      intro x a1
      cases x
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
    · simp only [Set.subset_def]
      intro x a1
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
        cases a1_right
        case _ i a2 =>
          simp only [concat] at a2
          simp only [derivative] at a2
          simp at a2
          cases a2
          case _ t a3 =>
            cases a3
            case _ a3_left a3_right =>
              simp only [← a3_right]
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
    exact fun a => id a.symm


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
  Str.equiv_class L [a] ∩ Strings.exp_set α 1 =
    { b | derivative L [a] = derivative L b ∧ b.length = 1 } :=
  by
    rfl


example
  {α : Type}
  [DecidableEq α]
  (L : Language α) :
  L.nullify ∪ ⋃ (a : α), concat {[a]} (derivative L [a]) =
    L.nullify ∪ ⋃ (a : α), concat (Str.equiv_class L [a] ∩ Strings.exp_set α 1) (derivative L [a]) :=
  by
    sorry


theorem Languages.extracted_1
  {α : Type}
  [inst : DecidableEq α]
  (L1 L2 : Language α)
  (s : Str α) :
  derivative (concat L1 L2) s = concat (derivative L1 s) L2 ∪ concat L1.nullify (derivative L2 s) :=
  by
    induction s generalizing L1 L2
    case nil =>
      simp only [derivative]
      simp only [concat]
      simp only [Language.nullify]
      ext cs
      simp
      intro a1 s a2 a3
      apply Exists.intro []
      constructor
      · exact a1
      · apply Exists.intro s
        constructor
        · exact a2
        · simp
          exact a3
    case cons hd tl ih =>
      have s1 : hd :: tl = [hd] ++ tl := by simp
      simp only [s1]
      clear s1

      simp only [thm_11_b]

      rw [thm_12_7]
      simp only [thm_12_5_str]

      rw [ih]

      simp only [Set.union_assoc]

      rw [← thm_11_b]

      sorry


theorem thm_16_1
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (s t : Str α)
  (h1 : L_equiv L1 s t)
  (h2 : L_equiv L2 s t) :
  L_equiv (concat L1 L2) s t :=
  by
    have s1 : derivative (concat L1 L2) s =
      concat (derivative L1 s) L2 ∪ concat L1.nullify (derivative L2 s) :=
    by
      sorry
    sorry
