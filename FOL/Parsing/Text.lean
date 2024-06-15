import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577

/-
Definition 1 (Alphabet). An alphabet is any, possibly infinite, set of symbols. We will use Σ to denote an alphabet with a non-empty, finite set of symbols.
-/

/-
  This formalization uses the symbol α instead of Σ since Σ is reserved in Lean.
-/

/-
Definition 2 (String). A string s over some alphabet Σ is a, possibly infinite, sequence of symbols s = a₁a₂...aᵢ..., with aᵢ ∈ Σ. We note the special case of a string with no symbols, called the empty string, and denote it by ε.
-/

abbrev Str (α : Type) : Type := List α


namespace Strings


/-
  Exponentiation
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

example : ['a'] ∈ exp Char 1 :=
  by
    apply exp.succ 0 'a' []
    exact exp.zero

example : ['a', 'b'] ∈ exp Char 2 :=
  by
    apply exp.succ 1 'b' ['a']
    apply exp.succ 0 'a' []
    exact exp.zero


lemma rev_str_mem_exp
  {α : Type}
  (s : Str α) :
  ∃ (n : ℕ), s.reverse ∈ exp α n :=
  by
    induction s
    case nil =>
      apply Exists.intro 0
      exact exp.zero
    case cons hd tl ih =>
      apply Exists.elim ih
      intro n a1
      apply Exists.intro (n + 1)
      simp
      exact exp.succ n hd tl.reverse a1


lemma str_mem_exp
  {α : Type}
  (s : Str α) :
  ∃ (n : ℕ), s ∈ exp α n :=
  by
    obtain s1 := rev_str_mem_exp s.reverse
    simp only [List.reverse_reverse] at s1
    exact s1


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


lemma str_mem_exp_str_len
  {α : Type}
  (s : Str α) :
  s ∈ exp α s.length :=
  by
    obtain s1 := rev_str_mem_exp_str_len s.reverse
    simp at s1
    exact s1


lemma mem_exp_imp_str_len_eq
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


example
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


lemma all_str_mem_kleene_closure
  {α : Type}
  (s : Str α) :
  s ∈ kleene_closure α :=
  by
    simp only [kleene_closure]
    simp
    exact str_mem_exp s


example
  (α : Type)
  (s t : Str α)
  (h1 : s ∈ kleene_closure α)
  (h2 : t ∈ kleene_closure α) :
  s ++ t ∈ kleene_closure α :=
  by
    simp only [kleene_closure] at *
    simp at *

    apply Exists.elim h1
    intro m a1
    clear h1

    apply Exists.elim h2
    intro n a2
    clear h2

    apply Exists.intro (m + n)

    obtain s1 := mem_exp_imp_str_len_eq s m a1
    obtain s2 := mem_exp_imp_str_len_eq t n a2

    obtain s3 := str_mem_exp_str_len (s ++ t)
    simp at s3
    simp only [s1, s2] at s3
    exact s3


theorem thm_2
  (α : Type)
  (s t u : Str α) :
  s ++ (t ++ u) = (s ++ t) ++ u :=
  by
    symm
    exact (List.append_assoc s t u)


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
Definition 11 (Concatenation)
-/
def concat
  {α : Type}
  (L1 L2 : Language α) :
  Language α :=
  { s ++ t | (s ∈ L1) (t ∈ L2) }


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
    aesop


def exp
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  Language α :=
  match n with
  | 0 => {[]}
  | n + 1 => concat (exp L n) L


example
  {α : Type}
  (L : Language α) :
  exp L 1 = L :=
  by
    simp only [exp]
    simp only [concat]
    simp


example
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  exp L (n + 1) = concat (exp L n) L :=
  by
    rfl


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


lemma exp_succ_concat_left
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  exp L (n + 1) = concat L (exp L n) :=
  by
    simp only [← concat_exp_comm]
    rfl


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
