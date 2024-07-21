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


example
  (α : Type)
  (n : ℕ)
  (a : α)
  (s : Str α)
  (h1 : s ∈ exp α n) :
  a :: s ∈ exp α (n + 1) :=
  by
    induction h1
    case zero =>
      have s1 : [a] = [] ++ [a] := by rfl
      rw [s1]
      apply exp.succ
      exact exp.zero
    case succ n' a' s' _ ih_2 =>
      have s1 : a :: (s' ++ [a']) = (a :: s') ++ [a'] := rfl
      rw [s1]
      apply exp.succ
      exact ih_2


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


/-
Definition 4 (String length). Let s ∈ Σ^n be a string. We say that the length of s is n, written |s| = n, and hence the length is the number of consecutive symbols. As a special case we have |ε| = 0.
-/


theorem str_append_length_left
  {α : Type}
  (s t : Str α)
  (h1 : ¬ s = []) :
  t.length < (s ++ t).length :=
  by
    simp
    exact h1


theorem str_append_length_right
  {α : Type}
  (s t : Str α)
  (h1 : ¬ t = []) :
  s.length < (s ++ t).length :=
  by
    simp
    exact h1


lemma str_reverse_mem_exp_length
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


theorem str_mem_exp_length
  {α : Type}
  (s : Str α) :
  s ∈ exp α s.length :=
  by
    obtain s1 := str_reverse_mem_exp_length s.reverse
    simp at s1
    exact s1


theorem str_mem_exp_length_eq
  {α : Type}
  (s : Str α)
  (n : ℕ)
  (h1 : s ∈ exp α n) :
  s.length = n :=
  by
    induction h1
    case zero =>
      simp
    case succ k c t ih_1 ih_2 =>
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
    ext cs
    simp
    constructor
    · intro a1
      exact str_mem_exp_length_eq cs n a1
    · intro a1
      simp only [← a1]
      exact str_mem_exp_length cs


/-
Definition 5 (Kleene closure). Let Σ be an alphabet, then we denote the set of all finite strings over Σ by Σ∗.
-/

def kleene_closure
  (α : Type) :
  Set (Str α) :=
  ⋃ (n : ℕ), exp α n


theorem str_mem_kleene_closure
  {α : Type}
  (s : Str α) :
  s ∈ kleene_closure α :=
  by
    simp only [kleene_closure]
    simp
    apply Exists.intro s.length
    exact str_mem_exp_length s


theorem kleene_closure_eq_univ
  (α : Type) :
  kleene_closure α = Set.univ :=
  by
    ext cs
    constructor
    · simp
    · simp
      exact str_mem_kleene_closure cs


/-
Definition 6 (Concatenation). Suppose that s ∈ Σ^m and t ∈ Σ^n are strings over some alphabet. The concatenation of s and t written s · t or st, is the string formed by letting the sequence of symbols in s be followed by the sequence of symbols in t, i.e. s · t = a1a2...am · b1b2...bn = a1a2...amb1b2...bn = st ∈ Σ^(m+n)
-/

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
    exact str_mem_exp_length (s ++ t)


example
  (α : Type)
  (s t : Str α) :
  s ++ t ∈ kleene_closure α :=
  by
    exact str_mem_kleene_closure (s ++ t)


theorem str_append_assoc
  (α : Type)
  (s t u : Str α) :
  s ++ (t ++ u) = (s ++ t) ++ u :=
  by
    symm
    exact List.append_assoc s t u


/-
Definition 7. (Substring) Suppose that s, t, u, v are strings such that s = tuv, then u is called a substring of s. Further, if at least one of t and v is not ε then u is called a proper substring of s.
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
Definition 8. (Prefix) Suppose that s, t, u are strings such that s = tu, then t is called a prefix of s. Further, t is called a proper prefix of s if u ≠ ε.
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
Definition 9. (Suffix) Suppose that s, t, u are strings such that s = tu, then u is called a suffix of s. Further, u is called a proper suffix of s if t ≠ ε.
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
