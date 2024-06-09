import Mathlib.Data.Set.Lattice


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577

/-
Definition 1 (Alphabet). An alphabet is any, possibly infinite, set of symbols. We will use Σ to denote an alphabet with a non-empty, finite set of symbols.
-/

/-
  This formalization uses the symbol α instead of Σ since Σ is reserved in Lean.
-/

/-
Definition 2 (String). A string s over some alphabet Σ is a, possibly infinite,
sequence of symbols s = a₁a₂...aᵢ..., with aᵢ ∈ Σ. We note the special case
of a string with no symbols, called the empty string, and denote it by ε.
-/

abbrev Str (α : Type) : Type := List α


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
    exp α n s →
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
  (α : Type)
  (s : Str α) :
  ∃ (n : ℕ), s.reverse ∈ exp α n :=
  by
    induction s
    case nil =>
      apply Exists.intro 0
      apply exp.zero
    case cons hd tl ih =>
      apply Exists.elim ih
      intro n a1
      apply Exists.intro (n + 1)
      simp
      exact exp.succ n hd tl.reverse a1


lemma str_mem_exp
  (α : Type)
  (s : Str α) :
  ∃ (n : ℕ), s ∈ exp α n :=
  by
    obtain s1 := rev_str_mem_exp α s.reverse
    simp only [List.reverse_reverse] at s1
    exact s1
