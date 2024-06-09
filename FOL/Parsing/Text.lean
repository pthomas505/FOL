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


/-
Definition 10 (Language). A language L over some alphabet Σ is a subset of Σ∗, i.e. L ⊆ Σ∗.
-/

abbrev Language (α : Type) : Type := Set (Str α)


example
  (α : Type)
  (L : Language α) :
  L ⊆ kleene_closure α :=
  by
    simp only [Set.subset_def]
    intro x _
    exact all_str_mem_kleene_closure x


/-
Definition 11 (Concatenation)
-/
def lang_concat
  {α : Type}
  (L1 L2 : Language α) :
  Language α :=
  { r ++ s | (r ∈ L1) (s ∈ L2) }


theorem thm_3_a
  {α : Type}
  (L : Language α) :
  lang_concat L ∅ = ∅ :=
  by
    simp only [lang_concat]
    simp


theorem thm_3_b
  {α : Type}
  (L : Language α) :
  lang_concat ∅ L = ∅ :=
  by
    simp only [lang_concat]
    simp


theorem thm_3_c
  {α : Type}
  (L1 L2 L3 : Language α) :
  lang_concat L1 (lang_concat L2 L3) =
    lang_concat (lang_concat L1 L2) L3 :=
  by
    simp only [lang_concat]
    simp


theorem thm_3_d
  {α : Type}
  (L1 L2 L3 : Language α) :
  lang_concat L1 (L2 ∪ L3) =
    lang_concat L1 L2 ∪ lang_concat L1 L3 :=
  by
    simp only [lang_concat]
    aesop


def lang_exp
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  Language α :=
  match n with
  | 0 => {[]}
  | n + 1 => lang_concat (lang_exp L n) L


inductive lang_kleene_closure
  (α : Type) :
  Language α → Language α
  | eps
    (L : Language α) :
    lang_kleene_closure α L []
  | succ
    (L : Language α)
    (s t : Str α) :
    s ∈ lang_kleene_closure α L →
    t ∈ L →
    lang_kleene_closure α L (s ++ t)
