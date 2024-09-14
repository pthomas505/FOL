import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic

import FOL.Parsing.Language.Kleene


set_option autoImplicit false


-- https://arxiv.org/pdf/1509.02032.pdf
-- https://core.ac.uk/download/pdf/156629067.pdf


/-
  The definition of a context free grammar.

  An alphabet Σ is a finite, non-empty set of indivisible symbols.
  A string over an alphabet Σ is a finite sequence of members of Σ.

  N is a non-terminal alphabet.
  T is a terminal alphabet such that N ∩ T = ∅.
  P ⊆ N × (N ∪ T)* is a set of productions.
  S ∈ N is the start symbol.
-/


inductive Symbol (NTS : Type) (TS : Type)
| nts : NTS → Symbol NTS TS
| ts : TS → Symbol NTS TS


def Symbol.isNTS
  {NTS : Type}
  {TS : Type} :
  Symbol NTS TS → Prop
  | nts _ => True
  | ts _ => False

instance
  (NTS : Type)
  (TS : Type)
  (c : Symbol NTS TS) :
  Decidable c.isNTS :=
  by
    simp only [Symbol.isNTS]
    cases c
    all_goals
      infer_instance


def Symbol.isTS
  {NTS : Type}
  {TS : Type} :
  Symbol NTS TS → Prop
  | nts _ => False
  | ts _ => True

instance
  (NTS : Type)
  (TS : Type)
  (c : Symbol NTS TS) :
  Decidable c.isTS :=
  by
    simp only [Symbol.isTS]
    cases c
    all_goals
      infer_instance


def Symbol.getNTS
  (NTS : Type)
  (TS : Type) :
  (c : Symbol NTS TS) → (h1 : c.isNTS) → NTS
  | nts a, _ => a


def Symbol.getTS
  (NTS : Type)
  (TS : Type) :
  (c : Symbol NTS TS) → (h1 : c.isTS) → TS
  | ts a, _ => a


structure Rule (NTS : Type) (TS : Type) :=
  (lhs : NTS)
  (rhs : Str (Symbol NTS TS))


def Rule.isEpsilonRule
  {NTS : Type}
  {TS : Type}
  (P : Rule NTS TS) :
  Prop :=
  P.rhs = []


structure CFG (NTS : Type) (TS : Type) :=
  (rule_list : List (Rule NTS TS))
  (start_symbol : NTS)


/--
  is_derivation_step G lsl rsl := lsl =>G rsl
-/
def is_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS)) :
  Prop :=
    ∃
      (R : Rule NTS TS)
      (sl_1 sl_2 : Str (Symbol NTS TS)),
      R ∈ G.rule_list ∧
      lsl = sl_1 ++ [Symbol.nts R.lhs] ++ sl_2 ∧
      rsl = sl_1 ++ R.rhs ++ sl_2


def is_leftmost_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS)) :
  Prop :=
    ∃
      (R : Rule NTS TS)
      (sl_1 sl_2 : Str (Symbol NTS TS)),
      (∀ (c : Symbol NTS TS), c ∈ sl_1 → c.isTS) ∧
      R ∈ G.rule_list ∧
      lsl = sl_1 ++ [Symbol.nts R.lhs] ++ sl_2 ∧
      rsl = sl_1 ++ R.rhs ++ sl_2


example
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS))
  (h1 : is_derivation_step G lsl rsl)
  (h2 : ¬ is_leftmost_derivation_step G lsl rsl) :
    ∃
      (R : Rule NTS TS)
      (sl_1 sl_2 : Str (Symbol NTS TS)),
      ¬ (∀ (c : Symbol NTS TS), c ∈ sl_1 → c.isTS) ∧
      R ∈ G.rule_list ∧
      lsl = sl_1 ++ [Symbol.nts R.lhs] ++ sl_2 ∧
      rsl = sl_1 ++ R.rhs ++ sl_2 :=
  by
    simp only [is_derivation_step] at h1
    obtain ⟨R, sl_1, sl_2, ih_1, ⟨ih_2, ih_3⟩⟩  := h1

    simp only [is_leftmost_derivation_step] at h2
    simp at h2
    specialize h2 R sl_1

    apply Exists.intro R
    apply Exists.intro sl_1
    apply Exists.intro sl_2
    constructor
    · intro contra
      simp at ih_2
      specialize h2 contra ih_1 sl_2 ih_2
      simp at ih_3
      contradiction
    · exact ⟨ih_1, ih_2, ih_3⟩


example
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS))
  (h1 : is_derivation_step G lsl rsl)
  (h2 : ¬ is_leftmost_derivation_step G lsl rsl) :
  ∃
    (sl_1 sl_2 sl_3 sl_4 : Str (Symbol NTS TS))
    (A B : NTS),
    (∀ (c : Symbol NTS TS), c ∈ sl_1 → c.isTS) ∧
    ⟨B, sl_3⟩ ∈ G.rule_list ∧
    lsl = sl_1 ++ [Symbol.nts A] ++ sl_2 ++ [Symbol.nts B] ++ sl_4 ∧
    rsl = sl_1 ++ [Symbol.nts A] ++ sl_2 ++ sl_3 ++ sl_4 :=
  by
    simp only [is_derivation_step] at h1
    obtain ⟨R, sl_1, sl_2, ih_1, ⟨ih_2, ih_3⟩⟩  := h1

    simp only [is_leftmost_derivation_step] at h2
    simp at h2

    specialize h2 R sl_1
    sorry


def is_rightmost_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS)) :
  Prop :=
    ∃
      (R : Rule NTS TS)
      (sl_1 sl_2 : Str (Symbol NTS TS)),
      (∀ (c : Symbol NTS TS), c ∈ sl_2 → c.isTS) ∧
      R ∈ G.rule_list ∧
      lsl = sl_1 ++ [Symbol.nts R.lhs] ++ sl_2 ∧
      rsl = sl_1 ++ R.rhs ++ sl_2


def is_derivation
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Str (Symbol NTS TS) → Str (Symbol NTS TS) → Prop :=
  Relation.ReflTransGen (is_derivation_step G)


def is_leftmost_derivation
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Str (Symbol NTS TS) → Str (Symbol NTS TS) → Prop :=
  Relation.ReflTransGen (is_leftmost_derivation_step G)


def is_rightmost_derivation
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Str (Symbol NTS TS) → Str (Symbol NTS TS) → Prop :=
  Relation.ReflTransGen (is_rightmost_derivation_step G)


inductive is_derivation_alt
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Str (Symbol NTS TS) → Str (Symbol NTS TS) → Prop
| refl
  (sl : Str (Symbol NTS TS)) :
  is_derivation_alt G sl sl

| trans
  (sl_1 sl_2 sl_3 : Str (Symbol NTS TS)) :
  is_derivation_alt G sl_1 sl_2 →
  is_derivation_step G sl_2 sl_3 →
  is_derivation_alt G sl_1 sl_3


example
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  is_derivation_alt G = is_derivation G :=
  by
    ext lsl rsl
    constructor
    · intro a1
      induction a1
      case _ =>
        exact Relation.ReflTransGen.refl
      case _ sl_1 sl_2 _ ih_2 ih_3 =>
        exact Relation.ReflTransGen.tail ih_3 ih_2
    · intro a1
      induction a1
      case _ =>
        exact is_derivation_alt.refl lsl
      case _ sl_1 sl_2 _ ih_2 ih_3 =>
        exact is_derivation_alt.trans lsl sl_1 sl_2 ih_3 ih_2


def CFG.LanguageOf
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Language.Language TS :=
  { s : Str TS | is_derivation G [Symbol.nts G.start_symbol] (s.map Symbol.ts) }


def CFG.LeftLanguageOf
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Language.Language TS :=
  { s : Str TS | is_leftmost_derivation G [Symbol.nts G.start_symbol] (s.map Symbol.ts) }


def CFG.RightLanguageOf
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Language.Language TS :=
  { s : Str TS | is_rightmost_derivation G [Symbol.nts G.start_symbol] (s.map Symbol.ts) }


lemma leftmost_derivation_step_is_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS))
  (h1 : is_leftmost_derivation_step G lsl rsl) :
  is_derivation_step G lsl rsl :=
  by
    simp only [is_leftmost_derivation_step] at h1
    obtain ⟨R, sl_1, sl_2, _, a2, a3⟩ := h1
    simp only [is_derivation_step]
    exact ⟨R, sl_1, sl_2, a2, a3⟩


lemma derivation_step_to_terminal_string_is_leftmost_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (sl s : Str (Symbol NTS TS))
  (h1 : is_derivation_step G sl s)
  (h2 : ∀ (c : Symbol NTS TS), c ∈ s → c.isTS) :
  is_leftmost_derivation_step G sl s :=
  by
    simp only [is_derivation_step] at h1
    obtain ⟨R, sl_1, sl_2, a1, a2, a3⟩ := h1
    rw [a3] at h2
    have s1 : ∀ (c : Symbol NTS TS), c ∈ sl_1 → c.isTS :=
    by
      intro c a4
      apply h2 c
      simp
      left
      exact a4
    simp only [is_leftmost_derivation_step]
    exact ⟨R, sl_1, sl_2, s1, a1, a2, a3⟩


example
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS))
  (h1 : Relation.TransGen (is_derivation_step G) lsl rsl)
  (h2 : ∀ (c : Symbol NTS TS), c ∈ rsl → c.isTS) :
  Relation.TransGen (is_leftmost_derivation_step G) lsl rsl :=
  by
    induction h1
    case single sl_1 ih_1 =>
      apply Relation.TransGen.single
      exact derivation_step_to_terminal_string_is_leftmost_derivation_step G lsl sl_1 ih_1 h2
    case tail sl_1 sl_2 ih_1 ih_2 ih_3 =>
      sorry


inductive LabeledTree (α : Type) : Type
  | mk
    (order : ℕ)
    (label : α)
    (children : Fin order → LabeledTree α) :
    LabeledTree α

compile_inductive% LabeledTree

open LabeledTree


def LabeledTree.order
  {α : Type}
  (T : LabeledTree α) :
  ℕ :=
  match T with
  | mk order _ _ => order


def LabeledTree.label
  {α : Type}
  (T : LabeledTree α) :
  α :=
  match T with
  | mk _ label _ => label


def LabeledTree.children
  {α : Type}
  (T : LabeledTree α) :
  Fin T.order → LabeledTree α :=
  match T with
  | mk _ _ children => children


def LabeledTree.children_list
  {α : Type}
  (T : LabeledTree α) :
  List (LabeledTree α) :=
  List.ofFn (fun (i : Fin T.order) => (T.children i))


def LabeledTree.isLeaf
  {α : Type}
  (T : LabeledTree α) :
  Prop :=
  T.order = 0

instance (α : Type) (T : LabeledTree α) : Decidable (isLeaf T) :=
  by
  induction T
  simp only [isLeaf]
  infer_instance


/--
  The leaves of the tree from left to right.
-/
def LabeledTree.frontier
  {α : Type} :
  LabeledTree α → List α
  | mk order label children =>
    if order = 0
    then [label]
    else (List.ofFn (fun (i : Fin order) => (children i).frontier)).join
