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
  directly_derives G lsl rsl := lsl =>G rsl
-/
def directly_derives
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


def directly_derives_left
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


def directly_derives_right
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


def derives_in
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Str (Symbol NTS TS) → Str (Symbol NTS TS) → Prop :=
  Relation.ReflTransGen (directly_derives G)


def derives_in_left
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Str (Symbol NTS TS) → Str (Symbol NTS TS) → Prop :=
  Relation.ReflTransGen (directly_derives_left G)


def derives_in_right
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Str (Symbol NTS TS) → Str (Symbol NTS TS) → Prop :=
  Relation.ReflTransGen (directly_derives_right G)


inductive derives_in_alt
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Str (Symbol NTS TS) → Str (Symbol NTS TS) → Prop
| refl
  (sl : Str (Symbol NTS TS)) :
  derives_in_alt G sl sl

| trans
  (sl_1 sl_2 sl_3 : Str (Symbol NTS TS)) :
  derives_in_alt G sl_1 sl_2 →
  directly_derives G sl_2 sl_3 →
  derives_in_alt G sl_1 sl_3


example
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  derives_in_alt G = derives_in G :=
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
        exact derives_in_alt.refl lsl
      case _ sl_1 sl_2 _ ih_2 ih_3 =>
        exact derives_in_alt.trans lsl sl_1 sl_2 ih_3 ih_2


def CFG.LanguageOf
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Language.Language TS :=
  { s : Str TS | derives_in G [Symbol.nts G.start_symbol] (s.map Symbol.ts) }


def CFG.LeftLanguageOf
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Language.Language TS :=
  { s : Str TS | derives_in_left G [Symbol.nts G.start_symbol] (s.map Symbol.ts) }


def CFG.RightLanguageOf
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Language.Language TS :=
  { s : Str TS | derives_in_right G [Symbol.nts G.start_symbol] (s.map Symbol.ts) }


lemma directly_derives_left_imp_directly_derives
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS))
  (h1 : directly_derives_left G lsl rsl) :
  directly_derives G lsl rsl :=
  by
    simp only [directly_derives_left] at h1
    obtain ⟨R, sl_1, sl_2, _, a2, a3⟩ := h1
    simp only [directly_derives]
    exact ⟨R, sl_1, sl_2, a2, a3⟩


lemma directly_derives_terminal_str_imp_directly_derives_left
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (sl s : Str (Symbol NTS TS))
  (h1 : directly_derives G sl s)
  (h2 : ∀ (c : Symbol NTS TS), c ∈ s → c.isTS) :
  directly_derives_left G sl s :=
  by
    simp only [directly_derives] at h1
    obtain ⟨R, sl_1, sl_2, a1, a2, a3⟩ := h1
    rw [a3] at h2
    have s1 : ∀ (c : Symbol NTS TS), c ∈ sl_1 → c.isTS :=
    by
      intro c a4
      apply h2 c
      simp
      left
      exact a4
    simp only [directly_derives_left]
    exact ⟨R, sl_1, sl_2, s1, a1, a2, a3⟩


example
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS))
  (h1 : Relation.TransGen (directly_derives G) lsl rsl)
  (h2 : ∀ (c : Symbol NTS TS), c ∈ rsl → c.isTS) :
  Relation.TransGen (directly_derives_left G) lsl rsl :=
  by
    induction h1
    case single sl_1 ih_1 =>
      apply Relation.TransGen.single
      exact directly_derives_terminal_str_imp_directly_derives_left G lsl sl_1 ih_1 h2
    case tail sf_1 sf_2 ih_1 ih_2 ih_3 =>
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
