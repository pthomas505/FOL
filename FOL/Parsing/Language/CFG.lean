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


abbrev SententialForm
  (NTS : Type)
  (TS : Type) :
  Type :=
  Str (Symbol NTS TS)


abbrev Sentence (TS : Type) : Type := Str TS


def SententialForm.isSentence
  (NTS : Type)
  (TS : Type)
  (sf : SententialForm NTS TS) :
  Prop :=
  ∀ (c : Symbol NTS TS), c ∈ sf → c.isTS


structure Rule (NTS : Type) (TS : Type) :=
  (lhs : NTS)
  (rhs : SententialForm NTS TS)


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
  (sf_l sf_r : SententialForm NTS TS) :
  Prop :=
    ∃
      (lhs : NTS)
      (rhs : SententialForm NTS TS)
      (sf_1 sf_2 : SententialForm NTS TS),
      ⟨lhs, rhs⟩ ∈ G.rule_list ∧
      sf_l = sf_1 ++ [Symbol.nts lhs] ++ sf_2 ∧
      sf_r = sf_1 ++ rhs ++ sf_2


def directly_derives_left
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (sf_l sf_r : SententialForm NTS TS) :
  Prop :=
    ∃
      (lhs : NTS)
      (rhs : SententialForm NTS TS)
      (sf_1 sf_2 : SententialForm NTS TS),
      sf_1.isSentence ∧
      ⟨lhs, rhs⟩ ∈ G.rule_list ∧
      sf_l = sf_1 ++ [Symbol.nts lhs] ++ sf_2 ∧
      sf_r = sf_1 ++ rhs ++ sf_2


def directly_derives_right
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (sf_l sf_r : SententialForm NTS TS) :
  Prop :=
    ∃
      (lhs : NTS)
      (rhs : SententialForm NTS TS)
      (sf_1 sf_2 : SententialForm NTS TS),
      sf_2.isSentence ∧
      ⟨lhs, rhs⟩ ∈ G.rule_list ∧
      sf_l = sf_1 ++ [Symbol.nts lhs] ++ sf_2 ∧
      sf_r = sf_1 ++ rhs ++ sf_2


/--
  derives_in G alpha_0 alpha_m := alpha_0 =>G* alpha_m
-/
inductive derives_in
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  SententialForm NTS TS → SententialForm NTS TS → Prop
| refl
  (sf : SententialForm NTS TS) :
  derives_in G sf sf

| trans
  (sf_1 sf_2 sf_3 : SententialForm NTS TS) :
  derives_in G sf_1 sf_2 →
  directly_derives G sf_2 sf_3 →
  derives_in G sf_1 sf_3


inductive derives_in_left
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  SententialForm NTS TS → SententialForm NTS TS → Prop
| refl
  (sf : SententialForm NTS TS) :
  derives_in_left G sf sf

| trans
  (sf_1 sf_2 sf_3 : SententialForm NTS TS) :
  derives_in_left G sf_1 sf_2 →
  directly_derives_left G sf_2 sf_3 →
  derives_in_left G sf_1 sf_3


inductive derives_in_right
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  SententialForm NTS TS → SententialForm NTS TS → Prop
| refl
  (sf : SententialForm NTS TS) :
  derives_in_right G sf sf

| trans
  (sf_1 sf_2 sf_3 : SententialForm NTS TS) :
  derives_in_right G sf_1 sf_2 →
  directly_derives_right G sf_2 sf_3 →
  derives_in_right G sf_1 sf_3


example
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  derives_in G = Relation.ReflTransGen (directly_derives G) :=
  by
    ext sf_1 sf_2
    constructor
    · intro a1
      induction a1
      case _ =>
        exact Relation.ReflTransGen.refl
      case _ alpha_0 alpha_1 _ ih_2 ih_3 =>
        exact Relation.ReflTransGen.tail ih_3 ih_2
    · intro a1
      induction a1
      case _ =>
        exact derives_in.refl sf_1
      case _ alpha_0 alpha_1 _ ih_2 ih_3 =>
        exact derives_in.trans sf_1 alpha_0 alpha_1 ih_3 ih_2


def CFG.LanguageOf
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Language.Language TS :=
  { s : Sentence TS | derives_in G [Symbol.nts G.start_symbol] (s.map Symbol.ts) }


def CFG.LeftLanguageOf
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Language.Language TS :=
  { s : Sentence TS | derives_in_left G [Symbol.nts G.start_symbol] (s.map Symbol.ts) }


def CFG.RightLanguageOf
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Language.Language TS :=
  { s : Sentence TS | derives_in_right G [Symbol.nts G.start_symbol] (s.map Symbol.ts) }


lemma directly_derives_left_imp_directly_derives
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (sf_l sf_r : SententialForm NTS TS)
  (h1 : directly_derives_left G sf_l sf_r) :
  directly_derives G sf_l sf_r :=
  by
    simp only [directly_derives_left] at h1
    obtain ⟨lhs, rhs, sf_1, sf_2, _, a2, a3⟩ := h1
    exact ⟨lhs, rhs, sf_1, sf_2, a2, a3⟩

example
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  G.LeftLanguageOf = G.LanguageOf :=
  by
    sorry


inductive LabeledTree (α : Type) : Type
  | mk
    (order : ℕ)
    (label : Option α)
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
  Option α :=
  match T with
  | mk _ label _ => label


def LabeledTree.children
  {α : Type}
  (T : LabeledTree α) :
  Fin T.order → LabeledTree α :=
  match T with
  | mk _ _ children => children


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
    if h : order = 0 ∧ label.isSome
    then [label.get h.right]
    else (List.ofFn (fun (i : Fin order) => (children i).frontier)).join
