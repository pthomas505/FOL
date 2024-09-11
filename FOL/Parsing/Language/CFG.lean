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


abbrev SententialForm (N : Type) (T : Type) : Type := Str (N ⊕ T)

abbrev Sentence (T : Type) : Type := Str T

def SententialForm.IsSentence
  (N : Type)
  (T : Type)
  (sf : SententialForm N T) :
  Prop :=
  ∀ (symbol : (N ⊕ T)), symbol ∈ sf → symbol.isRight


structure Production (N : Type) (T : Type) :=
  (lhs : N)
  (rhs : SententialForm N T)

structure CFG (N : Type) (T : Type) :=
  (production_list : List (Production N T))
  (start_symbol : N)


/--
  directly_derives G alpha_0 alpha_1 := alpha_0 =>G alpha_1
-/
inductive directly_derives
  {N : Type}
  {T : Type}
  (G : CFG N T) :
  SententialForm N T → SententialForm N T → Prop
  | directly_derives
    (alpha_0 alpha_1 : SententialForm N T)
    (A : N)
    (alpha beta gamma : SententialForm N T) :
    ⟨A, beta⟩ ∈ G.production_list →
    alpha_0 = alpha ++ [Sum.inl A] ++ gamma →
    alpha_1 = alpha ++ beta ++ gamma →
    directly_derives G alpha_0 alpha_1


inductive directly_derives_left
  {N : Type}
  {T : Type}
  (G : CFG N T) :
  SententialForm N T → SententialForm N T → Prop
  | directly_derives_left
    (alpha_0 alpha_1 : SententialForm N T)
    (A : N)
    (alpha beta gamma : SententialForm N T) :
    alpha.IsSentence →
    ⟨A, beta⟩ ∈ G.production_list →
    alpha_0 = alpha ++ [Sum.inl A] ++ gamma →
    alpha_1 = alpha ++ beta ++ gamma →
    directly_derives_left G alpha_0 alpha_1


inductive directly_derives_right
  {N : Type}
  {T : Type}
  (G : CFG N T) :
  SententialForm N T → SententialForm N T → Prop
  | directly_derives_right
    (alpha_0 alpha_1 : SententialForm N T)
    (A : N)
    (alpha beta gamma : SententialForm N T) :
    gamma.IsSentence →
    ⟨A, beta⟩ ∈ G.production_list →
    alpha_0 = alpha ++ [Sum.inl A] ++ gamma →
    alpha_1 = alpha ++ beta ++ gamma →
    directly_derives_right G alpha_0 alpha_1


def derives_in
  {N : Type}
  {T : Type}
  (G : CFG N T) :
  SententialForm N T → SententialForm N T → Prop :=
  Relation.ReflTransGen (directly_derives G)


def derives_in_left
  {N : Type}
  {T : Type}
  (G : CFG N T) :
  SententialForm N T → SententialForm N T → Prop :=
  Relation.ReflTransGen (directly_derives_left G)


def derives_in_right
  {N : Type}
  {T : Type}
  (G : CFG N T) :
  SententialForm N T → SententialForm N T → Prop :=
  Relation.ReflTransGen (directly_derives_right G)


/--
  derives_in G alpha_0 alpha_m := alpha_0 =>G* alpha_m
-/
inductive derives_in_example
  {N : Type}
  {T : Type}
  (G : CFG N T) :
  SententialForm N T → SententialForm N T → Prop
| refl
  (alpha : SententialForm N T) :
  derives_in_example G alpha alpha

| trans
  (alpha_0 alpha_1 alpha_2 : SententialForm N T) :
  derives_in_example G alpha_0 alpha_1 →
  directly_derives G alpha_1 alpha_2 →
  derives_in_example G alpha_0 alpha_2


example
  {N : Type}
  {T : Type}
  (G : CFG N T) :
  derives_in_example G = derives_in G :=
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
        exact derives_in_example.refl sf_1
      case _ alpha_0 alpha_1 _ ih_2 ih_3 =>
        exact derives_in_example.trans sf_1 alpha_0 alpha_1 ih_3 ih_2


def CFG.LanguageOf
  {N : Type}
  {T : Type}
  (G : CFG N T) :
  Set (Sentence T) :=
  { s : Sentence T | derives_in G [Sum.inl G.start_symbol] (s.map Sum.inr) }


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
