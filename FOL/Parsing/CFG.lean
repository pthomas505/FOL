
-- https://arxiv.org/pdf/1509.02032.pdf
/-
/-
  The definition of a context free grammar.

  An alphabet Σ is a finite, non-empty set of indivisible symbols.
  A string over an alphabet Σ is a finite sequence of members of Σ.

  N is a non-terminal alphabet.
  T is a terminal alphabet such that N ∩ T = ∅.
  P ⊆ N × (N ∪ T)* is a set of productions.
  S ∈ N is the start symbol.
-/
structure CFG :=
  (N : Type)
  (N_finite : Finite N)
  (N_nonempty: Nonempty N)
  (T : Type)
  (T_finite : Finite T)
  (T_nonempty: Nonempty T)
  (P : Set (N × (List (N ⊕ T))))
  (S : N)


/--
  derives g a b := b  a =>_g^* b
-/
inductive derives
  (g : CFG) :
  List (g.N ⊕ g.T) → List (g.N ⊕ g.T) → Prop

| refl
  (sf : List (g.N ⊕ g.T)) :
  derives g sf sf

| step
  (s1 s2 s3 : List (g.N ⊕ g.T))
  (subject : g.N)
  (rhs : List (g.N ⊕ g.T)) :
  derives g s1 (s2 ++ (Sum.inl subject :: s3)) →
  (subject, rhs) ∈ g.P  →
  derives g s1 (s2 ++ rhs ++ s3)


def CFG.generates
  (g : CFG)
  (s : List (g.N ⊕ g.T)) :
  Prop :=
  derives g [Sum.inl g.S] s


def CFG.produces
  (g : CFG)
  (s : List g.T) :
  Prop :=
  derives g [Sum.inl g.S] (s.map Sum.inr)


def CFG.languageOf
  (g : CFG) :
  Set (List g.T) :=
  { s : List g.T | g.produces s }


inductive LabeledTree (α : Type) : Type
  | node
    (label : α)
    (order : ℕ)
    (children : Fin order → LabeledTree α) :
    LabeledTree α

compile_inductive% LabeledTree

open LabeledTree


def LabeledTree.label
  {α : Type}
  (T : LabeledTree α) :
  α :=
  match T with
  | node label _ _ => label


def LabeledTree.order
  {α : Type}
  (T : LabeledTree α) :
  ℕ :=
  match T with
  | node _ order _ => order


def LabeledTree.children
  {α : Type}
  (T : LabeledTree α) :
  Fin T.order → LabeledTree α :=
  match T with
  | node _ _ children => children


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
  | node label order children =>
    if order = 0
    then [label]
    else (List.ofFn (fun i : Fin order => (children i).frontier)).join


inductive isParseNode
  (g : CFG) :
  LabeledTree (g.N ⊕ g.T) → Prop

  | non_terminal
    (T : LabeledTree (g.N ⊕ g.T))
    (h : T.label.isLeft) :
    ¬ T.isLeaf →
    (T.label.getLeft h, (List.ofFn T.children).map label) ∈ g.P →
    (∀ (i : Fin T.order), isParseNode g (T.children i)) →
    isParseNode g T

  | terminal
    (T : LabeledTree (g.N ⊕ g.T)) :
    T.label.isRight →
    T.isLeaf →
    isParseNode g T
-/



/-
structure Grammar (Symbol : Type) [DecidableEq Symbol] :=
  -- The set of nonterminal symbols.
  (N : Finset Symbol)
  (N_nonempty : Nonempty N)

  -- The set of terminal symbols.
  (T : Finset Symbol)
  (T_nonempty : Nonempty T)

  (N_T_disjoint : Disjoint N T)

  -- The set of productions.
  (P : Finset (N × (List (N ⊕ T))))

  -- The start symbol.
  (S : N)


inductive SententialForm (Symbol : Type) [DecidableEq Symbol] (G : Grammar Symbol) : Prop
  | start : G.S → SententialForm Symbol G
  | derive (subject : SententialForm Symbol G) :
-/

/-
Our definition of a language L is a set of finite-length strings over some finite alphabet Σ.
-/


/-
  An alphabet Σ is a finite, non-empty set of indivisible symbols.
  A string over an alphabet Σ is a finite sequence of members of Σ.
  The set of all strings over an alphabet Σ is denoted Σ*.
  A language L is a set of strings over some alphabet Σ. Hence L is a subset of Σ*.

  A grammar is a 4-tuple G = (N, Σ, P, S) where
  (1) N is a finite set of nonterminal symbols (sometimes called variables or
syntactic categories).
  (2) Σ is a finite set of terminal symbols, disjoint from N.
  (3) P is a finite subset of (N ∪ Σ)* N (N ∪ Σ)* x (N ∪ Σ)*.
  An element (α, β) in P will be written α → β and called a production.
  (4) S is a distinguished symbol in N called the sentence (or start) symbol.

-/
