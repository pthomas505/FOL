import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic


set_option autoImplicit false


-- https://arxiv.org/pdf/1509.02032.pdf


/-
  The definition of a context free grammar.

  An alphabet Σ is a finite, non-empty set of indivisible symbols.
  A string over an alphabet Σ is a finite sequence of members of Σ.

  N is a non-terminal alphabet.
  T is a terminal alphabet such that N ∩ T = ∅.
  P ⊆ N × (N ∪ T)* is a set of productions.
  S ∈ N is the start symbol.
-/


abbrev SententialForm (N : Type) (T : Type) : Type := List (N ⊕ T)

abbrev Sentence (T : Type) : Type := List T


structure Production (N : Type) (T : Type) :=
  (subject : N)
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


/--
  derives_in G alpha_0 alpha_m := alpha_0 =>G* alpha_m
-/
inductive derives_in
  {N : Type}
  {T : Type}
  (G : CFG N T) :
  SententialForm N T → SententialForm N T → Prop
| refl
  (alpha : SententialForm N T) :
  derives_in G alpha alpha

| trans
  (alpha_0 alpha_1 alpha_2 : SententialForm N T) :
  derives_in G alpha_0 alpha_1 →
  directly_derives G alpha_1 alpha_2 →
  derives_in G alpha_0 alpha_2


example
  {N : Type}
  {T : Type}
  (G : CFG N T) :
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
