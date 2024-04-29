import Mathlib.Util.CompileInductive
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic


set_option autoImplicit false


/-
  References:

  https://github.com/leanprover-community/mathlib4/blob/f1919fd4e80a859f53111cf94437b0f85b5d345a/Mathlib/Computability/DFA.lean

  https://github.com/leanprover-community/mathlib4/blob/f1919fd4e80a859f53111cf94437b0f85b5d345a/Mathlib/Computability/NFA.lean

  http://infolab.stanford.edu/~ullman/focs.html
-/


/--
  The type of deterministic automatons.
  `α` is the type of input characters.
  `σ` is the type of states.

  Transitions from one state to another state on each input character. The state that it transitions to is permitted to be the same state that it transitioned from.

  If the deterministic automaton `D` is at state `s` and the input sequence is `c :: cs` then `D` transitions to the state given by `D.step s c` and the input sequence becomes `cs`.
-/
structure DA (α : Type) (σ : Type) : Type :=
  (step : σ → α → σ)
  (startingState : σ)
  (acceptingStates : Set σ)


def DA.evalFrom
  {α : Type}
  {σ : Type}
  (D : DA α σ)
  (startingState : σ) :
  List α → σ :=
  List.foldl D.step startingState


/--
  `DA.eval D cs` := Returns the final state that the deterministic automaton `D` transitions to if it starts at `D.startingState` and consumes the list of characters `cs`.
-/
def DA.eval
  {α : Type}
  {σ : Type}
  (D : DA α σ) :
  List α → σ :=
  D.evalFrom D.startingState


def DA.accepts
  {α : Type}
  {σ : Type}
  (D : DA α σ)
  (input : List α) :
  Prop :=
  D.eval input ∈ D.acceptingStates


/--
  The type of nondeterministic automatons.
  `α` is the type of input characters.
  `σ` is the type of states.

  Transitions from one set of states to another set of states on each input character. The set of states that it transitions to is permitted to be the same set of states that it transitioned from.

  If the nondeterministic automaton `N` is at the set of states `S` and the input sequence is `c :: cs` then `N` transitions to the set of states given by `⋃ s ∈ S, N.step s c` and the input sequence becomes `cs`. If `s1 ∈ S` and `s2 ∈ S` then `⋃ s ∈ S, N.step s c` includes `(N.step s1 c) ∪ (N.step s2 c)`.
-/
structure NA (α : Type) (σ : Type) : Type :=
  (step : σ → α → Set σ)
  (startingStates : Set σ)
  (acceptingStates : Set σ)


/--
  `NA.stepSet N S c` := Returns the set of states that the nondeterministic automaton `N` transitions to if it starts at the set of states `S` and consumes the character `c`.
-/
def NA.stepSet
  {α : Type}
  {σ : Type}
  (N : NA α σ)
  (S : Set σ)
  (c : α) :
  Set σ :=
  ⋃ s ∈ S, N.step s c


def NA.evalFrom
  {α : Type}
  {σ : Type}
  (N : NA α σ)
  (startingStates : Set σ) :
  List α → Set σ :=
  List.foldl N.stepSet startingStates


/--
  `NA.eval N cs` := Returns the final set of states that the nondeterministic automaton `N` transitions to if it starts at `N.startingStates` and consumes the list of characters `cs`.
-/
def NA.eval
  {α : Type}
  {σ : Type}
  (N : NA α σ) :
  List α → Set σ :=
  N.evalFrom N.startingStates


def NA.accepts
  {α : Type}
  {σ : Type}
  (N : NA α σ)
  (input : List α) :
  Prop :=
  ∃ (s : σ), s ∈ N.eval input ∧ s ∈ N.acceptingStates


/--
  The subset construction of a deterministic automaton from a nondeterministic automaton.

  Each state in the deterministic automaton is a subset of the states of the nondeterministic automaton.
-/
def NA.toDA
  {α : Type}
  {σ : Type}
  (N : NA α σ) :
  DA α (Set σ) := {
    step := N.stepSet
    startingState := N.startingStates
    acceptingStates := { S : Set σ | ∃ (s : σ), s ∈ S ∧ s ∈ N.acceptingStates }
  }


example
  {α : Type}
  {σ : Type}
  (N : NA α σ) :
  (NA.toDA N).startingState = N.startingStates :=
  by rfl


lemma DA.memAccepts
  {α : Type}
  {σ : Type}
  (D : DA α σ)
  (input : List α) :
  D.accepts input ↔
    D.evalFrom D.startingState input ∈ D.acceptingStates := by rfl


lemma NA.memAccepts
  {α : Type}
  {σ : Type}
  (N : NA α σ)
  (input : List α) :
  N.accepts input ↔
    ∃ (s : σ), s ∈ N.evalFrom N.startingStates input ∧
      s ∈ N.acceptingStates := by rfl


/--
  The subset construction of a deterministic automaton from a nondeterministic automaton yields a deterministic automaton that is equivalent to the nondeterministic automaton.
-/
theorem NAtoDAisEquiv
  {α : Type}
  {σ : Type}
  (N : NA α σ) :
  N.toDA.accepts = N.accepts :=
  by
  ext cs
  simp only [DA.memAccepts]
  simp only [NA.memAccepts]
  simp only [NA.toDA]
  simp
  constructor
  all_goals
    simp
    intro s a1 a2
    apply Exists.intro s
    tauto


/--
  union R S = (R | S)
  closure R = R*
-/
inductive RegExp (α : Type) : Type
  | char : α → RegExp α
  | epsilon : RegExp α
  | zero : RegExp α
  | union : RegExp α → RegExp α → RegExp α
  | concat : RegExp α → RegExp α → RegExp α
  | closure : RegExp α → RegExp α
  deriving Repr


def RegExp.concat_n {α : Type} (R : RegExp α) : ℕ → RegExp α
  | 0 => RegExp.epsilon
  | (n + 1) => RegExp.concat R (RegExp.concat_n R n)

#eval RegExp.concat_n (RegExp.char 'a') 0
#eval RegExp.concat_n (RegExp.char 'a') 1


def RegExp.languageOf (α : Type) : RegExp α → Set (List α)
  | char x => { [x] }
  | epsilon => { [] }
  | zero => ∅
  | union R S => R.languageOf ∪ S.languageOf

  -- For each string r in L(R) and each string s in L(S), the string rs, the concatenation of strings r and s, is in L(RS).
  | concat R S => { r ++ s | (r ∈ R.languageOf) (s ∈ S.languageOf) }

  -- l is the concatenation of a list of strings, each of which is in L(R).
  | closure R => { l | ∃ rs : List (List α), (∀ (r : List α), r ∈ rs → r ∈ R.languageOf) ∧ rs.join = l }


example
  {α : Type}
  (R : RegExp α) :
  (RegExp.union R RegExp.zero).languageOf = R.languageOf ∧
    (RegExp.union RegExp.zero R).languageOf = R.languageOf :=
  by
  simp only [RegExp.languageOf]
  simp


example
  {α : Type}
  (R : RegExp α) :
  (RegExp.concat R RegExp.epsilon).languageOf = R.languageOf ∧
    (RegExp.concat RegExp.epsilon R).languageOf = R.languageOf :=
  by
  simp only [RegExp.languageOf]
  simp


example
  {α : Type}
  (R : RegExp α) :
  (RegExp.concat R RegExp.zero).languageOf = RegExp.zero.languageOf ∧
    (RegExp.concat RegExp.zero R).languageOf = RegExp.zero.languageOf :=
  by
  simp only [RegExp.languageOf]
  simp


example
  {α : Type}
  (R S : RegExp α) :
  (RegExp.union R S).languageOf = (RegExp.union S R).languageOf :=
  by
  simp only [RegExp.languageOf]
  exact Set.union_comm (RegExp.languageOf α R) (RegExp.languageOf α S)


example
  {α : Type}
  (R S T : RegExp α) :
  (RegExp.union (RegExp.union R S) T).languageOf =
    (RegExp.union R (RegExp.union S T)).languageOf :=
  by
  simp only [RegExp.languageOf]
  exact Set.union_assoc (RegExp.languageOf α R) (RegExp.languageOf α S) (RegExp.languageOf α T)


example
  {α : Type}
  (R S T : RegExp α) :
  (RegExp.concat (RegExp.concat R S) T).languageOf =
    (RegExp.concat R (RegExp.concat S T)).languageOf :=
  by
  simp only [RegExp.languageOf]
  simp


example
  {α : Type}
  (R S T : RegExp α) :
  (RegExp.concat R (RegExp.union S T)).languageOf =
    (RegExp.union (RegExp.concat R S) (RegExp.concat R T)).languageOf :=
  by
  simp only [RegExp.languageOf]
  ext cs
  constructor
  · simp
    intro xs a1 ys a2 a3
    subst a3
    cases a2
    case _ c1 =>
      left
      apply Exists.intro xs
      constructor
      · exact a1
      · apply Exists.intro ys
        tauto
    case _ c1 =>
      right
      apply Exists.intro xs
      constructor
      · exact a1
      · apply Exists.intro ys
        tauto
  · simp
    intro a1
    cases a1
    all_goals
      case _ c1 =>
        apply Exists.elim c1
        intro xs a2
        clear c1
        cases a2
        case _ a2_left a2_right =>
          apply Exists.elim a2_right
          intro ys a3
          apply Exists.intro xs
          constructor
          · tauto
          · apply Exists.intro ys
            tauto


example
  {α : Type}
  (R S T : RegExp α) :
  (RegExp.concat (RegExp.union S T) R).languageOf =
    (RegExp.union (RegExp.concat S R) (RegExp.concat T R)).languageOf :=
  by
  simp only [RegExp.languageOf]
  aesop


example
  {α : Type} :
  (RegExp.closure RegExp.zero).languageOf α = RegExp.epsilon.languageOf :=
  by
  simp only [RegExp.languageOf]
  ext cs
  simp
  constructor
  · intro a1
    apply Exists.elim a1
    intro rs a2
    cases a2
    case _ a2_left a2_right =>
      simp only [← a2_right]
      simp only [← List.eq_nil_iff_forall_not_mem] at a2_left
      simp only [a2_left]
      simp
  · intro a1
    apply Exists.intro []
    tauto


example
  {α : Type}
  (R : RegExp α) :
  (RegExp.concat R (RegExp.closure R)).languageOf = (RegExp.concat (RegExp.closure R) R).languageOf :=
  by
  sorry


/--
  The Brzozowski derivative u^{-1}S of a set S of strings and a string u is the set of all strings obtainable from a string in S by cutting off the prefix u.
-/
def Brzozowski_derivative
  (S : Set (String))
  (u : String) :
  Set String :=
  { v : String | u ++ v ∈ S }


-----

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
