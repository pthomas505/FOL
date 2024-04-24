import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic


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


def RegExp.languageOf (α : Type) : RegExp α → Set (List α)
  | char x => { [x] }
  | epsilon => { [] }
  | zero => ∅
  | union R S => R.languageOf ∪ S.languageOf
  | concat R S => { r ++ s | (r ∈ R.languageOf) (s ∈ S.languageOf) }
  | closure R => sorry


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
  (RegExp.closure RegExp.zero).languageOf α = RegExp.epsilon.languageOf := sorry


example
  {α : Type}
  (R : RegExp α) :
  (RegExp.concat R (RegExp.closure R)).languageOf = (RegExp.concat (RegExp.closure R) R).languageOf :=
  by
  sorry


-----

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
structure CFG (Symbol : Type) :=
  (N : Type)
  (T : Type)
  (P : N → List (N ⊕ T))
  (S : N)
