import Mathlib.Data.Set.Lattice


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
  (startState : σ) :
  List α → σ :=
  List.foldl D.step startState


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

  If the nondeterministic automaton `N` is at the set of states `S` and the input sequence is `c :: cs` then `N` transitions to the set of states given by `⋃ s ∈ S, N.step s a` and the input sequence becomes `cs`.
-/
structure NA (α : Type) (σ : Type) : Type :=
  (step : σ → α → Set σ)
  (startingStates : Set σ)
  (acceptingStates : Set σ)


def NA.stepSet
  {α : Type}
  {σ : Type}
  (N : NA α σ)
  (S : Set σ)
  (a : α) :
  Set σ :=
  ⋃ s ∈ S, N.step s a


def NA.evalFrom
  {α : Type}
  {σ : Type}
  (N : NA α σ)
  (startingStates : Set σ) :
  List α → Set σ :=
  List.foldl N.stepSet startingStates


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
  ∃ (S : σ), S ∈ N.eval input ∧ S ∈ N.acceptingStates


/--
  The subset construction of a deterministic automaton from a nondeterministic automaton.
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
    ∃ (S : σ), S ∈ N.evalFrom N.startingStates input ∧
      S ∈ N.acceptingStates := by rfl


/--
  The subset construction of a deterministic automaton from a nondeterministic automaton yields a deterministic automaton that is equivalent to the nondeterministic automaton.
-/
theorem NAtoDAisEquiv
  {α : Type}
  {σ : Type}
  (N : NA α σ) :
  N.toDA.accepts = N.accepts :=
  by
  ext xs
  simp only [DA.memAccepts]
  simp only [NA.memAccepts]
  simp only [NA.toDA]
  simp
  constructor
  all_goals
    simp
    intro x a1 a2
    apply Exists.intro x
    tauto
