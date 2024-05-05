import Mathlib.Util.CompileInductive
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic

import FOL.FunctionUpdateITE


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

compile_inductive% RegExp

open RegExp


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
  · aesop
  · intro a1
    apply Exists.intro []
    simp
    simp only [a1]


example
  {α : Type}
  (R : RegExp α) :
  (RegExp.concat R (RegExp.closure R)).languageOf = (RegExp.concat (RegExp.closure R) R).languageOf :=
  by
  simp only [RegExp.languageOf]
  ext cs
  simp
  constructor
  · intro a1
    apply Exists.elim a1
    intro r a2
    clear a1

    cases a2
    case _ a2_left a2_right =>
      apply Exists.elim a2_right
      intro rs a3
      clear a2_right

      cases a3
      case _ a3_left a3_right =>
        · have s1 := List.eq_nil_or_concat (r :: rs)
          simp at s1

          apply Exists.elim s1
          intro rs' a4
          clear s1

          apply Exists.elim a4
          intro r' a5
          clear a4

          have s2 : ∀ (x : List α), x ∈ (r :: rs) → x ∈ RegExp.languageOf α R
          simp
          tauto

          apply Exists.intro rs'
          constructor
          · intro x a6
            apply s2
            simp only [a5]
            simp
            left
            exact a6

          · apply Exists.intro r'
            constructor
            · apply s2
              simp only [a5]
              simp
            · simp only [← a3_right]

              have s3 : List.join rs' ++ r' = List.join (rs' ++ [r'])
              simp

              simp only [s3]

              have s4 : r ++ List.join rs = List.join (r :: rs)
              simp

              simp only [s4]

              simp only [a5]
  · intro a1
    apply Exists.elim a1
    intro rs a2
    clear a1
    cases a2
    case _ a2_left a2_right =>
      apply Exists.elim a2_right
      intro r a3
      clear a2_right
      cases a3
      case _ a3_left a3_right =>
        subst a3_right

        have s2 : List.join rs ++ r = List.join (rs ++ [r])
        simp

        simp only [s2]
        clear s2

        have s3 : r ++ List.join rs = List.join ([r] ++ rs)
        simp

        cases rs
        case nil =>
          apply Exists.intro r
          constructor
          · exact a3_left
          · apply Exists.intro []
            simp
        case cons hd tl =>
          simp at a2_left
          cases a2_left
          case _ a2_left_left a2_left_right =>
            apply Exists.intro hd
            constructor
            · exact a2_left_left
            · apply Exists.intro (tl ++ [r])
              constructor
              · simp
                intro r' a4
                cases a4
                case _ a4_left =>
                  apply a2_left_right
                  exact a4_left
                case _ a4_right =>
                  subst a4_right
                  exact a3_left
              · simp

-----

namespace RegExpToNDA


inductive RegExp (α : Type) [DecidableEq α] : Type
  | char : α → RegExp α
  | epsilon : RegExp α
  | zero : RegExp α
  | union : RegExp α → RegExp α → RegExp α
  | concat : RegExp α → RegExp α → RegExp α
  | closure : RegExp α → RegExp α
  deriving Repr


def RegExp.languageOf (α : Type) [DecidableEq α] : RegExp α → Set (List α)
  | char x => { [x] }
  | epsilon => { [] }
  | zero => ∅
  | union R S => R.languageOf ∪ S.languageOf

  -- For each string r in L(R) and each string s in L(S), the string rs, the concatenation of strings r and s, is in L(RS).
  | concat R S => { r ++ s | (r ∈ R.languageOf) (s ∈ S.languageOf) }

  -- l is the concatenation of a list of strings, each of which is in L(R).
  | closure R => { l | ∃ rs : List (List α), (∀ (r : List α), r ∈ rs → r ∈ R.languageOf) ∧ rs.join = l }


/--
  The type of nondeterministic automatons.
  `α` is the type of input symbols.
  `σ` is the type of states.

  `symbolSet` is the set of all of the symbols that the automaton can step from one state in `stateSet` to another on.

  If the automaton `e` is at state `s` and the input sequence is `c :: cs` and there is a step `((s, Option.some c), S)` in `e.stepList`, then `e` simultaneously transitions to each of the states in `S` and the input sequence becomes `cs`.

  If the automation `e` is at state `s` and the input sequence is `cs` and there is a step `((s, Option.none), S)` in `e.stepList`, then `e` simultaneously transitions to each of the states in `S` and the input sequence remains `cs`.

  `startingStateList` is the list of states that the automaton starts at.

  If the automaton `e` is at a state in `e.acceptingStateList` and there are no remaining symbols in the input sequence, then `e` accepts the input sequence.
-/
structure NDA
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ] :
  Type :=
/-
  (stateSet : Set σ)
  (symbolSet : Set α)
-/
  (stepList : List ((σ × Option α) × List σ))
  (startingStateList : List σ)
  (acceptingStateList : List σ)
  deriving Repr


/--
  Helper function for stepListToFun.
-/
def stepListToFunAux
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (stepList : List ((σ × Option α) × List σ))
  (stateArg : σ)
  (symbolArg : α)
  -- The accumulated results of all of the steps that have the state and symbol arguments as a pair.
  (imageAcc : List σ) :
  List σ :=
  match stepList with
  | [] => List.dedup imageAcc
  | ((state, Option.some symbol), state_list) :: tl =>
    let image : List σ :=
      if stateArg = state ∧ symbolArg = symbol
      then state_list
      else []
    stepListToFunAux tl stateArg symbolArg (imageAcc ++ image)
  | ((state, Option.none), state_list) :: tl =>
    let image : List σ :=
      if stateArg = state
      then state_list
      else []
    stepListToFunAux tl stateArg symbolArg (imageAcc ++ image)


/--
  Recursively iterates through the step list and returns the accumulated results of all of the steps that have the state and symbol arguments as a pair.
-/
def stepListToFun
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (stepList : List ((σ × Option α) × List σ))
  (stateArg : σ)
  (symbolArg : α) :
  List σ :=
  stepListToFunAux stepList stateArg symbolArg []


example : stepListToFun ([] : List ((ℕ × Option Char) × List ℕ)) 0 'a' == [] := by rfl

example : stepListToFun [((0, Option.some 'a'), [1])] 0 'a' == [1] := by rfl

example : stepListToFun [((0, Option.some 'a'), [1])] 0 'b' == [] := by rfl

example : stepListToFun [((0, Option.none), [1])] 0 'a' == [1] := by rfl

example : stepListToFun [((0, Option.some 'a'), [1]), ((0, Option.some 'b'), [1])] 0 'a' == [1] := by rfl

example : stepListToFun [((0, Option.some 'a'), [1]), ((0, Option.some 'b'), [1])] 0 'b' == [1] := by rfl

example : stepListToFun [((0, Option.some 'a'), [1]), ((0, Option.some 'b'), [2])] 0 'a' == [1] := by rfl

example : stepListToFun [((0, Option.some 'a'), [1]), ((0, Option.some 'b'), [2])] 0 'b' == [2] := by rfl

example : stepListToFun [((0, Option.some 'a'), [1]), ((0, Option.some 'a'), [2])] 0 'a' == [1, 2] := by rfl


/--
  `NDA.evalOne e l c` := Returns the list of states that the nondeterministic automaton `e` transitions to if it starts at the list of states `l` and consumes the symbol `c`.
-/
def NDA.evalOne
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : NDA α σ)
  (stateList : List σ)
  (symbol : α) :
  List σ :=
  (stateList.map (fun (state : σ) => stepListToFun e.stepList state symbol)).join.dedup


def NDA.evalFrom
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : NDA α σ)
  (startingStateList : List σ) :
  List α → List σ :=
  List.foldl e.evalOne startingStateList


/--
  `NA.eval N cs` := Returns the final list of states that the nondeterministic automaton `N` transitions to if it starts at `N.startingStateList` and consumes the list of symbols `cs`.
-/
def NDA.eval
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (N : NDA α σ) :
  List α → List σ :=
  N.evalFrom N.startingStateList


def NDA.accepts
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (N : NDA α σ)
  (input : List α) :
  Prop :=
  ∃ (s : σ), s ∈ N.eval input ∧ s ∈ N.acceptingStateList


def NDA.wrapLeft
  {α : Type}
  [DecidableEq α]
  {σ_l : Type}
  [DecidableEq σ_l]
  (σ_r : Type)
  [DecidableEq σ_r]
  (e : NDA α σ_l) :
  NDA α (σ_l ⊕ σ_r) :=
  {
/-
    stateSet := e.stateSet.image Sum.inl
    symbolSet := e.symbolSet
-/
    stepList := e.stepList.map (fun (step : ((σ_l × Option α) × List σ_l)) => ((Sum.inl step.fst.fst, step.fst.snd), step.snd.map Sum.inl))
    startingStateList := e.startingStateList.map Sum.inl
    acceptingStateList := e.acceptingStateList.map Sum.inl
  }


def NDA.wrapRight
  {α : Type}
  [DecidableEq α]
  (σ_l : Type)
  [DecidableEq σ_l]
  {σ_r : Type}
  [DecidableEq σ_r]
  (e : NDA α σ_r) :
  NDA α (σ_l ⊕ σ_r) :=
  {
/-
    stateSet := e.stateSet.image Sum.inr
    symbolSet := e.symbolSet
-/
    stepList := e.stepList.map (fun (step : ((σ_r × Option α) × List σ_r)) => ((Sum.inr step.fst.fst, step.fst.snd), step.snd.map Sum.inr))
    startingStateList := e.startingStateList.map Sum.inr
    acceptingStateList := e.acceptingStateList.map Sum.inr
  }


def match_char_NDA
  {α : Type}
  [DecidableEq α]
  (c : α) :
  NDA α ℕ :=
  {
/-
    stateSet := {0, 1}
    symbolSet := {c}
-/
    stepList := [((0, Option.some c), [1])]
    startingStateList := [0]
    acceptingStateList := [1]
  }


example
  (α : Type)
  [DecidableEq α]
  (c : α)
  (x : α) :
  (match_char_NDA c).accepts [x] ↔ x = c :=
  by
  simp only [match_char_NDA]
  simp only [NDA.accepts]
  simp only [NDA.eval]
  simp only [NDA.evalFrom]
  simp
  simp only [NDA.evalOne]
  simp
  simp only [stepListToFun]
  simp only [stepListToFunAux]
  simp
  split
  case _ c1 =>
    simp
    exact c1
  case _ c1 =>
    simp
    exact c1


def match_epsilon_NDA
  (α : Type)
  [DecidableEq α] :
  NDA α ℕ :=
  {
/-
    stateSet := {0}
    symbolSet := {}
-/
    stepList := []
    startingStateList := [0]
    acceptingStateList := [0]
  }


example
  (α : Type)
  [DecidableEq α] :
  (match_epsilon_NDA α).accepts [] :=
  by
  simp only [match_epsilon_NDA]
  simp only [NDA.accepts]
  simp only [NDA.eval]
  simp only [NDA.evalFrom]
  simp


example
  (α : Type)
  [DecidableEq α]
  (c : α) :
  ¬ (match_epsilon_NDA α).accepts [c] :=
  by
  simp only [match_epsilon_NDA]
  simp only [NDA.accepts]
  simp only [NDA.eval]
  simp only [NDA.evalFrom]
  simp
  simp only [NDA.evalOne]
  simp
  simp only [stepListToFun]
  simp only [stepListToFunAux]
  simp


def match_zero_NDA
  (α : Type)
  [DecidableEq α] :
  NDA α ℕ :=
  {
/-
    stateSet := {0}
    symbolSet := {}
-/
    stepList := []
    startingStateList := [0]
    acceptingStateList := []
  }


def match_union_NDA
  (α : Type)
  [DecidableEq α]
  (σ_0 σ_1 : Type)
  [DecidableEq σ_0]
  [DecidableEq σ_1]
  (e1 : NDA α σ_0)
  (e2 : NDA α σ_1) :
  NDA α (ℕ ⊕ (σ_0 ⊕ σ_1)) :=
  -- The states of e1 need to be made disjoint from the states of e2. Therefore the states of e1 are made Sum.inl instances of (σ_0 ⊕ σ_1) and the states of e2 are made Sum.inr instances of (σ_0 ⊕ σ_1).
  let e1' : NDA α (σ_0 ⊕ σ_1) := e1.wrapLeft σ_1
  let e2' : NDA α (σ_0 ⊕ σ_1) := e2.wrapRight σ_0

  -- The new NDA needs to have a new starting state that is disjoint from the states of e1' and e2'. Therefore it is made a Sum.inl instance of (ℕ ⊕ (σ_0 ⊕ σ_1)) and the states of e1' and e2' are made Sum.inr instances of (ℕ ⊕ (σ_0 ⊕ σ_1)).
  let e1'' : NDA α (ℕ ⊕ (σ_0 ⊕ σ_1)) := e1'.wrapRight ℕ
  let e2'' : NDA α (ℕ ⊕ (σ_0 ⊕ σ_1)) := e2'.wrapRight ℕ

  let new_starting_state : ℕ ⊕ (σ_0 ⊕ σ_1) := Sum.inl 0

  -- A step on epsilon (represented as Option.none) from the new starting state to both the starting state of e1'' and the starting state of e2''.
  let new_starting_step : ((ℕ ⊕ (σ_0 ⊕ σ_1)) × Option α) × List (ℕ ⊕ (σ_0 ⊕ σ_1)) := ((new_starting_state, Option.none), List.dedup (e1''.startingStateList ++ e2''.startingStateList))

  {
/-
    stateSet := {new_starting_state} ∪ e1''.stateSet ∪ e2''.stateSet
    symbolSet := e1''.symbolSet ∪ e2''.symbolSet
-/
    stepList := new_starting_step :: e1''.stepList ++ e2''.stepList
    startingStateList := [new_starting_state]
    acceptingStateList := List.dedup (e1''.acceptingStateList ++ e2''.acceptingStateList)
  }


def match_concat_NDA
  (α : Type)
  [DecidableEq α]
  (σ_0 σ_1 : Type)
  [DecidableEq σ_0]
  [DecidableEq σ_1]
  (e1 : NDA α σ_0)
  (e2 : NDA α σ_1) :
  NDA α (σ_0 ⊕ σ_1) :=
  let e1' : NDA α (σ_0 ⊕ σ_1) := e1.wrapLeft σ_1
  let e2' : NDA α (σ_0 ⊕ σ_1) := e2.wrapRight σ_0
  {
/-
    stateSet := e1'.stateSet ∪ e2'.stateSet
    symbolSet := e1'.symbolSet ∪ e2'.symbolSet
-/
    -- Steps on epsilon from each of the accepting states of e1' to the starting state of e2'.
    stepList := e1'.acceptingStateList.map (fun (state : σ_0 ⊕ σ_1) => ((state, Option.none), e2'.startingStateList))

    startingStateList := e1'.startingStateList
    acceptingStateList := e2'.acceptingStateList
  }


def match_closure_NDA
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ]
  (e : NDA α σ) :
  NDA α (ℕ ⊕ σ) :=

  let e' : NDA α (ℕ ⊕ σ) := e.wrapRight ℕ

  let new_starting_state : ℕ ⊕ σ := Sum.inl 0

  -- A step on epsilon from the new starting state to the starting state of e'.
  let new_starting_step : ((ℕ ⊕ σ) × Option α) × List (ℕ ⊕ σ) := ((new_starting_state, Option.none), e'.startingStateList)

  -- Steps on epsilon from each of the accepting states of e' to the new starting state.
  let new_step_list := e'.acceptingStateList.map (fun (state : ℕ ⊕ σ) => ((state, Option.none), [new_starting_state]))

  {
/-
    stateSet := {new_starting_state} ∪ e'.stateSet
    symbolSet := e'.symbolSet
-/
    stepList := new_starting_step :: new_step_list
    startingStateList := [new_starting_state]
    acceptingStateList := new_starting_state :: e'.acceptingStateList
  }


end RegExpToNDA

-----

-- Take the set of strings in S that start with u and then remove the u from them.

/--
  The Brzozowski derivative u^{-1}S of a set S of strings and a string u is the set of all strings obtainable from a string in S by cutting off the prefix u.
-/
def Brzozowski_derivative
  (S : Set (String))
  (u : String) :
  Set String :=
  { v : String | u ++ v ∈ S }


/-
The derivative, D_a(r) of a regular expression r by alphabet letter a is defined as D_a(r) = {w : aw ∈ r}. The derivative represents the set of continuations after letter a that the regular expression r can match.
-/


def RegExp.delta
  {α : Type} :
  RegExp α → RegExp α
  | char _ => RegExp.zero
  | epsilon => RegExp.epsilon
  | zero => RegExp.zero
  | union r s => RegExp.union r.delta s.delta
  | concat r s => RegExp.concat r.delta s.delta
  | closure _ => RegExp.epsilon


def RegExp.Brzozowski_derivative_set
  {α : Type}
  [DecidableEq α]
  (r : RegExp α)
  (a : α) :
  Set (List α) :=
  {w : List α | (a :: w) ∈ r.languageOf}


def RegExp.Brzozowski_derivative
  {α : Type}
  [DecidableEq α]
  (a : α) :
  RegExp α → RegExp α
  | char b => if a = b then RegExp.epsilon else RegExp.zero
  | epsilon => RegExp.zero
  | zero => RegExp.zero
  | union r s => RegExp.union (r.Brzozowski_derivative a) (s.Brzozowski_derivative a)
  | concat r s => RegExp.union (RegExp.concat (r.Brzozowski_derivative a) s) (RegExp.concat r.delta (s.Brzozowski_derivative a))
  | closure r => RegExp.concat (r.Brzozowski_derivative a) r.closure


example
  {α : Type}
  [DecidableEq α]
  (r : RegExp α)
  (a : α) :
  RegExp.Brzozowski_derivative_set r a = (r.Brzozowski_derivative a).languageOf :=
  by
  ext cs
  induction r
  case char a b =>
    simp only [RegExp.Brzozowski_derivative_set]
    simp only [RegExp.Brzozowski_derivative]
    split_ifs
    case pos c1 =>
      simp only [RegExp.languageOf]
      simp
      intro _
      exact c1
    case neg c1 =>
      simp only [RegExp.languageOf]
      simp
      intro contra
      contradiction
  case epsilon =>
    simp only [RegExp.Brzozowski_derivative_set]
    simp only [RegExp.Brzozowski_derivative]
    simp only [RegExp.languageOf]
    simp
  case zero =>
    simp only [RegExp.Brzozowski_derivative_set]
    simp only [RegExp.Brzozowski_derivative]
    simp only [RegExp.languageOf]
    simp
  case union r s r_ih s_ih =>
    simp only [RegExp.languageOf]
    simp
    simp only [← r_ih]
    simp only [← s_ih]
    simp only [RegExp.Brzozowski_derivative_set]
    simp only [RegExp.languageOf]
    simp
  case concat r s r_ih s_ih =>
    simp only [RegExp.Brzozowski_derivative_set] at r_ih
    simp at r_ih

    simp only [RegExp.Brzozowski_derivative_set] at s_ih
    simp at s_ih

    simp only [RegExp.Brzozowski_derivative_set]
    simp

    simp only [RegExp.Brzozowski_derivative]

    simp only [RegExp.languageOf]
    simp

    constructor
    · intro a1
      apply Exists.elim a1
      intro r' a2
      clear a1
      cases a2
      case _ a2_left a2_right =>
        apply Exists.elim a2_right
        intro s' a3
        clear a2_right
        cases a3
        case _ a3_left a3_right =>
          sorry
    · intro a1
      cases a1
      case _ a1_left =>
        apply Exists.elim a1_left
        intro r' a2
        clear a1_left
        cases a2
        case _ a2_left a2_right =>
          apply Exists.elim a2_right
          intro s' a3
          clear a2_right
          cases a3
          case _ a3_left a3_right =>
            sorry
      case _ a1_right =>
        sorry
  case closure r r_ih =>
    simp only [RegExp.Brzozowski_derivative_set] at r_ih
    simp at r_ih

    simp only [RegExp.Brzozowski_derivative_set]
    simp only [RegExp.Brzozowski_derivative]
    simp only [RegExp.languageOf]
    simp
    constructor
    · intro a1
      apply Exists.elim a1
      intro rs a2
      clear a1
      cases a2
      case _ a2_left a2_right =>
        simp only [← a2_right] at r_ih
        cases r_ih
        case _ mp mpr =>
          cases rs
          case nil =>
            simp at a2_right
          case cons hd tl =>
            simp at a2_left
            cases a2_left
            case _ a2_left_left a2_left_right =>
              simp at a2_right
              apply Exists.intro cs
              sorry
    · sorry

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
