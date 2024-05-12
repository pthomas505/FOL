import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Defs


structure Step
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ] :
  Type :=
  (beginState : σ)
  (symbol : α)
  (endStateList : List σ)
  deriving Repr


structure EpsilonStep
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ] :
  Type :=
  (beginState : σ)
  (endStateList : List σ)
  deriving Repr


structure NDFA
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ] :
  Type :=
  (stepList : List (Step α σ))
  (epsilonStepList : List (EpsilonStep α σ))
  (startingStateList : List σ)
  (acceptingStateList : List σ)
  deriving Repr
