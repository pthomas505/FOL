import Mathlib.Tactic
--import Mathlib.Order.Interval.Set.Basic

set_option autoImplicit false


/--
  Left-closed right-open interval
-/
structure Ico
  (α : Type)
  [Preorder α] :
  Type :=
  (min : α)
  (max : α)
  (min_lt_max : min < max)


def Ico.mem
  {α : Type}
  [Preorder α]
  (I : Ico α)
  (x : α) :
  Prop :=
  I.min <= x ∧ x < I.max

def Ico.lt
  {α : Type}
  [Preorder α]
  (I : Ico α)
  (x : α) :
  Prop :=
  I.max <= x

def Ico.gt
  {α : Type}
  [Preorder α]
  (I : Ico α)
  (x : α) :
  Prop :=
  x < I.min


/-
  I is less than x if and only if every member of I is less than x.
-/
example
  {α : Type}
  [Preorder α]
  [PredOrder α]
  [NoMinOrder α]
  (I : Ico α)
  (x : α) :
  I.lt x ↔ ∀ (y : α), I.mem y → y < x :=
  by
    simp only [Ico.lt]
    simp only [Ico.mem]
    constructor
    · intro a1 y a2
      cases a2
      case _ left right =>
        exact lt_of_lt_of_le right a1
    · intro a1
      apply Order.le_of_pred_lt
      apply a1
      constructor
      · exact PredOrder.le_pred_of_lt I.min_lt_max
      · exact Order.pred_lt I.max


/-
  I is greater than x if and only if every member of I is greater than x.
-/
example
  {α : Type}
  [Preorder α]
  (I : Ico α)
  (x : α) :
  I.gt x ↔ ∀ (y : α), I.mem y → x < y :=
  by
    simp only [Ico.gt]
    simp only [Ico.mem]
    constructor
    · intro a1 y a2
      cases a2
      case _ left right =>
        exact lt_of_lt_of_le a1 left
    · intro a1
      apply a1 I.min
      constructor
      · exact le_refl I.min
      · exact I.min_lt_max


example
  {α : Type}
  [LinearOrder α]
  (I J : Ico α) :
  (∃ (x : α), I.mem x ∧ J.mem x) ↔ J.min < I.max /\ I.min < J.max :=
  by
    simp only [Ico.mem]
    constructor
    · intro a1
      apply Exists.elim a1
      intro a a2
      clear a1
      cases a2
      case _ left right =>
        cases left
        case _ left_left left_right =>
          cases right
          case _ right_left right_right =>
            constructor
            · apply lt_of_le_of_lt right_left
              exact left_right
            · apply lt_of_le_of_lt left_left
              exact right_right
    · intro a1
      cases a1
      case _ left right =>
        by_cases c1 : I.min < J.min
        · apply Exists.intro J.min
          constructor
          · constructor
            · exact le_of_lt c1
            · exact left
          · constructor
            · exact Preorder.le_refl J.min
            · exact J.min_lt_max
        · apply Exists.intro I.min
          constructor
          · constructor
            · exact Preorder.le_refl I.min
            · exact I.min_lt_max
          · constructor
            · exact le_of_not_lt c1
            · exact right


inductive Color
  | Red : Color
  | Black : Color
  deriving Inhabited, DecidableEq

inductive RBTree : Type
  | leaf : RBTree
  | node : Color → RBTree → Int → RBTree → RBTree

  deriving Inhabited, DecidableEq
