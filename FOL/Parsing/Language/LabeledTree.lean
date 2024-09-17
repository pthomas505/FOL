import Mathlib.Data.Finset.Basic


set_option autoImplicit false


inductive LabeledTree (α : Type) : Type
  | mk
    (order : ℕ)
    (label : α)
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
  α :=
  match T with
  | mk _ label _ => label


def LabeledTree.children
  {α : Type}
  (T : LabeledTree α) :
  Fin T.order → LabeledTree α :=
  match T with
  | mk _ _ children => children


def LabeledTree.children_list
  {α : Type}
  (T : LabeledTree α) :
  List (LabeledTree α) :=
  List.ofFn (fun (i : Fin T.order) => (T.children i))


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
    if order = 0
    then [label]
    else (List.ofFn (fun (i : Fin order) => (children i).frontier)).join
