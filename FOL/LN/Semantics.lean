import FOL.LN.Formula

set_option autoImplicit false


namespace LN

open Var Formula


structure Interpretation (D : Type) : Type where
  (nonempty_ : Nonempty D)
  (pred_ : String → (List D → Prop))


def Interpretation.usingPred
  (D : Type)
  (I : Interpretation D)
  (pred_ : String → List D → Prop) :
  Interpretation D := {
    nonempty_ := I.nonempty_
    pred_ := pred_ }


def VarAssignment (D : Type) : Type := Var → D


def shift
  (D : Type)
  (V : VarAssignment D)
  (d : D) :
  VarAssignment D
  | free_ x => V (free_ x)
  | bound_ 0 => d
  | bound_ (i + 1) => V (bound_ i)


def shiftList
  (D : Type)
  (V : VarAssignment D) :
  List D → VarAssignment D
  | [] => V
  | d :: ds => shift D (shiftList D V ds) d


def Holds
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D) :
  Formula → Prop
  | pred_ X vs => I.pred_ X (vs.map V)
  | not_ phi => ¬ Holds D I V phi
  | imp_ phi psi => Holds D I V phi → Holds D I V psi
  | forall_ _ phi => ∀ (d : D), Holds D I (shift D V d) phi


def Formula.isValid (F : Formula) : Prop :=
  ∀ (D : Type) (I : Interpretation D) (V : VarAssignment D), Holds D I V F
