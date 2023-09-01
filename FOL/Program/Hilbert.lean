import Mathlib.Data.Finset.Basic

set_option autoImplicit false


def LF : Char := Char.ofNat 10


inductive Formula : Type
  | var_ : String → Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  deriving Inhabited, DecidableEq

open Formula

def Formula.toString : Formula → String
  | var_ phi => phi
  | not_ phi => s! "¬ {phi.toString}"
  | imp_ phi psi => s! "({phi.toString} → {psi.toString})"

instance : ToString Formula :=
  { toString := fun x => x.toString }

instance : Repr Formula :=
  { reprPrec := fun x _ => x.toString.toFormat }


inductive DerivationStep : Type
  | thin : List Formula → String → DerivationStep
  | assume : Formula → DerivationStep
  | prop_1 : Formula → Formula → DerivationStep
  | prop_2 : Formula → Formula → Formula → DerivationStep
  | prop_3 : Formula → Formula → DerivationStep
  | mp : String → String → DerivationStep

open DerivationStep

def DerivationStep.toString : DerivationStep → String
  | thin delta local_label => s! "thin {delta} {local_label}"
  | assume phi => s! "assume {phi}"
  | prop_1 phi psi => s! "prop_1 {phi} {psi}"
  | prop_2 phi psi chi => s! "prop_2 {phi} {psi} {chi}"
  | prop_3 phi psi => s! "prop_3 {phi} {psi}"
  | mp local_major_label local_minor_label => s! "mp {local_major_label} {local_minor_label}"

instance : ToString DerivationStep :=
  { toString := fun x => x.toString }

instance : Repr DerivationStep :=
  { reprPrec := fun x _ => x.toString.toFormat }


structure labeledDerivationStep : Type :=
  (label : String)
  (step : DerivationStep)

def labeledDerivationStep.toString (x : labeledDerivationStep) : String :=
  s! "{x.label} : {x.step}"

instance : ToString labeledDerivationStep :=
  { toString := fun x => x.toString }

instance : Repr labeledDerivationStep :=
  { reprPrec := fun x _ => x.toString.toFormat }


structure Judgement : Type :=
  (assumptions : List Formula)
  (conclusion : Formula)

def Judgement.toString (x : Judgement) : String :=
  s! "{x.assumptions} ⊢ {x.conclusion}"

instance : ToString Judgement :=
  { toString := fun x => x.toString }

instance : Repr Judgement :=
  { reprPrec := fun x _ => x.toString.toFormat }


structure labeledJudgement : Type :=
  (label : String)
  (judgement : Judgement)

def labeledJudgement.toString (x : labeledJudgement) : String :=
  s! "{x.label} : {x.judgement}"

instance : ToString labeledJudgement :=
  { toString := fun x => x.toString }

instance : Repr labeledJudgement :=
  { reprPrec := fun x _ => x.toString.toFormat }


def Context : Type := List labeledJudgement

def Context.toString : Context → String
  | [] => ""
  | hd :: tl => s! "{Context.toString tl}{LF}{hd}"

instance : ToString Context :=
  { toString := fun x => x.toString }

instance : Repr Context :=
  { reprPrec := fun x _ => x.toString.toFormat }


def Context.find
  (context : Context)
  (label : String) :
  Except String Judgement :=
  if let Option.some val := context.find? (fun val => val.label = label)
  then Except.ok val.judgement
  else Except.error s!"{label} not found in context."


def checkDerivationStep
  (global_context : Context)
  (local_context : Context) :
  DerivationStep → Except String Judgement

  | thin delta local_label => do
    let judgement ← local_context.find local_label
    Except.ok {
      assumptions := delta ++ judgement.assumptions
      conclusion := judgement.conclusion
    }

  | assume phi =>
    Except.ok {
      assumptions := [phi]
      conclusion := phi }

  | prop_1 phi psi =>
      Except.ok {
        assumptions := []
        conclusion := (phi.imp_ (psi.imp_ phi)) }

  | prop_2 phi psi chi =>
      Except.ok {
        assumptions := []
        conclusion := ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi))) }

  | prop_3 phi psi =>
      Except.ok {
        assumptions := []
        conclusion := (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi)) }

  | mp local_major_label local_minor_label => do
    let major ← local_context.find local_major_label
    let minor ← local_context.find local_minor_label
    if major.assumptions.toFinset = minor.assumptions.toFinset
    then
      if let imp_ major_conclusion_antecedent major_conclusion_consequent := major.conclusion
      then
        if minor.conclusion = major_conclusion_antecedent
        then Except.ok {
          assumptions := major.assumptions
          conclusion := major_conclusion_consequent
        }
        else Except.error s! "major judgement : {local_major_label} : {major}{LF}minor judgement : {local_minor_label} : {minor}{LF}The conclusion of the minor judgement must match the antecedent of the conclusion of the major judgement."
      else Except.error s! "major judgement : {local_major_label} : {major}{LF}The conclusion of the major judgement must be an implication."
    else Except.error s! "major judgement : {local_major_label} : {major}{LF}minor judgement : {local_minor_label} : {minor}{LF}The assumptions of the minor judgement must match the assumptions of the major judgement."


def checkDerivationStepListAux
  (global_context : Context)
  (local_context : Context) :
  List labeledDerivationStep → Except String Context
  | [] => Except.ok local_context
  | hd :: tl =>
    match checkDerivationStep global_context local_context hd.step with
    | Except.ok judgement =>
        checkDerivationStepListAux
          global_context
          (
            {
              label := hd.label
              judgement := judgement
            } :: local_context
          )
          tl
    | Except.error message => Except.error s! "Global Context{LF}{global_context}{LF}-----{LF}Local Context{local_context}{LF}-----{LF}Error{LF}{hd}{LF}{message}"

def checkDerivationStepList
  (global_context : Context)
  (xs : List labeledDerivationStep) :
  Except String Context :=
  checkDerivationStepListAux global_context [] xs


def ExceptToString : Except String Context → String
  | Except.ok local_context => local_context.toString
  | Except.error E => E


#eval IO.print (
  ExceptToString (
    checkDerivationStepList [] [
      ⟨ "s1", (prop_2 (Formula.var_ "P") (Formula.imp_ (Formula.var_ "P") (Formula.var_ "P")) (Formula.var_ "P")) ⟩,

      ⟨ "s2", (prop_1 (Formula.var_ "P") (Formula.imp_ (Formula.var_ "P") (Formula.var_ "P"))) ⟩,

      ⟨ "s3", (mp "s1" "s2") ⟩,

      ⟨ "s4", (prop_1 (Formula.var_ "P") (Formula.var_ "P")) ⟩,

      ⟨ "s5", (mp "s3" "s4") ⟩ 
    ]
  )
)
