import Mathlib.Data.Finset.Basic

set_option autoImplicit false


abbrev eol := '\n'

inductive Formula : Type
| var_ : String → Formula
| not_ : Formula → Formula
| imp_ : Formula → Formula → Formula
deriving Inhabited, DecidableEq

open Formula

def Formula.toString : Formula → String
| var_ phi => phi
| not_ phi => s! "(¬ {phi.toString})"
| imp_ phi psi => s! "({phi.toString} → {psi.toString})"

instance : ToString Formula :=
  { toString := fun x => x.toString }

instance : Repr Formula :=
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


inductive Step : Type
| structural_1 : Formula → String → Step
| assumption : Formula → Step
| ax_1 : List Formula → Formula → Formula → Step
| ax_2 : List Formula → Formula → Formula → Formula → Step
| ax_3 : List Formula → Formula → Formula → Step
| mp : String → String → Step

open Step

def Step.toString : Step → String
| structural_1 H label => s! "structural_1 {H} {label}"
| assumption H => s! "assumption {H}"
| ax_1 delta phi psi => s! "ax_1 {delta} {phi} {psi}"
| ax_2 delta phi psi chi => s! "ax_2 {delta} {phi} {psi} {chi}"
| ax_3 delta phi psi => s! "ax_3 {delta} {phi} {psi}"
| mp major_label minor_label => s! "mp {major_label} {minor_label}"

instance : ToString Step :=
  { toString := fun x => x.toString }

instance : Repr Step :=
  { reprPrec := fun x _ => x.toString.toFormat }


structure labeledStep : Type :=
(label : String)
(step : Step)

def labeledStep.toString (x : labeledStep) : String :=
  s! "{x.label} : {x.step}"

instance : ToString labeledStep :=
  { toString := fun x => x.toString }

instance : Repr labeledStep :=
  { reprPrec := fun x _ => x.toString.toFormat }


def Context : Type := List labeledJudgement

def Context.toString : Context → String
| [] => ""
| hd :: tl => s! "{Context.toString tl}{eol}{hd}"

instance : ToString Context :=
  { toString := fun x => x.toString }

instance : Repr Context :=
  { reprPrec := fun x _ => x.toString.toFormat }


def Context.find
  (gamma : Context)
  (label : String) :
  Except String Judgement :=
  if let Option.some val := gamma.find? (fun val => val.label = label)
  then Except.ok val.judgement
  else Except.error s!"{label} not found in context."


def checkStep (gamma : Context) : Step → Except String Judgement

| structural_1 H label => do
  let judgement ← gamma.find label
  Except.ok {
    assumptions := H :: judgement.assumptions
    conclusion := judgement.conclusion
  }

| assumption H =>
  Except.ok {
    assumptions := [H]
    conclusion := H }

| ax_1 delta phi psi =>
    Except.ok {
      assumptions := delta
      conclusion := (phi.imp_ (psi.imp_ phi)) }

| ax_2 delta phi psi chi =>
    Except.ok {
      assumptions := delta
      conclusion := ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi))) }

| ax_3 delta phi psi =>
    Except.ok {
      assumptions := delta
      conclusion := (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi)) }

| mp major_label minor_label => do
  let major ← gamma.find major_label
  let minor ← gamma.find minor_label
  if major.assumptions.toFinset = minor.assumptions.toFinset
  then
    if let imp_ major_conclusion_antecedent major_conclusion_consequent := major.conclusion
    then
      if minor.conclusion = major_conclusion_antecedent
      then Except.ok {
        assumptions := major.assumptions
        conclusion := major_conclusion_consequent
      }
      else Except.error s! "major judgement : {major_label} : {major}{eol}minor judgement : {minor_label} : {minor}{eol}The conclusion of the minor judgement must match the antecedent of the conclusion of the major judgement."
    else Except.error s! "major judgement : {major_label} : {major}{eol}The conclusion of the major judgement must be an implication."
  else Except.error s! "major judgement : {major_label} : {major}{eol}minor judgement : {minor_label} : {minor}{eol}The assumptions of the minor judgement must match the assumptions of the major judgement."


def checkStepListAux
  (gamma : Context) :
  List labeledStep → Except String Context
| [] => Except.ok gamma
| hd :: tl =>
  match checkStep gamma hd.step with
  | Except.ok judgement => checkStepListAux (
    { label := hd.label
      judgement := judgement } :: gamma) tl
  | Except.error message => Except.error s! "Error{eol}{gamma}{eol}-----{eol}{hd}{eol}{message}"

def checkStepList
  (xs : List labeledStep) :
  Except String Context :=
  checkStepListAux [] xs


def unfoldExcept : Except String Context → String
| Except.ok gamma => gamma.toString
| Except.error E => E


#eval IO.print (
  unfoldExcept (
    checkStepList [
      ⟨ "s1", (ax_2 [] (Formula.var_ "P") (Formula.imp_ (Formula.var_ "P") (Formula.var_ "P")) (Formula.var_ "P")) ⟩,

      ⟨ "s2", (ax_1 [] (Formula.var_ "P") (Formula.imp_ (Formula.var_ "P") (Formula.var_ "P"))) ⟩,

      ⟨ "s3", (mp "s1" "s2") ⟩,

      ⟨ "s4", (assumption (Formula.var_ "H")) ⟩
    ]
  )
)
