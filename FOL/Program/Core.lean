import Mathlib.Data.Finset.Basic

set_option autoImplicit false


inductive Formula : Type
  | var_ : String → Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  deriving Inhabited, DecidableEq

open Formula


structure Sequent : Type :=
  (hypotheses : List Formula)
  (conclusion : Formula)
  deriving Inhabited, DecidableEq

structure LabeledSequent : Type :=
  (label : String)
  (sequent : Sequent)


inductive Justification : Type
  | thin : String → List Formula → Justification
  | assume : Formula → Justification
  | prop_1 : Formula → Formula → Justification
  | prop_2 : Formula → Formula → Formula → Justification
  | prop_3 : Formula → Formula → Justification
  | mp : String → String → Justification

open Justification


def Context.find
  (context : List LabeledSequent)
  (label : String) :
  Option Sequent :=
  if let Option.some val := context.find? (fun val => val.label = label)
  then Option.some val.sequent
  else Option.none


def compileJustificationToSequent
  (globalContext : List LabeledSequent)
  (localContext : List LabeledSequent) :
  Justification → Option Sequent

  | thin label hypotheses => do
    let sequent ← Context.find localContext label
    Option.some {
      hypotheses := sequent.hypotheses ++ hypotheses
      conclusion := sequent.conclusion }

  | assume phi =>
    Option.some {
      hypotheses := [phi],
      conclusion := phi }

  | prop_1 phi psi =>
    Option.some {
      hypotheses := [],
      conclusion := (phi.imp_ (psi.imp_ phi)) }

  | prop_2 phi psi chi =>
    Option.some {
      hypotheses := []
      conclusion := ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi))) }

  | prop_3 phi psi =>
    Option.some {
      hypotheses := []
      conclusion := (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi))
    }

  | mp major_label minor_label => do
    let major ← Context.find localContext major_label
    let minor ← Context.find localContext minor_label
    if major.hypotheses.toFinset = minor.hypotheses.toFinset
    then
      if let imp_ major_conclusion_antecedent major_conclusion_consequent := major.conclusion
      then
        if minor.conclusion = major_conclusion_antecedent
        then Option.some {
          hypotheses := major.hypotheses
          conclusion := major_conclusion_consequent }
        else Option.none
      else Option.none
    else Option.none


structure Step : Type :=
  (assertion : Sequent)
  (justification : Justification)

structure LabeledStep : Type :=
  (label : String)
  (step : Step)


def checkStep
  (globalContext : List LabeledSequent)
  (localContext : List LabeledSequent)
  (step : Step) :
  Bool :=
  if let Option.some sequent := compileJustificationToSequent globalContext localContext step.justification
  then
    if sequent = step.assertion
    then true
    else false
  else false


def compileLabeledStepListToLabledSequentListAux
  (globalContext : List LabeledSequent)
  (localContext : List LabeledSequent) :
  List LabeledStep → Option (List LabeledSequent)
  | [] => Option.some localContext
  | hd :: tl =>
    if checkStep globalContext localContext hd.step
    then compileLabeledStepListToLabledSequentListAux globalContext (localContext ++ [{label := hd.label, sequent := hd.step.assertion}]) tl
    else Option.none

def compileLabeledStepListToLabeledSequentList
  (globalContext : List LabeledSequent)
  (steps : List LabeledStep) :
  Option (List LabeledSequent) :=
  compileLabeledStepListToLabledSequentListAux globalContext [] steps


structure Proof : Type :=
  (assertion : Sequent)
  (steps : List LabeledStep)

structure LabeledProof : Type :=
  (label : String)
  (proof : Proof)

def checkProof
  (globalContext : List LabeledSequent)
  (proof : Proof) :
  Bool :=
  if let Option.some xs := compileLabeledStepListToLabeledSequentList globalContext proof.steps
  then
    if let Option.some labeledSequent := xs.getLast?
    then
      if labeledSequent.sequent = proof.assertion
      then true
      else false
    else false
  else false


def compileLabeledProofListToLabledSequentListAux
  (globalContext : List LabeledSequent) :
  List LabeledProof → Option (List LabeledSequent)
  | [] => globalContext
  | hd :: tl =>
    if checkProof globalContext hd.proof
    then compileLabeledProofListToLabledSequentListAux (globalContext ++ [{label := hd.label, sequent := hd.proof.assertion}]) tl
    else Option.none

def compileLabeledProofListToLabledSequentList
  (proofs : List LabeledProof) :
  Option (List LabeledSequent) :=
  compileLabeledProofListToLabledSequentListAux [] proofs
