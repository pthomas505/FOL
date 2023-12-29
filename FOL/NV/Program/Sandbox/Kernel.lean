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


inductive Justification : Type
  | thin : String → List Formula → Justification
  | assume : Formula → Justification
  | prop_1 : Formula → Formula → Justification
  | prop_2 : Formula → Formula → Formula → Justification
  | prop_3 : Formula → Formula → Justification
  | mp : String → String → Justification

open Justification


structure Step : Type :=
  (label : String)
  (assertion : Sequent)
  (justification : Justification)


structure Proof : Type :=
  (label : String)
  (assertion : Sequent)
  (steps : List Step)


def Context.find
  (context : List Step)
  (label : String) :
  Option Step :=
  if let Option.some x := context.find? (fun x => x.label = label)
  then Option.some x
  else Option.none


def justificationToSequent
  (globalContext : List Proof)
  (localContext : List Step) :
  Justification → Option Sequent

  | thin label hypotheses => do
    let step ← Context.find localContext label
    Option.some {
      hypotheses := step.assertion.hypotheses ++ hypotheses
      conclusion := step.assertion.conclusion }

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
    if major.assertion.hypotheses.toFinset = minor.assertion.hypotheses.toFinset
    then
      if let imp_ major_conclusion_antecedent major_conclusion_consequent := major.assertion.conclusion
      then
        if minor.assertion.conclusion = major_conclusion_antecedent
        then Option.some {
          hypotheses := major.assertion.hypotheses
          conclusion := major_conclusion_consequent }
        else Option.none
      else Option.none
    else Option.none


def checkStep
  (globalContext : List Proof)
  (localContext : List Step)
  (step : Step) :
  Bool :=
  if let Option.some sequent := justificationToSequent globalContext localContext step.justification
  then sequent = step.assertion
  else false

def checkStepListAux
  (globalContext : List Proof)
  (localContext : List Step) :
  List Step → Bool
  | [] => true
  | hd :: tl =>
    if checkStep globalContext localContext hd
    then checkStepListAux globalContext (localContext ++ [hd]) tl
    else false

def checkStepList
  (globalContext : List Proof)
  (steps : List Step) :
  Bool :=
  checkStepListAux globalContext [] steps


def checkProof
  (globalContext : List Proof)
  (proof : Proof) :
  Bool :=
  if checkStepList globalContext proof.steps
  then
    if let Option.some step := List.getLast? proof.steps
    then step.assertion = proof.assertion
    else false
  else false

def checkProofListAux
  (globalContext : List Proof) :
  List Proof → Bool
  | [] => true
  | hd :: tl =>
    if checkProof globalContext hd
    then checkProofListAux (globalContext ++ [hd]) tl
    else false

def checkProofList
  (proofs : List Proof) :
  Bool :=
  checkProofListAux [] proofs
