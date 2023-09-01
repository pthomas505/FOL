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
  | thin : ℕ → List Formula → Justification
  | assume : Formula → Justification
  | prop_1 : Formula → Formula → Justification
  | prop_2 : Formula → Formula → Formula → Justification
  | prop_3 : Formula → Formula → Justification
  | mp : ℕ → ℕ → Justification

open Justification


def compileJustification
  (globalContext : List Sequent)
  (localContext : List Sequent) :
  Justification → Option Sequent

  | thin index hypotheses => do
    let sequent ← localContext.get? index
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

  | mp major_index minor_index => do
    let major ← localContext.get? major_index
    let minor ← localContext.get? minor_index
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

def checkStep
  (globalContext : List Sequent)
  (localContext : List Sequent)
  (step : Step) :
  Bool :=
  if let Option.some sequent := compileJustification globalContext localContext step.justification
  then
    if sequent = step.assertion
    then true
    else false
  else false


def compileStepListAux
  (globalContext : List Sequent)
  (localContext : List Sequent) :
  List Step → Option (List Sequent)
  | [] => Option.some localContext
  | hd :: tl =>
    if checkStep globalContext localContext hd
    then compileStepListAux globalContext (localContext ++ [hd.assertion]) tl
    else Option.none

def compileStepList
  (globalContext : List Sequent)
  (xs : List Step) :
  Option (List Sequent) :=
  compileStepListAux globalContext [] xs


structure Proof : Type :=
  (assertion : Sequent)
  (steps : List Step)

def checkProof
  (globalContext : List Sequent)
  (x : Proof) :
  Bool :=
  if let Option.some sequent_list := compileStepList globalContext x.steps
  then
    if let Option.some sequent := sequent_list.getLast?
    then
      if sequent = x.assertion
      then true
      else false
    else false
  else false


def compileProofListAux
  (globalContext : List Sequent) :
  List Proof → Option (List Sequent)
  | [] => globalContext
  | hd :: tl =>
    if checkProof globalContext hd
    then compileProofListAux (globalContext ++ [hd.assertion]) tl
    else Option.none

def compileProofList
  (xs : List Proof) :
  Option (List Sequent) :=
  compileProofListAux [] xs

