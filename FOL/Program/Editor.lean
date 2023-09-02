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


structure Sequent : Type :=
  (hypotheses : List Formula)
  (conclusion : Formula)
  deriving Inhabited, DecidableEq

def Sequent.toString (x : Sequent) : String :=
  s! "{x.hypotheses} ⊢ {x.conclusion}"

instance : ToString Sequent :=
  { toString := fun x => x.toString }


inductive Justification : Type
  | thin : String → List Formula → Justification
  | assume : Formula → Justification
  | prop_1 : Formula → Formula → Justification
  | prop_2 : Formula → Formula → Formula → Justification
  | prop_3 : Formula → Formula → Justification
  | mp : String → String → Justification
  | thm : String → Justification

open Justification

def Justification.toString : Justification → String
  | thin label hypotheses => s! "thin {label} {hypotheses}"
  | assume hypothesis => s! "assume {hypothesis}"
  | prop_1 phi psi => s! "prop_1 {phi} {psi}"
  | prop_2 phi psi chi => s! "prop_2 {phi} {psi} {chi}"
  | prop_3 phi psi => s! "prop_3 {phi} {psi}"
  | mp major_label minor_label => s! "mp {major_label} {minor_label}"
  | thm label => s! "thm {label}"

instance : ToString Justification :=
  { toString := fun x => x.toString }


structure Step : Type :=
  (label : String)
  (assertion : Sequent)
  (justification : Justification)

def Step.toString (x : Step) : String :=
  s! "{x.label} : {x.assertion} : {x.justification}"

instance : ToString Step :=
  { toString := fun x => x.toString }


structure Proof : Type :=
  (label : String)
  (assertion : Sequent)
  (steps : List Step)

def Proof.toString (x : Proof) : String :=
  s! "{x.label} {x.assertion}"

instance : ToString Proof :=
  { toString := fun x => x.toString }


abbrev GlobalContext : Type := List Proof

abbrev LocalContext : Type := List Step

def GlobalContext.find
  (context : GlobalContext)
  (label : String) :
  Except String Proof :=
  if let Option.some x := context.find? (fun x => x.label = label)
  then Except.ok x
  else Except.error s! "{label} not found in global context."

def LocalContext.find
  (context : LocalContext)
  (label : String) :
  Except String Step :=
  if let Option.some x := context.find? (fun x => x.label = label)
  then Except.ok x
  else Except.error s! "{label} not found in local context."

def LocalContext.getLast
  (context : LocalContext) :
  Except String Step :=
  if let Option.some x := context.getLast?
  then Except.ok x
  else Except.error s! "The local context is empty."


def justificationToSequent
  (globalContext : GlobalContext)
  (localContext : LocalContext) :
  Justification → Except String Sequent

  | thin label hypotheses => do
    let step ← localContext.find label
    Except.ok {
      hypotheses := step.assertion.hypotheses ++ hypotheses
      conclusion := step.assertion.conclusion }

  | assume phi =>
    Except.ok {
      hypotheses := [phi],
      conclusion := phi }

  | prop_1 phi psi =>
    Except.ok {
      hypotheses := [],
      conclusion := (phi.imp_ (psi.imp_ phi)) }

  | prop_2 phi psi chi =>
    Except.ok {
      hypotheses := []
      conclusion := ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi))) }

  | prop_3 phi psi =>
    Except.ok {
      hypotheses := []
      conclusion := (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi)) }

  | mp major_label minor_label => do
    let major ← localContext.find major_label
    let minor ← localContext.find minor_label
    if major.assertion.hypotheses.toFinset = minor.assertion.hypotheses.toFinset
    then
      if let imp_ major_conclusion_antecedent major_conclusion_consequent := major.assertion.conclusion
      then
        if minor.assertion.conclusion = major_conclusion_antecedent
        then Except.ok {
          hypotheses := major.assertion.hypotheses
          conclusion := major_conclusion_consequent }
        else Except.error s! "major premise : {major}{LF}minor premise : {minor}{LF}The conclusion of the minor premise must match the antecedent of the conclusion of the major premise."
      else Except.error s! "major premise : {major}{LF}The conclusion of the major premise must be an implication."
    else Except.error s! "major premise : {major}{LF}minor premise : {minor}{LF}The hypotheses of the minor premise must match the hypotheses of the major premise."

  | thm label => do
    let proof ← globalContext.find label
    Except.ok proof.assertion

def createStep
  (globalContext : GlobalContext)
  (localContext : LocalContext)
  (label : String)
  (justification : Justification) :
  Except String Step := do
  let sequent ← justificationToSequent globalContext localContext justification
  Except.ok { label := label, assertion := sequent, justification := justification }


def createStepListAux
  (globalContext : GlobalContext)
  (localContext : LocalContext) :
  List (String × Justification) → Except String (List Step)
  | [] => Except.ok localContext
  | (label, justification) :: tl => do
    let step ← createStep globalContext localContext label justification
    createStepListAux globalContext (localContext ++ [step]) tl

def createStepList
  (globalContext : GlobalContext)
  (tactic_list : List (String × Justification)) :
  Except String (List Step) :=
  createStepListAux globalContext [] tactic_list


def createProof
  (globalContext : GlobalContext)
  (label : String)
  (tactic_list : List (String × Justification)) :
  Except String Proof := do
  let step_list ← createStepList globalContext tactic_list
  let step ← LocalContext.getLast step_list
  Except.ok {
    label := label
    assertion := step.assertion
    steps := step_list }


def createProofListAux
  (globalContext : GlobalContext) :
  List (String × (List (String × Justification))) → Except String (List Proof)
  | [] => Except.ok globalContext
  | hd :: tl => do
  let proof ← createProof globalContext hd.fst hd.snd
  createProofListAux (globalContext ++ [proof]) tl

def createProofList
  (tactic_list_list : List (String × (List (String × Justification)))) :
  Except String (List Proof) :=
  createProofListAux [] tactic_list_list


#eval createProofList []

#eval createProofList [
  ( "id", [
      ( "s1", (prop_2 (Formula.var_ "P") (Formula.imp_ (Formula.var_ "P") (Formula.var_ "P")) (Formula.var_ "P")) ),
      ( "s2", (prop_1 (Formula.var_ "P") (Formula.imp_ (Formula.var_ "P") (Formula.var_ "P"))) ),
      ( "s3", (mp "s1" "s2") ),
      ( "s4", (prop_1 (Formula.var_ "P") (Formula.var_ "P")) ),
      ( "s5", (mp "s3" "s4") )
    ]
  )
]
