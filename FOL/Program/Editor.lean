import Mathlib.Data.Finset.Basic

set_option autoImplicit false


def LF : Char := Char.ofNat 10


inductive Formula : Type
  | var_ : String → Formula
  | true_ : Formula
  | false_ : Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  | and_ : Formula → Formula → Formula
  | or_ : Formula → Formula → Formula
  | iff_ : Formula → Formula → Formula
  deriving Inhabited, DecidableEq

open Formula

def Formula.toString : Formula → String
  | var_ phi => phi
  | true_ => "T"
  | false_ => "F"
  | not_ phi => s! "¬ {phi.toString}"
  | imp_ phi psi => s! "({phi.toString} → {psi.toString})"
  | and_ phi psi => s! "({phi.toString} ∧ {psi.toString})"
  | or_ phi psi => s! "({phi.toString} ∨ {psi.toString})"
  | iff_ phi psi => s! "({phi.toString} ↔ {psi.toString})"

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


def Function.updateIte
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (a' : α)
  (b : β)
  (a : α) :
  β :=
  if a = a' then b else f a

def Function.updateListIte
  {α β : Type}
  [DecidableEq α]
  (f : α → β) :
  List α → List β → α → β
  | x::xs, y::ys => Function.updateIte (Function.updateListIte f xs ys) x y
  | _, _ => f


def propSub
  (σ : String → String) :
  Formula → Formula
  | var_ v => var_ (σ v)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (propSub σ phi)
  | imp_ phi psi => imp_ (propSub σ phi) (propSub σ psi)
  | and_ phi psi => and_ (propSub σ phi) (propSub σ psi)
  | or_ phi psi => or_ (propSub σ phi) (propSub σ psi)
  | iff_ phi psi => iff_ (propSub σ phi) (propSub σ psi)


inductive Justification : Type
  | thin : String → List Formula → Justification
  | assume : Formula → Justification
  | prop_1 : Formula → Formula → Justification
  | prop_2 : Formula → Formula → Formula → Justification
  | prop_3 : Formula → Formula → Justification
  | mp : String → String → Justification
  | def_false : Justification
  | def_and : Formula → Formula → Justification
  | def_or : Formula → Formula → Justification
  | def_iff : Formula → Formula → Justification
  | thm : String → Justification
  | sub : String → List (String × String) → Justification

open Justification

def Justification.toString : Justification → String
  | thin label hypotheses => s! "thin {label} {hypotheses}"
  | assume hypothesis => s! "assume {hypothesis}"
  | prop_1 phi psi => s! "prop_1 {phi} {psi}"
  | prop_2 phi psi chi => s! "prop_2 {phi} {psi} {chi}"
  | prop_3 phi psi => s! "prop_3 {phi} {psi}"
  | mp major_label minor_label => s! "mp {major_label} {minor_label}"
  | def_false => s! "def_false"
  | def_and phi psi => s! "def_and {phi} {psi}"
  | def_or phi psi => s! "def_or {phi} {psi}"
  | def_iff phi psi => s! "def_iff {phi} {psi}"
  | thm label => s! "thm {label}"
  | sub label pairs => s! "sub {label} {pairs}"

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
  (steps : Array Step)

def Proof.toString (x : Proof) : String :=
  s! "{x.label} : {x.assertion} : {x.steps}"

instance : ToString Proof :=
  { toString := fun x => x.toString }


abbrev GlobalContext : Type := Std.HashMap String Proof

def GlobalContext.find
  (context : GlobalContext)
  (label : String) :
  Except String Proof :=
  if let Option.some x := context.find? label
  then Except.ok x
  else Except.error s! "{label} not found in global context."


abbrev LocalContext : Type := Std.HashMap String Step

def LocalContext.find
  (context : LocalContext)
  (label : String) :
  Except String Step :=
  if let Option.some x := context.find? label
  then Except.ok x
  else Except.error s! "{label} not found in local context."


def justificationToSequent
  (globalContext : GlobalContext)
  (localContext : LocalContext) :
  Justification → Except String Sequent

  | thin label hypotheses => do
      let step ← localContext.find label
      Except.ok {
        hypotheses := step.assertion.hypotheses ++ hypotheses
        conclusion := step.assertion.conclusion }

  | assume phi => Except.ok {
      hypotheses := [phi],
      conclusion := phi }

  | prop_1 phi psi => Except.ok {
      hypotheses := [],
      conclusion := (phi.imp_ (psi.imp_ phi)) }

  | prop_2 phi psi chi => Except.ok {
      hypotheses := []
      conclusion := ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi))) }

  | prop_3 phi psi => Except.ok {
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
          else Except.error s! "mp :{LF}major premise : {major}{LF}minor premise : {minor}{LF}The conclusion of the minor premise must match the antecedent of the conclusion of the major premise."
        else Except.error s! "mp :{LF}major premise : {major}{LF}The conclusion of the major premise must be an implication."
      else Except.error s! "mp :{LF}major premise : {major}{LF}minor premise : {minor}{LF}The hypotheses of the minor premise must match the hypotheses of the major premise."

  | def_false => Except.ok {
      hypotheses := []
      conclusion := false_.iff_ (not_ true_) }

  | def_and phi psi => Except.ok {
      hypotheses := []
      conclusion := ((phi.and_ psi).iff_ (not_ (phi.imp_ (not_ psi)))) }

  | def_or phi psi => Except.ok {
      hypotheses := []
      conclusion := ((phi.or_ psi).iff_ ((not_ phi).imp_ psi)) }

  | def_iff phi psi => Except.ok {
      hypotheses := []
      conclusion := (not_ (((phi.iff_ psi).imp_ (not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi))))).imp_ (not_ ((not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi)))).imp_ (phi.iff_ psi))))) }

  | thm label => do
      let proof ← globalContext.find label
      Except.ok proof.assertion

  | sub label pairs => do
      let step ← localContext.find label
      let (xs, ys) := List.unzip pairs
      Except.ok {
        hypotheses := step.assertion.hypotheses.map (propSub (Function.updateListIte id xs ys))
        conclusion := propSub (Function.updateListIte id xs ys) step.assertion.conclusion
      }


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
  (localContext : LocalContext)
  (acc : Array Step) :
  List (String × Justification) → Except String (Array Step)
  | [] => Except.ok acc
  | (label, justification) :: tl => do
    let step ← createStep globalContext localContext label justification
      |>.mapError fun msg => s! "step : {label}{LF}{msg}"
    createStepListAux globalContext (localContext.insert label step) (acc.push step) tl

def createStepList
  (globalContext : GlobalContext)
  (tactic_list : List (String × Justification)) :
  Except String (Array Step) :=
  createStepListAux globalContext {} #[] tactic_list


def createProof
  (globalContext : GlobalContext)
  (label : String)
  (tactic_list : List (String × Justification)) :
  Except String Proof := do
  let step_list ← createStepList globalContext tactic_list
  let Option.some last_step := step_list.back? | Except.error "The step list is empty."
  Except.ok {
    label := label
    assertion := last_step.assertion
    steps := step_list }


def createProofListAux
  (globalContext : GlobalContext)
  (acc : Array Proof) :
  List (String × (List (String × Justification))) → Except String (Array Proof)
  | [] => Except.ok acc
  | hd :: tl => do
  let proof ← createProof globalContext hd.fst hd.snd
    |>.mapError fun msg => s! "proof : {hd.fst}{LF}{msg}"
  createProofListAux (globalContext.insert hd.fst proof) (acc.push proof) tl

def createProofList
  (tactic_list_list : List (String × (List (String × Justification)))) :
  Except String (Array Proof) :=
  createProofListAux {} #[] tactic_list_list


#eval createProofList []

#eval createProofList [
  ( "id", [
      ( "s1", (prop_2 (Formula.var_ "P") (Formula.imp_ (Formula.var_ "P") (Formula.var_ "P")) (Formula.var_ "P")) ),
      ( "s2", (prop_1 (Formula.var_ "P") (Formula.imp_ (Formula.var_ "P") (Formula.var_ "P"))) ),
      ( "s3", (mp "s1" "s2") ),
      ( "s4", (prop_1 (Formula.var_ "P") (Formula.var_ "P")) ),
      ( "s5", (mp "s3" "s4") )
    ]
  ),
  ( "id'", [ ("s1", (thm "id")), ("s2", sub "s1" [("P", "Q")]) ] ),
  ( "meh", [ ("s1", (assume (Formula.var_ "P"))) ] ),
  ( "blah", [ ("s1", (def_and (Formula.var_ "P") (Formula.var_ "Q"))) ] )
]
