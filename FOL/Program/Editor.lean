import Mathlib.Data.Finset.Basic

set_option autoImplicit false


def LF : Char := Char.ofNat 10


inductive Formula : Type
  | pred_var_ : String → List String → Formula
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
  | pred_var_ X xs => s! "{X}{xs}"
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
  | pred_var_ X xs => pred_var_ (σ (X)) xs
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (propSub σ phi)
  | imp_ phi psi => imp_ (propSub σ phi) (propSub σ psi)
  | and_ phi psi => and_ (propSub σ phi) (propSub σ psi)
  | or_ phi psi => or_ (propSub σ phi) (propSub σ psi)
  | iff_ phi psi => iff_ (propSub σ phi) (propSub σ psi)


inductive Justification : Type
  | thin_ : String → List Formula → Justification
  | assume_ : Formula → Justification
  | prop_true_ : Justification
  | prop_1_ : Formula → Formula → Justification
  | prop_2_ : Formula → Formula → Formula → Justification
  | prop_3_ : Formula → Formula → Justification
  | mp_ : String → String → Justification
  | def_false_ : Justification
  | def_and_ : Formula → Formula → Justification
  | def_or_ : Formula → Formula → Justification
  | def_iff_ : Formula → Formula → Justification
  | global_ : String → List String → Justification
  | sub_ : String → List (String × String) → Justification

open Justification

def Justification.toString : Justification → String
  | thin_ label hypotheses => s! "thin {label} {hypotheses}"
  | assume_ hypothesis => s! "assume {hypothesis}"
  | prop_true_ => "prop_true"
  | prop_1_ phi psi => s! "prop_1 {phi} {psi}"
  | prop_2_ phi psi chi => s! "prop_2 {phi} {psi} {chi}"
  | prop_3_ phi psi => s! "prop_3 {phi} {psi}"
  | mp_ major_step_label minor_step_label => s! "mp {major_step_label} {minor_step_label}"
  | def_false_ => s! "def_false"
  | def_and_ phi psi => s! "def_and {phi} {psi}"
  | def_or_ phi psi => s! "def_or {phi} {psi}"
  | def_iff_ phi psi => s! "def_iff {phi} {psi}"
  | global_ global_proof_label local_steps_labels => s! "global {global_proof_label} {local_steps_labels}"
  | sub_ label pairs => s! "sub {label} {pairs}"

instance : ToString Justification :=
  { toString := fun x => x.toString }


structure Step : Type :=
  (label : String)
  (assertion : Sequent)
  (justification : Justification)

def Step.toString (x : Step) : String :=
  s! "{x.label}. {x.assertion} : {x.justification}"

instance : ToString Step :=
  { toString := fun x => x.toString }


structure Proof : Type :=
  (label : String)
  (assertion : Sequent)
  (steps : Array Step)

def List.toLFString
  {α : Type}
  [ToString α] :
  List α → String
  | [] => ""
  | hd :: tl => toString hd ++ LF.toString ++ List.toLFString tl

def Proof.toString (x : Proof) : String :=
  s! "{x.label} : {x.assertion}{LF}{x.steps.data.toLFString}"

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

def LocalContext.findList
  (context : LocalContext)
  (label_list : List String) :
  Except String (List Step) :=
  label_list.mapM (LocalContext.find context)


def justificationToSequent
  (globalContext : GlobalContext)
  (localContext : LocalContext) :
  Justification → Except String Sequent

  | thin_ label hypotheses => do
      let step ← localContext.find label
      Except.ok {
        hypotheses := step.assertion.hypotheses ++ hypotheses
        conclusion := step.assertion.conclusion }

  | assume_ phi => Except.ok {
      hypotheses := [phi],
      conclusion := phi }

  | prop_true_ => Except.ok {
      hypotheses := [],
      conclusion := true_ }

  | prop_1_ phi psi => Except.ok {
      hypotheses := [],
      conclusion := (phi.imp_ (psi.imp_ phi)) }

  | prop_2_ phi psi chi => Except.ok {
      hypotheses := []
      conclusion := ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi))) }

  | prop_3_ phi psi => Except.ok {
      hypotheses := []
      conclusion := (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi)) }

  | mp_ major_step_label minor_step_label => do
      let major_step ← localContext.find major_step_label
      let minor_step ← localContext.find minor_step_label
      if major_step.assertion.hypotheses.toFinset = minor_step.assertion.hypotheses.toFinset
      then
        if let imp_ major_step_assertion_conclusion_antecedent major_step_assertion_conclusion_consequent := major_step.assertion.conclusion
        then
          if minor_step.assertion.conclusion = major_step_assertion_conclusion_antecedent
          then Except.ok {
            hypotheses := major_step.assertion.hypotheses
            conclusion := major_step_assertion_conclusion_consequent }
          else Except.error s! "major step : {major_step_label} : {major_step.assertion}{LF}minor step : {minor_step_label} : {minor_step.assertion}{LF}The conclusion of the minor step must match the antecedent of the conclusion of the major step."
        else Except.error s! "major step : {major_step_label} : {major_step.assertion}{LF}The conclusion of the major step must be an implication."
      else Except.error s! "major step : {major_step_label} : {major_step.assertion}{LF}minor step : {minor_step_label} : {minor_step.assertion}{LF}The hypotheses of the minor step must match the hypotheses of the major step."

  | def_false_ => Except.ok {
      hypotheses := []
      conclusion := false_.iff_ (not_ true_) }

  | def_and_ phi psi => Except.ok {
      hypotheses := []
      conclusion := ((phi.and_ psi).iff_ (not_ (phi.imp_ (not_ psi)))) }

  | def_or_ phi psi => Except.ok {
      hypotheses := []
      conclusion := ((phi.or_ psi).iff_ ((not_ phi).imp_ psi)) }

  | def_iff_ phi psi => Except.ok {
      hypotheses := []
      conclusion := (not_ (((phi.iff_ psi).imp_ (not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi))))).imp_ (not_ ((not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi)))).imp_ (phi.iff_ psi))))) }

  | global_ global_proof_label local_steps_labels => do
      let global_proof ← globalContext.find global_proof_label
      let local_steps ← localContext.findList local_steps_labels
      let local_steps_assertions := local_steps.map Step.assertion
      let local_steps_assertions_hypotheses := local_steps_assertions.map Sequent.hypotheses
      let local_steps_assertions_conclusions := local_steps_assertions.map Sequent.conclusion
      if local_steps_assertions_conclusions = global_proof.assertion.hypotheses
      then
        if let hd :: tl := local_steps_assertions_hypotheses
        then
          if tl.all (hd == ·)
          then Except.ok {
            hypotheses := hd
            conclusion := global_proof.assertion.conclusion }
          else Except.error s! "local steps : {local_steps_labels} : {local_steps_assertions}{LF}The hypotheses of the local steps must be the same."
        else Except.ok {
            hypotheses := []
            conclusion := global_proof.assertion.conclusion }
      else Except.error s! "global proof : {global_proof_label} : {global_proof.assertion}{LF}local steps : {local_steps_labels} : {local_steps_assertions}{LF}The conclusions of the local steps must match the hypotheses of the global proof."

  | sub_ label pairs => do
      let step ← localContext.find label
      let (xs, ys) := List.unzip pairs
      let σ := Function.updateListIte id xs ys
      Except.ok {
        hypotheses := step.assertion.hypotheses.map (propSub σ)
        conclusion := propSub σ step.assertion.conclusion
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
      |>.mapError fun msg => s! "step label : {label}{LF}justification : {justification}{LF}{msg}"
    createStepListAux globalContext (localContext.insert label step) (acc.push step) tl

def createStepList
  (globalContext : GlobalContext)
  (justification_list : List (String × Justification)) :
  Except String (Array Step) :=
  createStepListAux globalContext {} #[] justification_list


def createProof
  (globalContext : GlobalContext)
  (label : String)
  (justification_list : List (String × Justification)) :
  Except String Proof := do
  let step_list ← createStepList globalContext justification_list
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
    |>.mapError fun msg => s! "proof label : {hd.fst}{LF}{msg}"
  createProofListAux (globalContext.insert hd.fst proof) (acc.push proof) tl

def createProofList
  (justification_list_list : List (String × (List (String × Justification)))) :
  Except String (Array Proof) :=
  createProofListAux {} #[] justification_list_list


#eval createProofList []

#eval createProofList [
  ( "id", [
      ( "s1", (prop_2_ (Formula.pred_var_ "P" []) (Formula.imp_ (Formula.pred_var_ "P" []) (Formula.pred_var_ "P" [])) (Formula.pred_var_ "P" [])) ),
      ( "s2", (prop_1_ (Formula.pred_var_ "P" []) (Formula.imp_ (Formula.pred_var_ "P" []) (Formula.pred_var_ "P" []))) ),
      ( "s3", (mp_ "s1" "s2") ),
      ( "s4", (prop_1_ (Formula.pred_var_ "P" []) (Formula.pred_var_ "P" [])) ),
      ( "s5", (mp_ "s3" "s4") )
    ]
  )
]
