import FOL.NV.Program.Backend


set_option autoImplicit false


namespace FOL.NV.Program.Frontend

open Formula


def FreshChar : Char := '+'

def LF : Char := Char.ofNat 10


def List.toLFString
  {α : Type}
  [ToString α] :
  List α → String
  | [] => ""
  | hd :: tl => toString hd ++ LF.toString ++ List.toLFString tl


structure Step : Type :=
  (assertion : Backend.Sequent)
  (rule : Backend.Rule)

def Step.toString (x : Step) : String :=
  s! "{x.assertion} : {x.rule}"

instance : ToString Step :=
  { toString := fun x => x.toString }


structure Proof : Type :=
  (assertion : Backend.Sequent)
  (step_list : List Step)

def Proof.toString (x : Proof) : String :=
  s! "{x.assertion}{LF}{List.toLFString x.step_list}"

instance : ToString Proof :=
  { toString := fun x => x.toString }


abbrev LocalContext : Type := List Step

def LocalContext.get
  (context : LocalContext)
  (index : ℕ) :
  Except String Step :=
  let opt := context.get? index
  if h : Option.isSome opt
  then Except.ok (Option.get opt h)
  else Except.error s! "{index} not found in local context."


abbrev GlobalContext : Type := List Proof

def GlobalContext.get
  (context : GlobalContext)
  (index : ℕ) :
  Except String Proof :=
  let opt := context.get? index
  if h : Option.isSome opt
  then Except.ok (Option.get opt h)
  else Except.error s! "{index} not found in global context."


/-
-- index of first item is 0
#eval [1, 2].length
#eval List.take 0 [1, 2]
#eval List.drop 2 [1, 2]
#eval [1, 2][0]
#eval [1, 2][1]


def shift_hypothesis_left
  (step : Step)
  (label : String)
  (index : ℕ) :
  Except String Step :=
  let hypotheses := step.assertion.hypotheses
  let conclusion := step.assertion.conclusion

  if h1 : index < hypotheses.length
  then
    if h2 : index > 0
    then
      have : index - 1 < hypotheses.length := tsub_lt_of_lt h1
      let Δ_1 := List.take (index - 1) hypotheses
      let Δ_2 := List.drop (index + 1) hypotheses
      let H_1 := hypotheses[index - 1]
      let H_2 := hypotheses[index]

      Except.ok {
        label := label
        assertion := {
          hypotheses := (Δ_1 ++ [H_2] ++ [H_1] ++ Δ_2)
          conclusion := conclusion }
        rule := struct_3_ Δ_1 Δ_2 H_1 H_2 conclusion step.label
      }
    else Except.error "index must be greater than zero"
  else Except.error "index out of range"


def test_step : Step := {
  label := "1"
  assertion := {
    hypotheses := [P, Q, R, S]
    conclusion := P
  }
  rule := assume_ P
}

#eval shift_hypothesis_left test_step "2" 1

def prop_1_
  (label : String)
  (phi psi : Formula) :
  Step := {
    label := label
    assertion := {
      hypotheses := []
      conclusion := (phi.imp_ (psi.imp_ phi))
    }
    rule := Rule.prop_1_ phi psi
  }


def mp_
  (label : String)
  (context : Context)
  (major_step_label : String)
  (minor_step_label : String) :
  Except String Step := do
    let major_step ← context.find major_step_label
    let minor_step ← context.find minor_step_label

    if let (imp_ major_left major_right) := major_step.assertion.conclusion
    then
      if major_step.assertion.hypotheses = minor_step.assertion.hypotheses
      then
        if major_left = minor_step.assertion.conclusion
        then Except.ok {
          label := label
          assertion := {
            hypotheses := major_step.assertion.hypotheses
            conclusion := major_right
          }
          rule := Rule.mp_ major_step.assertion.hypotheses major_left major_right major_step_label minor_step_label
        }
        else Except.error s! "minor does match major antecedent."
      else Except.error "minor hypotheses do not match major hypotheses."
    else Except.error s! "{major_step_label} is not an implication."
-/

inductive Command : Type
  | shift_hypothesis_left_ : ℕ → ℕ → Command
  | assume_ : Formula → Command
  | prop_1_ : Formula → Formula → Command
  | mp_ : ℕ → ℕ → Command


open Command


def createStepList
  (globalContext : GlobalContext)
  (localContext : LocalContext) :
  Command → Except String (List Step)

  | shift_hypothesis_left_ step_index index => do
      let step ← localContext.get step_index

      let hypotheses := step.assertion.hypotheses
      let conclusion := step.assertion.conclusion

      if h1 : index < hypotheses.length
      then
        if h2 : index > 0
        then
          have : index - 1 < hypotheses.length := tsub_lt_of_lt h1
          let Δ_1 := List.take (index - 1) hypotheses
          let Δ_2 := List.drop (index + 1) hypotheses
          let H_1 := hypotheses[index - 1]
          let H_2 := hypotheses[index]

          Except.ok [{
            assertion := {
              hypotheses := (Δ_1 ++ [H_2] ++ [H_1] ++ Δ_2)
              conclusion := conclusion }
            rule := Backend.Rule.struct_3_ Δ_1 Δ_2 H_1 H_2 conclusion step_index.repr
          }]
        else Except.error "index must be greater than zero"
      else Except.error "index out of range"

  | assume_ phi =>
      Except.ok [{
        assertion := {
          hypotheses := [phi]
          conclusion := phi
        }
        rule := Backend.Rule.assume_ phi
      }]

  | prop_1_ phi psi =>
      Except.ok [{
        assertion := {
          hypotheses := []
          conclusion := (phi.imp_ (psi.imp_ phi))
        }
        rule := Backend.Rule.prop_1_ phi psi
      }]

  | mp_ major_step_index minor_step_index => do
    let major_step ← localContext.get major_step_index
    let minor_step ← localContext.get minor_step_index

    if let (imp_ major_left major_right) := major_step.assertion.conclusion
    then
      if major_step.assertion.hypotheses = minor_step.assertion.hypotheses
      then
        if major_left = minor_step.assertion.conclusion
        then Except.ok [{
          assertion := {
            hypotheses := major_step.assertion.hypotheses
            conclusion := major_right
          }
          rule := Backend.Rule.mp_ major_step.assertion.hypotheses major_left major_right major_step_index.repr minor_step_index.repr
        }]
        else Except.error s! "minor does match major antecedent."
      else Except.error "minor hypotheses do not match major hypotheses."
    else Except.error s! "{major_step} is not an implication."


def createProofStepListAux
  (globalContext : GlobalContext)
  (localContext : LocalContext) :
  List Command → Except String (List Step)
  | [] => Except.ok localContext
  | hd :: tl => do
      let step_list ← createStepList globalContext localContext hd

      createProofStepListAux globalContext (localContext ++ step_list) tl


def createProofStepList
  (globalContext : GlobalContext)
  (commands : List Command) :
  Except String (List Step) :=
  createProofStepListAux globalContext [] commands


def createProofLabeledStepListAux
  (index : ℕ) :
  List Step → List Backend.Step
  | [] => []
  | hd :: tl =>
    let step : Backend.Step := {
      label := index.repr
      assertion := hd.assertion
      rule := hd.rule
    }
    step :: (createProofLabeledStepListAux (index + 1) tl)


def createProof
  (globalContext : GlobalContext)
  (label : String)
  (commands : List Command) :
  Except String Backend.Proof := do
  let step_list ← createProofStepList globalContext commands

  let labeled_step_list := createProofLabeledStepListAux 0 step_list

  if let Option.some last_step := step_list.getLast?
  then Except.ok {
    label := label
    assertion := last_step.assertion
    step_list := labeled_step_list
  }
  else Except.error "The step list has no steps."


def checkProof
  (proof : Except String Backend.Proof) :
  Except String Backend.checkedProof := do
  let proof' ← proof
  Backend.checkProof {} proof'


def P := pred_var_ (PredName.mk "P") []

#eval checkProof (createProof [] "id" [assume_ P, assume_ P])