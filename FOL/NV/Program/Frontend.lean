import MathlibExtra.Except
import FOL.NV.Program.Backend


set_option autoImplicit false


namespace FOL.NV.Program.Frontend

open Formula_


abbrev GlobalContext : Type := Batteries.HashMap String Backend.Proof

def GlobalContext.find
  (context : GlobalContext)
  (label : String) :
  Except String Backend.Proof :=
  let opt : Option Backend.Proof := context.find? label
  opt.toExcept s! "{label} not found in global context."


abbrev LocalContext : Type := Array Backend.Step

def LocalContext.get
  (context : LocalContext)
  (index : ℕ) :
  Except String Backend.Step :=
  let opt : Option Backend.Step := context.get? index
  opt.toExcept s! "{index} not found in local context."


def shift_hypothesis_left
  (localContext : LocalContext)
  (step_index : ℕ)
  (hypothesis_index : ℕ) :
  Except String Backend.Step := do
  let step ← localContext.get step_index

  let hypotheses := step.assertion.hypotheses
  let conclusion := step.assertion.conclusion

  if h1 : hypothesis_index < hypotheses.length
  then
    have : hypothesis_index - 1 < hypotheses.length := tsub_lt_of_lt h1
    let Δ_1 := List.take (hypothesis_index - 1) hypotheses
    let Δ_2 := List.drop (hypothesis_index + 1) hypotheses
    let H_1 := hypotheses[hypothesis_index - 1]
    let H_2 := hypotheses[hypothesis_index]

    Except.ok {
      assertion := {
        hypotheses := (Δ_1 ++ [H_2] ++ [H_1] ++ Δ_2)
        conclusion := conclusion }
      rule := Backend.Rule.struct_3_ Δ_1 Δ_2 H_1 H_2 conclusion step_index
    }
  else Except.error "The hypothesis index is out of range."


def assume (phi : Formula_) :
  Except String Backend.Step :=
    Except.ok {
      assertion := {
        hypotheses := [phi]
        conclusion := phi
      }
      rule := Backend.Rule.assume_ phi
    }


def prop_1
  (phi : Formula_)
  (psi : Formula_) :
  Except String Backend.Step :=
    Except.ok {
      assertion := {
        hypotheses := []
        conclusion := (phi.imp_ (psi.imp_ phi))
      }
      rule := Backend.Rule.prop_1_ phi psi
    }


def prop_2
  (phi : Formula_)
  (psi : Formula_)
  (chi : Formula_) :
  Except String Backend.Step :=
    Except.ok {
      assertion := {
        hypotheses := []
        conclusion := ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi)))
      }
      rule := Backend.Rule.prop_2_ phi psi chi
    }


def mp
  (localContext : LocalContext)
  (major_step_index : ℕ)
  (minor_step_index : ℕ) :
  Except String Backend.Step := do
  let major_step ← localContext.get major_step_index
  let minor_step ← localContext.get minor_step_index

  if let (imp_ major_left major_right) := major_step.assertion.conclusion
  then
    if major_step.assertion.hypotheses = minor_step.assertion.hypotheses
    then
      if major_left = minor_step.assertion.conclusion
      then Except.ok {
        assertion := {
          hypotheses := major_step.assertion.hypotheses
          conclusion := major_right
        }
        rule := Backend.Rule.mp_ major_step.assertion.hypotheses major_left major_right major_step_index minor_step_index
      }
      else Except.error s! "The minor formula does not match the antecedent of the major formula."
    else Except.error "The minor hypotheses do not match the major hypotheses."
  else Except.error s! "The major step is not an implication."


def sub
  (localContext : LocalContext)
  (step_index : ℕ)
  (xs : List (PredName_ × (List VarName_ × Formula_))) :
  Except String Backend.Step := do
  let step ← localContext.get step_index

  let hypotheses := step.assertion.hypotheses
  let conclusion := step.assertion.conclusion

  let τ : PredName_ → ℕ → Option (List VarName_ × Formula_) := Backend.PredReplaceListToFun xs

  Except.ok {
    assertion := {
      hypotheses := hypotheses.map (Sub.Pred.All.Rec.Option.Fresh.sub_pred_all_rec_opt Backend.freshChar τ)
      conclusion := Sub.Pred.All.Rec.Option.Fresh.sub_pred_all_rec_opt Backend.freshChar τ conclusion
    }
    rule := Backend.Rule.sub_ hypotheses conclusion xs step_index
  }


def thm
  (globalContext : GlobalContext)
  (label : String) :
  Except String Backend.Step := do
  let step ← globalContext.find label

  Except.ok {
    assertion := {
      hypotheses := step.assertion.hypotheses
      conclusion := step.assertion.conclusion
    }
    rule := Backend.Rule.thm_ label
  }


inductive Command : Type
  | shift_hypothesis_left_ : ℕ → ℕ → Command
  | assume_ : Formula_ → Command
  | prop_1_ : Formula_ → Formula_ → Command
  | prop_2_ : Formula_ → Formula_ → Formula_ → Command
  | mp_ : ℕ → ℕ → Command
  | sub_ : ℕ → List (PredName_ × (List VarName_ × Formula_)) → Command
  | thm_ : String → Command


open Command


def createStepList
  (globalContext : GlobalContext)
  (localContext : LocalContext) :
  Command → Except String (List Backend.Step)

  | shift_hypothesis_left_ step_index hypothesis_index => do
    let step ← shift_hypothesis_left localContext step_index hypothesis_index
    Except.ok [step]

  | assume_ phi => do
    let step ← assume phi
    Except.ok [step]

  | prop_1_ phi psi => do
    let step ← prop_1 phi psi
    Except.ok [step]

  | prop_2_ phi psi chi => do
    let step ← prop_2 phi psi chi
    Except.ok [step]

  | mp_ major_step_index minor_step_index => do
    let step ← mp localContext major_step_index minor_step_index
    Except.ok [step]

  | sub_ step_index a => do
    let step ← sub localContext step_index a
    Except.ok [step]

  | thm_ label => do
    let step ← thm globalContext label
    Except.ok [step]


def createProofStepListAux
  (globalContext : GlobalContext)
  (localContext : LocalContext)
  (acc : List Backend.Step) :
  List Command → Except String (List Backend.Step)
  | [] => Except.ok acc
  | hd :: tl => do
      let step_list ← createStepList globalContext localContext hd

      createProofStepListAux globalContext (localContext ++ step_list) (acc.append step_list) tl


def createProofStepList
  (globalContext : GlobalContext)
  (commands : List Command) :
  Except String (List Backend.Step) :=
  createProofStepListAux globalContext #[] [] commands


def createProof
  (globalContext : GlobalContext)
  (label : String)
  (commands : List Command) :
  Except String Backend.Proof := do
  let step_list ← createProofStepList globalContext commands

  let opt := step_list.getLast?
  let last ← opt.toExcept "The step list is empty."

  Except.ok {
    label := label
    assertion := last.assertion
    step_list := step_list
  }


def createProofListAux
  (globalContext : GlobalContext)
  (acc : List Backend.Proof) :
  List (String × (List Command)) → Except String (List Backend.Proof)
  | [] => Except.ok acc
  | (label, commands) :: tl => do
    let proof ← createProof globalContext label commands

    createProofListAux (globalContext.insert label proof) (acc ++ [proof]) tl

def createProofList
  (labeled_command_list : List (String × (List Command))) :
  Except String (List Backend.Proof) :=
  createProofListAux {} [] labeled_command_list


def createJsonProofList
  (labeled_command_list : List (String × (List Command))) :
  Except String Lean.Json := do
  let proof_list ← createProofList labeled_command_list
  Except.ok (Lean.toJson proof_list)


def checkProofList
  (proof_list : Except String (List Backend.Proof)) :
  Except String (List Backend.CheckedProof) := do
  let proof_list' ← proof_list
  Backend.checkProofList proof_list'


def P := pred_var_ (PredName_.mk "P") []
def Q := pred_var_ (PredName_.mk "Q") []

#eval checkProofList (createProofList [
  ("id", [prop_2_ P (P.imp_ P) P, prop_1_ P (P.imp_ P), mp_ 0 1, prop_1_ P P, mp_ 2 3]),
  ("id'", [thm_ "id", sub_ 0 [(PredName_.mk "P", ([], Q))]])
  ]
)

#eval createJsonProofList [
  ("id", [prop_2_ P (P.imp_ P) P, prop_1_ P (P.imp_ P), mp_ 0 1, prop_1_ P P, mp_ 2 3]),
  ("id'", [thm_ "id", sub_ 0 [(PredName_.mk "P", ([], Q))]])
  ]
