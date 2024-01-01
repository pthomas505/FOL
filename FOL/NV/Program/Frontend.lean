import FOL.NV.Program.Backend


set_option autoImplicit false


namespace FOL.NV.Program.Frontend

open Formula


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


abbrev GlobalContext : Type := Std.HashMap String Backend.Proof

def GlobalContext.find
  (context : GlobalContext)
  (label : String) :
  Except String Backend.Proof :=
  let opt : Option Backend.Proof := context.find? label

  if h : Option.isSome opt
  then Except.ok (Option.get opt h)
  else Except.error s! "{label} not found in global context."


def shift_hypothesis_left
  (localContext : LocalContext)
  (step_index : ℕ)
  (index : ℕ) :
  Except String Step := do
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

      Except.ok {
        assertion := {
          hypotheses := (Δ_1 ++ [H_2] ++ [H_1] ++ Δ_2)
          conclusion := conclusion }
        rule := Backend.Rule.struct_3_ Δ_1 Δ_2 H_1 H_2 conclusion step_index.repr
      }
    else Except.error "index must be greater than zero"
  else Except.error "index out of range"


def assume (phi : Formula) :
  Except String Step :=
    Except.ok {
      assertion := {
        hypotheses := [phi]
        conclusion := phi
      }
      rule := Backend.Rule.assume_ phi
    }


def prop_1
  (phi : Formula)
  (psi : Formula) :
  Except String Step :=
    Except.ok {
      assertion := {
        hypotheses := []
        conclusion := (phi.imp_ (psi.imp_ phi))
      }
      rule := Backend.Rule.prop_1_ phi psi
    }


def prop_2
  (phi : Formula)
  (psi : Formula)
  (chi : Formula) :
  Except String Step :=
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
  Except String Step := do
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
        rule := Backend.Rule.mp_ major_step.assertion.hypotheses major_left major_right major_step_index.repr minor_step_index.repr
      }
      else Except.error s! "minor does match major antecedent."
    else Except.error "minor hypotheses do not match major hypotheses."
  else Except.error s! "{major_step} is not an implication."


def PredReplaceListToFun : List (PredName × (List VarName) × Formula) → PredName → ℕ → Option ((List VarName) × Formula)
  | [] => fun (_ : PredName) (_ : ℕ) => Option.none
  | (X, zs, H) :: tl =>
    fun (P : PredName) (n : ℕ) =>
      if P = X ∧ n = zs.length
      then Option.some (zs, H)
      else PredReplaceListToFun tl P n


def sub
  (localContext : LocalContext)
  (step_index : ℕ)
  (pred_replace_list : List (PredName × (List VarName × Formula))) :
  Except String Step := do
  let step ← localContext.get step_index

  let hypotheses := step.assertion.hypotheses
  let conclusion := step.assertion.conclusion

  let τ : PredName → ℕ → Option (List VarName × Formula) := PredReplaceListToFun pred_replace_list
  Except.ok {
    assertion := {
      hypotheses := hypotheses.map (Sub.Pred.All.Rec.Option.Fresh.sub Backend.freshChar τ)
      conclusion := Sub.Pred.All.Rec.Option.Fresh.sub Backend.freshChar τ conclusion
    }
    rule := Backend.Rule.sub_ hypotheses conclusion τ step_index.repr
  }


def thm
  (globalContext : GlobalContext)
  (label : String) :
  Except String Step := do
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
  | assume_ : Formula → Command
  | prop_1_ : Formula → Formula → Command
  | prop_2_ : Formula → Formula → Formula → Command
  | mp_ : ℕ → ℕ → Command
  | sub_ : ℕ → List (PredName × (List VarName × Formula)) → Command
  | thm_ : String → Command


open Command


def createStepList
  (globalContext : GlobalContext)
  (localContext : LocalContext) :
  Command → Except String (List Step)

  | shift_hypothesis_left_ step_index index => do
    let step ← shift_hypothesis_left localContext step_index index
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


def checkProofList
  (proof_list : Except String (List Backend.Proof)) :
  Except String Unit := do
  let proof_list' ← proof_list
  Backend.checkProofList proof_list'


def P := pred_var_ (PredName.mk "P") []
def Q := pred_var_ (PredName.mk "Q") []

#eval createProofList [
  ("id", [prop_2_ P (P.imp_ P) P, prop_1_ P (P.imp_ P), mp_ 0 1, prop_1_ P P, mp_ 2 3]),
  ("id'", [thm_ "id", sub_ 0 [(PredName.mk "P", ([], Q))]])
  ]
