import FOL.NV.Program.Check


set_option autoImplicit false


namespace FOL.NV.Program.Frontend


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


inductive Rule : Type
  | struct_1_ : List Formula → Formula → Formula → String → Rule
  | struct_2_ : List Formula → Formula → Formula → String → Rule
  | shift_hypothesis_left : ℕ → ℕ → Rule
  | assume_ : Formula → Rule
  | prop_0_ : Rule
  | prop_1_ : Formula → Formula → Rule
  | prop_2_ : Formula → Formula → Formula → Rule
  | prop_3_ : Formula → Formula → Rule
  | mp_ : List Formula → Formula → Formula → String → String → Rule
  | dt_ : List Formula → Formula → Formula → String → Rule
  | pred_1_ : VarName → Formula → Formula → Rule
  | pred_2_ : VarName → VarName → Formula → Rule
  | pred_3_ : VarName → Formula → Rule
  | gen_ : VarName → Formula → String → Rule
  | eq_1_ : VarName → Rule
  | eq_2_eq_ : VarName → VarName → VarName → VarName → Rule
  | def_false_ : Rule
  | def_and_ : Formula → Formula → Rule
  | def_or_ : Formula → Formula → Rule
  | def_iff_ : Formula → Formula → Rule
  | def_exists_ : VarName → Formula → Rule
  | sub_ : List Formula → Formula → (PredName → ℕ → Option (List VarName × Formula)) → String → Rule
  | thm_ : String → Rule

open Rule


def createStepList
  (globalContext : GlobalContext)
  (localContext : LocalContext) :
  Rule → Except String (List Step)

  | shift_hypothesis_left step_index index => do
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
            label := label
            assertion := {
              hypotheses := (Δ_1 ++ [H_2] ++ [H_1] ++ Δ_2)
              conclusion := conclusion }
            rule := struct_3_ Δ_1 Δ_2 H_1 H_2 conclusion step.label
          }
        else Except.error "index must be greater than zero"
      else Except.error "index out of range"
