import Mathlib.Data.Finset.Basic
import Mathlib.Util.CompileInductive


set_option autoImplicit false


def LF : Char := Char.ofNat 10


/--
  The type of formulas.
-/
inductive Formula : Type
  | atom_ : String → Formula
  | true_ : Formula
  | false_ : Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  | and_ : Formula → Formula → Formula
  | or_ : Formula → Formula → Formula
  | iff_ : Formula → Formula → Formula
  deriving Inhabited, DecidableEq

compile_inductive% Formula

open Formula

/--
  The string representation of formulas.
-/
def Formula.toString : Formula → String
  | atom_ X => X
  | true_ => "T"
  | false_ => "F"
  | not_ phi => s! "(¬ {phi.toString})"
  | imp_ phi psi => s! "({phi.toString} → {psi.toString})"
  | and_ phi psi => s! "({phi.toString} ∧ {psi.toString})"
  | or_ phi psi => s! "({phi.toString} ∨ {psi.toString})"
  | iff_ phi psi => s! "({phi.toString} ↔ {psi.toString})"

instance : ToString Formula :=
  { toString := fun F => F.toString }


inductive IsDeduct : List Formula → Formula → Prop
  | struct_1_
    (Δ : List Formula)
    (H phi : Formula) :
    IsDeduct Δ phi →
    IsDeduct (H :: Δ) phi

  | struct_2_
    (Δ : List Formula)
    (H phi : Formula) :
    IsDeduct (H :: H :: Δ) phi →
    IsDeduct (H :: Δ) phi

  | struct_3_
    (Δ_1 Δ_2 : List Formula)
    (H_1 H_2 phi : Formula) :
    IsDeduct (Δ_1 ++ [H_1] ++ [H_2] ++ Δ_2) phi →
    IsDeduct (Δ_1 ++ [H_2] ++ [H_1] ++ Δ_2) phi

  /-
    phi ⊢ phi
  -/
  | assume_
    (phi : Formula) :
    IsDeduct [phi] phi

  /-
    ⊢ ⊤
  -/
  | prop_0_ :
    IsDeduct [] true_

  /-
    ⊢ phi → (psi → phi)
  -/
  | prop_1_
    (phi psi : Formula) :
    IsDeduct [] (phi.imp_ (psi.imp_ phi))

  /-
    ⊢ (phi → (psi → chi)) → ((phi → psi) → (phi → chi))
  -/
  | prop_2_
    (phi psi chi : Formula) :
    IsDeduct []
      ((phi.imp_ (psi.imp_ chi)).imp_
        ((phi.imp_ psi).imp_ (phi.imp_ chi)))

  /-
    ⊢ (¬ phi → ¬ psi) → (psi → phi)
  -/
  | prop_3_
    (phi psi : Formula) :
    IsDeduct []
      (((not_ phi).imp_ (not_ psi)).imp_
        (psi.imp_ phi))

  /-
    Δ ⊢ phi → psi ⇒
    Δ ⊢ phi ⇒
    Δ ⊢ psi
  -/
  | mp_
    (Δ : List Formula)
    (phi psi : Formula) :
    IsDeduct Δ (phi.imp_ psi) →
    IsDeduct Δ phi →
    IsDeduct Δ psi

  /-
    ⊢ ⊥ ↔ ¬ ⊤
  -/
  | def_false_ :
    IsDeduct [] (false_.iff_ (not_ true_))

  /-
    ⊢ (phi ∧ psi) ↔ ¬ (phi → ¬ psi)
  -/
  | def_and_
    (phi psi : Formula) :
    IsDeduct [] ((phi.and_ psi).iff_ (not_ (phi.imp_ (not_ psi))))

  /-
    ⊢ (phi ∨ psi) ↔ ((¬ phi) → psi)
  -/
  | def_or_
    (phi psi : Formula) :
    IsDeduct [] ((phi.or_ psi).iff_ ((not_ phi).imp_ psi))

  /-
    ⊢ (phi ↔ psi) ↔ ((phi → psi) ∧ (psi → phi))
    ⊢ (phi ↔ psi) ↔ ¬ ((phi → psi) → ¬ (psi → phi))
    ⊢ ((phi ↔ psi) → (¬ ((phi → psi) → ¬ (psi → phi)))) ∧ (¬ ((phi → psi) → ¬ (psi → phi)) → (phi ↔ psi))
    ⊢ ¬ (((phi ↔ psi) → (¬ ((phi → psi) → ¬ (psi → phi)))) → ¬ (¬ ((phi → psi) → ¬ (psi → phi)) → (phi ↔ psi)))
  -/
  | def_iff_
    (phi psi : Formula) :
    IsDeduct [] (not_ (((phi.iff_ psi).imp_ (not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi))))).imp_ (not_ ((not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi)))).imp_ (phi.iff_ psi)))))

  /-
    H :: Δ ⊢ phi ⇒
    Δ ⊢ H → phi
  -/
  | dt_
    (Δ : List Formula)
    (H : Formula)
    (phi : Formula) :
    IsDeduct (H :: Δ) phi →
    IsDeduct Δ (H.imp_ phi)


inductive Rule : Type
  | struct_1_ : List Formula → Formula → Formula → String → Rule
  | struct_2_ : List Formula → Formula → Formula → String → Rule
  | struct_3_ : List Formula → List Formula → Formula → Formula → Formula → String → Rule
  | assume_ : Formula → Rule
  | prop_0_ : Rule
  | prop_1_ : Formula → Formula → Rule
  | prop_2_ : Formula → Formula → Formula → Rule
  | prop_3_ : Formula → Formula → Rule
  | mp_ : List Formula → Formula → Formula → String → String → Rule
  | def_false_ : Rule
  | def_and_ : Formula → Formula → Rule
  | def_or_ : Formula → Formula → Rule
  | def_iff_ : Formula → Formula → Rule
  | dt_ : List Formula → Formula → Formula → String → Rule
  | thm_ : String → Rule

open Rule

def Rule.toString : Rule → String
  | struct_1_ Δ H phi label => s! "struct_1_ {Δ} {H} {phi} {label}"
  | struct_2_ Δ H phi label => s! "struct_2_ {Δ} {H} {phi} {label}"
  | struct_3_ Δ_1 Δ_2 H_1 H_2 phi label => s! "struct_3_ {Δ_1} {Δ_2} {H_1} {H_2} {phi} {label}"
  | assume_ phi => s! "assume_ {phi}"
  | prop_0_ => "prop_0_"
  | prop_1_ phi psi => s! "prop_1_ {phi} {psi}"
  | prop_2_ phi psi chi => s! "prop_2_ {phi} {psi} {chi}"
  | prop_3_ phi psi => s! "prop_3_ {phi} {psi}"
  | mp_ Δ phi psi label_1 label_2 => s! "mp_ {Δ} {phi} {psi} {label_1} {label_2}"
  | def_false_ => s! "def_false_"
  | def_and_ phi psi => s! "def_and_ {phi} {psi}"
  | def_or_ phi psi => s! "def_or_ {phi} {psi}"
  | def_iff_ phi psi => s! "def_iff_ {phi} {psi}"
  | dt_ Δ H phi label => s! "dt_ {Δ} {H} {phi} {label}"
  | thm_ label => s! "thm_ {label}"

instance : ToString Rule :=
  { toString := fun x => x.toString }


structure Sequent : Type :=
  (hypotheses : List Formula)
  (conclusion : Formula)
  deriving DecidableEq

def Sequent.toString (x : Sequent) : String :=
  s! "{x.hypotheses} ⊢ {x.conclusion}"

instance : ToString Sequent :=
  { toString := fun x => x.toString }

structure Sequent' : Type :=
  (val : Sequent)
  (prop : IsDeduct val.hypotheses val.conclusion)

def Sequent'.toString (x : Sequent') : String :=
  s! "{x.val.hypotheses} ⊢ {x.val.conclusion}"

instance : ToString Sequent' :=
  { toString := fun x => x.toString }


structure Step : Type :=
  (label : String)
  (assertion : Sequent')
  (rule : Rule)

def Step.toString (x : Step) : String :=
  s! "{x.label}. {x.assertion} : {x.rule}"

instance : ToString Step :=
  { toString := fun x => x.toString }


def List.toLFString
  {α : Type}
  [ToString α] :
  List α → String
  | [] => ""
  | hd :: tl => toString hd ++ LF.toString ++ List.toLFString tl


structure Proof : Type :=
  (label : String)
  (assertion : Sequent')
  (step_list : Array Step)

def Proof.toString (x : Proof) : String :=
  s! "{x.label} : {x.assertion}{LF}{x.step_list.data.toLFString}"

instance : ToString Proof :=
  { toString := fun x => x.toString }


abbrev GlobalContext : Type := Std.HashMap String Proof

def GlobalContext.find
  (context : GlobalContext)
  (label : String) :
  Except String Proof :=
  let opt := context.find? label
  if h : Option.isSome opt
  then Except.ok (Option.get opt h)
  else Except.error s! "{label} not found in global context."


abbrev LocalContext : Type := Std.HashMap String Step

def LocalContext.find
  (context : LocalContext)
  (label : String) :
  Except String Step :=
  let opt := context.find? label
  if h : Option.isSome opt
  then Except.ok (Option.get opt h)
  else Except.error s! "{label} not found in local context."


def ruleToSequent
  (globalContext : GlobalContext)
  (localContext : LocalContext) :
  Rule → Except String Sequent'

  | struct_1_ Δ H phi label => do
      let found ← localContext.find label

      let expected_val : Sequent := {
        hypotheses := Δ
        conclusion := phi }

      let return_val : Sequent := {
        hypotheses := H :: Δ
        conclusion := phi }

      if h : found.assertion.val = expected_val
      then Except.ok {
        val := return_val
        prop := by {
          apply IsDeduct.struct_1_ Δ H phi
          obtain s1 := found.assertion.prop
          simp only [h] at s1
          exact s1
        }
      }
      else Except.error s! "Expected :{LF}{expected_val}{LF}Found :{LF}{found.assertion.val}"

  | struct_2_ Δ H phi label => do
      let found ← localContext.find label

      let expected_val : Sequent := {
        hypotheses := H :: H :: Δ
        conclusion := phi }

      let return_val : Sequent := {
        hypotheses := H :: Δ
        conclusion := phi }

      if h : found.assertion.val = expected_val
      then Except.ok {
        val := return_val
        prop := by {
          apply IsDeduct.struct_2_ Δ H phi
          obtain s1 := found.assertion.prop
          simp only [h] at s1
          exact s1
        }
      }
      else Except.error s! "Expected :{LF}{expected_val}{LF}Found :{LF}{found.assertion.val}"

  | struct_3_ Δ_1 Δ_2 H_1 H_2 phi label => do
      let found ← localContext.find label

      let expected_val : Sequent := {
        hypotheses := Δ_1 ++ [H_1] ++ [H_2] ++ Δ_2
        conclusion := phi }

      let return_val : Sequent := {
        hypotheses := Δ_1 ++ [H_2] ++ [H_1] ++ Δ_2
        conclusion := phi }

      if h : found.assertion.val = expected_val
      then Except.ok {
        val := return_val
        prop := by {
          apply IsDeduct.struct_3_ Δ_1 Δ_2 H_1 H_2 phi
          obtain s1 := found.assertion.prop
          simp only [h] at s1
          exact s1
        }
      }
      else Except.error s! "Expected :{LF}{expected_val}{LF}Found :{LF}{found.assertion.val}"

  | assume_ phi =>
      let return_val : Sequent := {
        hypotheses := [phi]
        conclusion := phi }

      Except.ok {
        val := return_val
        prop := IsDeduct.assume_ phi
      }

  | prop_0_ =>
      let return_val : Sequent := {
        hypotheses := []
        conclusion := true_ }

      Except.ok {
        val := return_val
        prop := IsDeduct.prop_0_
      }

  | prop_1_ phi psi =>
      let return_val : Sequent := {
        hypotheses := []
        conclusion := (phi.imp_ (psi.imp_ phi)) }

      Except.ok {
        val := return_val
        prop := IsDeduct.prop_1_ phi psi
      }

  | prop_2_ phi psi chi =>
      let return_val : Sequent := {
        hypotheses := []
        conclusion := ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi))) }

      Except.ok {
        val := return_val
        prop := IsDeduct.prop_2_ phi psi chi
      }

  | prop_3_ phi psi =>
      let return_val : Sequent := {
      hypotheses := []
      conclusion := (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi)) }

      Except.ok {
        val := return_val
        prop := IsDeduct.prop_3_ phi psi
      }

  | mp_ Δ phi psi label_1 label_2 => do
      let found_1 ← localContext.find label_1
      let found_2 ← localContext.find label_2

      let expected_1 : Sequent := {
        hypotheses := Δ
        conclusion := phi.imp_ psi }

      let expected_2 : Sequent := {
        hypotheses := Δ
        conclusion := phi }

      let return_val : Sequent := {
          hypotheses := Δ
          conclusion := psi }

      if h1 : found_1.assertion.val = expected_1
      then
        if h2 : found_2.assertion.val = expected_2
        then Except.ok {
          val := return_val
          prop := by {
            apply IsDeduct.mp_ Δ phi psi
            · obtain s1 := found_1.assertion.prop
              simp only [h1] at s1
              exact s1
            · obtain s2 := found_2.assertion.prop
              simp only [h2] at s2
              exact s2
          }
        }
        else Except.error s! "Expected :{LF}{expected_2}{LF}Found :{LF}{found_2.assertion}"
      else Except.error s! "Expected :{LF}{expected_1}{LF}Found :{LF}{found_1.assertion}"

  | def_false_ =>
      let return_val : Sequent := {
        hypotheses := []
        conclusion := false_.iff_ (not_ true_) }

      Except.ok {
        val := return_val
        prop := IsDeduct.def_false_
      }

  | def_and_ phi psi =>
      let return_val : Sequent := {
        hypotheses := []
        conclusion := ((phi.and_ psi).iff_ (not_ (phi.imp_ (not_ psi)))) }

      Except.ok {
        val := return_val
        prop := IsDeduct.def_and_ phi psi
      }

  | def_or_ phi psi =>
      let return_val : Sequent := {
        hypotheses := []
        conclusion := ((phi.or_ psi).iff_ ((not_ phi).imp_ psi)) }

      Except.ok {
        val := return_val
        prop := IsDeduct.def_or_ phi psi
      }

  | def_iff_ phi psi =>
      let return_val : Sequent := {
        hypotheses := []
        conclusion := (not_ (((phi.iff_ psi).imp_ (not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi))))).imp_ (not_ ((not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi)))).imp_ (phi.iff_ psi))))) }

      Except.ok {
        val := return_val
        prop := IsDeduct.def_iff_ phi psi
      }

  | dt_ Δ H phi label => do
    let found ← localContext.find label

    let expected : Sequent := {
      hypotheses := H :: Δ
      conclusion := phi }

    let return_val : Sequent := {
      hypotheses := Δ
      conclusion := H.imp_ phi }

    if h : found.assertion.val = expected
    then Except.ok {
      val := return_val
      prop := by {
        apply IsDeduct.dt_ Δ H phi
        obtain s1 := found.assertion.prop
        simp only [h] at s1
        exact s1
      }
    }
    else Except.error s! "Expected :{LF}{expected}{LF}Found :{LF}{found.assertion}"

  | thm_ label => do
    let step ← globalContext.find label
    Except.ok step.assertion


def createStep
  (globalContext : GlobalContext)
  (localContext : LocalContext)
  (label : String)
  (rule : Rule) :
  Except String Step := do
  let sequent ← ruleToSequent globalContext localContext rule
  Except.ok {
    label := label
    assertion := sequent
    rule := rule }


def createStepListAux
  (globalContext : GlobalContext)
  (localContext : LocalContext)
  (step_list : Array Step) :
  List (String × Rule) → Except String (Array Step)
  | [] => Except.ok step_list
  | (label, rule) :: tl => do
    let step ← createStep globalContext localContext label rule
      |>.mapError fun message => s! "step label : {label}{LF}rule : {rule}{LF}{message}"
    createStepListAux globalContext (localContext.insert label step) (step_list.push step) tl

def createStepList
  (globalContext : GlobalContext)
  (labeled_rule_list : List (String × Rule)) :
  Except String (Array Step) :=
  createStepListAux globalContext {} #[] labeled_rule_list


def createProof
  (globalContext : GlobalContext)
  (label : String)
  (instruction_list : List (String × Rule)) :
  Except String Proof := do
  let step_list ← createStepList globalContext instruction_list
  let Option.some last_step := step_list.back? | Except.error "The step list is empty."
  Except.ok {
    label := label
    assertion := last_step.assertion
    step_list := step_list }


def createProofListAux
  (globalContext : GlobalContext)
  (proof_list : Array Proof) :
  List (String × (List (String × Rule))) → Except String (Array Proof)
  | [] => Except.ok proof_list
  | hd :: tl => do
  let proof ← createProof globalContext hd.fst hd.snd
    |>.mapError fun msg => s! "proof label : {hd.fst}{LF}{msg}"
  createProofListAux (globalContext.insert hd.fst proof) (proof_list.push proof) tl

def createProofList
  (instruction_list : List (String × (List (String × Rule)))) :
  Except String (Array Proof) :=
  createProofListAux {} #[] instruction_list
