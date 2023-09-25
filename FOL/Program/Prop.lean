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


structure Sequent : Type :=
  (hypotheses : List Formula)
  (conclusion : Formula)
  deriving Inhabited, DecidableEq

def Sequent.toString (x : Sequent) : String :=
  s! "{x.hypotheses} ⊢ {x.conclusion}"

instance : ToString Sequent :=
  { toString := fun x => x.toString }


inductive Justification : Type
  | struct_1_ : List Formula → Formula → Formula → String → Justification
  | struct_2_ : List Formula → Formula → Formula → String → Justification
  | struct_3_ : List Formula → List Formula → Formula → Formula → Formula → String → Justification
  | assume_ : Formula → Justification
  | prop_0_ : Justification
  | prop_1_ : Formula → Formula → Justification
  | prop_2_ : Formula → Formula → Formula → Justification
  | prop_3_ : Formula → Formula → Justification
  | mp_ : List Formula → Formula → Formula → String → String → Justification
  | def_false_ : Justification
  | def_and_ : Formula → Formula → Justification
  | def_or_ : Formula → Formula → Justification
  | def_iff_ : Formula → Formula → Justification
  | dt_ : List Formula → Formula → Formula → String → Justification
  | thm_ : String → Justification


open Justification

def Justification.toString : Justification → String
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


def justificationToSequent
  (globalContext : GlobalContext)
  (localContext : LocalContext) :
  Justification → Except String Sequent

  | struct_1_ Δ H phi label => do
      let step ← localContext.find label
      let expected : Sequent := {
        hypotheses := Δ
        conclusion := phi }

      if step.assertion = expected
      then Except.ok {
        hypotheses := H :: Δ
        conclusion := phi }
      else Except.error "TBD"

  | struct_2_ Δ H phi label => do
      let step ← localContext.find label
      let expected : Sequent := {
        hypotheses := H :: H :: Δ
        conclusion := phi }

      if step.assertion = expected
      then Except.ok {
        hypotheses := H :: Δ
        conclusion := phi }
      else Except.error "TBD"

  | struct_3_ Δ_1 Δ_2 H_1 H_2 phi label => do
      let step ← localContext.find label
      let expected : Sequent := {
        hypotheses := Δ_1 ++ [H_1] ++ [H_2] ++ Δ_2
        conclusion := phi }

      if step.assertion = expected
      then Except.ok {
        hypotheses := Δ_1 ++ [H_2] ++ [H_1] ++ Δ_2
        conclusion := phi }
      else Except.error "TBD"

  | assume_ phi => Except.ok {
      hypotheses := [phi]
      conclusion := phi }

  | prop_0_ => Except.ok {
      hypotheses := []
      conclusion := true_ }

  | prop_1_ phi psi => Except.ok {
      hypotheses := []
      conclusion := (phi.imp_ (psi.imp_ phi)) }

  | prop_2_ phi psi chi => Except.ok {
      hypotheses := []
      conclusion := ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi))) }

  | prop_3_ phi psi => Except.ok {
      hypotheses := []
      conclusion := (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi)) }

  | mp_ Δ phi psi label_1 label_2 => do
      let step_1 ← localContext.find label_1
      let step_2 ← localContext.find label_2

      let expected_1 : Sequent := {
        hypotheses := Δ
        conclusion := phi.imp_ psi }

      let expected_2 : Sequent := {
        hypotheses := Δ
        conclusion := phi }

      if step_1.assertion = expected_1 ∧ step_2.assertion = expected_2
      then Except.ok {
        hypotheses := Δ
        conclusion := psi }
      else Except.error "TBD"

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

  | dt_ Δ H phi label => do
    let step ← localContext.find label
    let expected : Sequent := {
      hypotheses := H :: Δ
      conclusion := phi }

    if step.assertion = expected
    then Except.ok {
      hypotheses := Δ
      conclusion := H.imp_ phi }
    else Except.error "TBD"

  | thm_ label => do
    let step ← globalContext.find label
    Except.ok step.assertion


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
  (instructions : List (String × Justification)) :
  Except String (Array Step) :=
  createStepListAux globalContext {} #[] instructions


def createProof
  (globalContext : GlobalContext)
  (label : String)
  (instructions : List (String × Justification)) :
  Except String Proof := do
  let step_list ← createStepList globalContext instructions
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
  (instructions : List (String × (List (String × Justification)))) :
  Except String (Array Proof) :=
  createProofListAux {} #[] instructions
