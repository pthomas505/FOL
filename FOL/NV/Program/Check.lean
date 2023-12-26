import FOL.NV.Formula
import FOL.NV.Sub.Var.All.Rec.Fresh.Sub

import Std


set_option autoImplicit false


namespace FOL.NV

open Formula


def FreshChar : Char := '+'

def LF : Char := Char.ofNat 10


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
    H :: Δ ⊢ phi ⇒
    Δ ⊢ H → phi
  -/
  | dt_
    (Δ : List Formula)
    (H : Formula)
    (phi : Formula) :
    IsDeduct (H :: Δ) phi →
    IsDeduct Δ (H.imp_ phi)

  /-
    ⊢ (∀ v (phi → psi)) → ((∀ v phi) → (∀ v psi))
  -/
  | pred_1_
    (v : VarName)
    (phi psi : Formula) :
    IsDeduct [] ((forall_ v (phi.imp_ psi)).imp_ ((forall_ v phi).imp_ (forall_ v psi)))

  /-
    ⊢ (∀ v phi) → phi(t/v)  provided phi admits t for v
  -/
  | pred_2_
    (v t : VarName)
    (phi : Formula) :
    IsDeduct [] ((forall_ v phi).imp_ (Sub.Var.All.Rec.Fresh.subFresh (Function.updateITE id v t) FreshChar phi))

  /-
    ⊢ phi → (∀ v phi)  provided v is not free in phi
  -/
  | pred_3_
    (v : VarName)
    (phi : Formula) :
    ¬ isFreeIn v phi →
    IsDeduct [] (phi.imp_ (forall_ v phi))

  /-
    ⊢ phi ⇒ ⊢ ∀ v phi
  -/
  | gen_
    (v : VarName)
    (phi : Formula) :
    IsDeduct [] phi →
    IsDeduct [] (forall_ v phi)

  /-
    ⊢ ∀ v (v = v)
  -/
  | eq_1_
    (v : VarName) :
    IsDeduct [] (forall_ v (eq_ v v))

  /-
    ⊢ ∀ x_0 ... ∀ x_n ∀ y_0 ... y_n ((x_0 = y_0) ∧ ... ∧ (x_n = y_n) ∧ ⊤) →((pred_ name [x_0 ... x_n] ↔ pred_ name [y_0 ... y_n]))
  -/
/-
  | eq_2_pred_const_
    (name : PredName)
    (n : ℕ)
    (xs ys : Fin n → VarName) :
    IsDeduct []
      (Forall_ (List.ofFn xs)
        (Forall_ (List.ofFn ys)
          ((And_ (List.ofFn fun i : Fin n => eq_ (xs i) (ys i))).imp_
            ((pred_const_ name (List.ofFn xs)).iff_ (pred_const_ name (List.ofFn ys))))))
-/

  /-
    ⊢ ∀ x_0 ∀ x_1 ∀ y_0 ∀ y_1 ((x_0 = y_0) ∧ (x_1 = y_1)) → ((eq_ x_0 x_1) ↔ (eq_ y_0 y_1))
  -/
  | eq_2_eq_
    (x_0 x_1 y_0 y_1 : VarName) :
    IsDeduct []
      (forall_ x_0
        (forall_ x_1
          (forall_ y_0
            (forall_ y_1
              ((and_ (eq_ x_0 y_0) (eq_ x_1 y_1)).imp_
                ((eq_ x_0 x_1).iff_ (eq_ y_0 y_1)))))))

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
    ⊢ (∃ v phi) ↔ ¬ (∀ v ¬ phi)
  -/
  | def_exists_
    (v : VarName)
    (phi : Formula) :
    IsDeduct [] ((exists_ v phi).iff_ (not_ (forall_ v (not_ phi))))


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
  | dt_ Δ H phi label => s! "dt_ {Δ} {H} {phi} {label}"
  | pred_1_ v phi psi => s! "pred_1_ {v} {phi} {psi}"
  | pred_2_ v t phi => s! "pred_2_ {v} {t} {phi}"
  | pred_3_ v phi => s! "pred_3_ {v} {phi}"
  | gen_ v phi label_1 => s! "gen_ {v} {phi} {label_1}"
  | eq_1_ v => s! "eq_1_ {v}"
  | eq_2_eq_ x_0 x_1 y_0 y_1 => s! "eq_2_eq_ {x_0} {x_1} {y_0} {y_1}"
  | def_false_ => s! "def_false_"
  | def_and_ phi psi => s! "def_and_ {phi} {psi}"
  | def_or_ phi psi => s! "def_or_ {phi} {psi}"
  | def_iff_ phi psi => s! "def_iff_ {phi} {psi}"
  | def_exists_ v phi => s! "def_exists_ {v} {phi}"
  | thm_ label => s! "thm_ {label}"

instance : ToString Rule :=
  { toString := fun x => x.toString }


structure Sequent : Type :=
  (hypotheses : List Formula)
  (conclusion : Formula)
  deriving Inhabited, DecidableEq

def Sequent.toString (x : Sequent) : String :=
  s! "{x.hypotheses} ⊢ {x.conclusion}"

instance : ToString Sequent :=
  { toString := fun x => x.toString }


structure checkedSequent : Type :=
  (val : Sequent)
  (prop : IsDeduct val.hypotheses val.conclusion)

instance : ToString checkedSequent :=
  { toString := fun x => x.val.toString }


structure Step : Type :=
  (label : String)
  (assertion : Sequent)
  (rule : Rule)

def Step.toString (x : Step) : String :=
  s! "{x.label}. {x.assertion} : {x.rule}"

instance : ToString Step :=
  { toString := fun x => x.toString }


structure checkedStep : Type :=
  (label : String)
  (assertion : checkedSequent)


def List.toLFString
  {α : Type}
  [ToString α] :
  List α → String
  | [] => ""
  | hd :: tl => toString hd ++ LF.toString ++ List.toLFString tl


structure Proof : Type :=
  (label : String)
  (assertion : Sequent)
  (step_list : List Step)

def Proof.toString (x : Proof) : String :=
  s! "{x.label} : {x.assertion}{LF}{List.toLFString x.step_list}"

instance : ToString Proof :=
  { toString := fun x => x.toString }


structure checkedProof : Type :=
  (label : String)
  (assertion : checkedSequent)

def checkedProof.toString (x : checkedProof) : String :=
  s! "{x.label} : {x.assertion}"

instance : ToString checkedProof :=
  { toString := fun x => x.toString }


abbrev GlobalContext : Type := Std.HashMap String checkedProof

def GlobalContext.find
  (context : GlobalContext)
  (label : String) :
  Except String checkedProof :=
  let opt := context.find? label
  if h : Option.isSome opt
  then Except.ok (Option.get opt h)
  else Except.error s! "{label} not found in global context."


abbrev LocalContext : Type := Std.HashMap String checkedStep

def LocalContext.find
  (context : LocalContext)
  (label : String) :
  Except String checkedStep :=
  let opt := context.find? label
  if h : Option.isSome opt
  then Except.ok (Option.get opt h)
  else Except.error s! "{label} not found in local context."


def checkRule
  (globalContext : GlobalContext)
  (localContext : LocalContext) :
  Rule → Except String checkedSequent

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

      let expected_val_1 : Sequent := {
        hypotheses := Δ
        conclusion := phi.imp_ psi }

      let expected_val_2 : Sequent := {
        hypotheses := Δ
        conclusion := phi }

      let return_val : Sequent := {
        hypotheses := Δ
        conclusion := psi }

      if h1 : found_1.assertion.val = expected_val_1
      then
        if h2 : found_2.assertion.val = expected_val_2
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
        else Except.error s! "Expected :{LF}{expected_val_2}{LF}Found :{LF}{found_2.assertion.val}"
      else Except.error s! "Expected :{LF}{expected_val_1}{LF}Found :{LF}{found_1.assertion.val}"

  | dt_ Δ H phi label => do
    let found ← localContext.find label

    let expected_val : Sequent := {
      hypotheses := H :: Δ
      conclusion := phi }

    let return_val : Sequent := {
      hypotheses := Δ
      conclusion := H.imp_ phi }

    if h : found.assertion.val = expected_val
    then Except.ok {
      val := return_val
      prop := by {
        apply IsDeduct.dt_ Δ H phi
        obtain s1 := found.assertion.prop
        simp only [h] at s1
        exact s1
      }
    }
    else Except.error s! "Expected :{LF}{expected_val}{LF}Found :{LF}{found.assertion.val}"

  | pred_1_ v phi psi =>
      let return_val : Sequent := {
        hypotheses := []
        conclusion := ((forall_ v (phi.imp_ psi)).imp_ ((forall_ v phi).imp_ (forall_ v psi))) }

      Except.ok {
        val := return_val
        prop := IsDeduct.pred_1_ v phi psi
      }

  | pred_2_ v t phi =>
      let return_val : Sequent := {
        hypotheses := []
        conclusion := ((forall_ v phi).imp_ (Sub.Var.All.Rec.Fresh.subFresh (Function.updateITE id v t) FreshChar phi)) }

      Except.ok {
        val := return_val
        prop := IsDeduct.pred_2_ v t phi
      }

  | pred_3_ v phi => do
      let return_val : Sequent := {
        hypotheses := []
        conclusion := phi.imp_ (forall_ v phi) }

      if h : ¬ isFreeIn v phi
      then Except.ok {
        val := return_val
        prop := IsDeduct.pred_3_ v phi h
      }
      else Except.error s! "{v} must not be free in {phi}."

  | gen_ v phi label => do
      let found ← localContext.find label

      let expected_val : Sequent := {
        hypotheses := []
        conclusion := phi }

      let return_val : Sequent := {
        hypotheses := []
        conclusion := forall_ v phi }

      if h : found.assertion.val = expected_val
      then Except.ok {
        val := return_val
        prop := by {
          apply IsDeduct.gen_ v phi
          obtain s1 := found.assertion.prop
          simp only [h] at s1
          exact s1
        }
      }
      else Except.error s! "Expected :{LF}{expected_val}{LF}Found :{LF}{found.assertion.val}"

  | eq_1_ v =>
      let return_val : Sequent := {
        hypotheses := []
        conclusion := forall_ v (eq_ v v) }

      Except.ok {
        val := return_val
        prop := IsDeduct.eq_1_ v
      }

  | eq_2_eq_ x_0 x_1 y_0 y_1 =>
      let return_val : Sequent := {
        hypotheses := []
        conclusion :=
          forall_ x_0
            (forall_ x_1
              (forall_ y_0
                (forall_ y_1
                  ((and_ (eq_ x_0 y_0) (eq_ x_1 y_1)).imp_
                    ((eq_ x_0 x_1).iff_ (eq_ y_0 y_1)))))) }

      Except.ok {
        val := return_val
        prop := IsDeduct.eq_2_eq_ x_0 x_1 y_0 y_1
      }

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

  | def_exists_ v phi =>
      let return_val : Sequent := {
        hypotheses := []
        conclusion := (exists_ v phi).iff_ (not_ (forall_ v (not_ phi))) }

      Except.ok {
        val := return_val
        prop := IsDeduct.def_exists_ v phi
      }

  | thm_ label => do
    let step ← globalContext.find label
    Except.ok step.assertion


def checkStep
  (globalContext : GlobalContext)
  (localContext : LocalContext)
  (step : Step) :
  Except String checkedStep := do
  let checkedSequent ← checkRule globalContext localContext step.rule
  if checkedSequent.val = step.assertion
  then Except.ok {
    label := step.label
    assertion := checkedSequent }
  else Except.error s! "Step assertion :{LF}{step.assertion}{LF}Rule assertion :{LF}{checkedSequent.val}"


def checkStepListAux
  (globalContext : GlobalContext)
  (localContext : LocalContext) :
  List Step → Except String checkedStep
  | [] => Except.error "The step list has no steps."
  | [last] => do
    let checkedStep ← checkStep globalContext localContext last
      |>.mapError fun message => s! "step label : {last.label}{LF}rule : {last.rule}{LF}{message}"
    Except.ok checkedStep
  | hd :: tl => do
    let checkedStep ← checkStep globalContext localContext hd
      |>.mapError fun message => s! "step label : {hd.label}{LF}rule : {hd.rule}{LF}{message}"
    checkStepListAux globalContext (localContext.insert checkedStep.label checkedStep) tl

def checkStepList
  (globalContext : GlobalContext)
  (stepList : List Step) :
  Except String checkedStep :=
  checkStepListAux globalContext {} stepList


def checkProof
  (globalContext : GlobalContext)
  (proof : Proof) :
  Except String checkedProof := do
  let lastCheckedStep ← checkStepList globalContext proof.step_list
  if lastCheckedStep.assertion.val = proof.assertion
  then Except.ok {
    label := proof.label
    assertion := lastCheckedStep.assertion }
  else Except.error s! "Proof assertion :{LF}{proof.assertion}{LF}Last step assertion :{LF}{lastCheckedStep.assertion.val}"


def checkProofListAux
  (globalContext : GlobalContext)
  (checkedProofList : List checkedProof) :
  List Proof → Except String (List checkedProof)
  | [] => Except.ok checkedProofList
  | hd :: tl => do
  let checkedProof ← checkProof globalContext hd
    |>.mapError fun message => s! "proof label : {hd.label}{LF}{message}"
  checkProofListAux (globalContext.insert checkedProof.label checkedProof) (checkedProofList.append [checkedProof]) tl

def checkProofList
  (proofList : List Proof) :
  Except String (List checkedProof) :=
  checkProofListAux {} [] proofList


example
  (Δ : List Formula)
  (F : Formula)
  (h1 : IsDeduct Δ F) :
  ∀ (D : Type) (I : Interpretation D) (V : VarAssignment D) (E : Env),
  ((∀ (H : Formula), H ∈ Δ → Holds D I V E H) → Holds D I V E F) :=
  by
  induction h1
  case struct_1_ Δ' H _ _ ih_2 =>
    intro D I V E a1
    apply ih_2
    intro H' a2
    simp at a1
    cases a1
    case _ a1_left a1_right =>
      exact a1_right H' a2
  case struct_2_ Δ' H _ _ ih_2 =>
    intro D I V E a1
    apply ih_2
    intro H' a2
    simp at a1
    cases a1
    case _ a1_left a1_right =>
      simp at a2
      cases a2
      case _ a2 =>
        simp only [a2]
        exact a1_left
      case _ a2 =>
        exact a1_right H' a2
  case struct_3_ Δ_1 Δ_2 H_1 H_2 _ _ ih_2 =>
    intro D I V E a1
    apply ih_2
    intro H' a2
    simp at a1
    apply a1
    simp at a2
    tauto
  case assume_ phi =>
    intro D I V E a1
    simp at a1
    exact a1
  case prop_0_ =>
    intro D I V E _
    simp only [Holds]
  case prop_1_ phi psi =>
    intro D I V E _
    simp only [Holds]
    tauto
  case prop_2_ phi psi chi =>
    intro D I V E _
    simp only [Holds]
    tauto
  case prop_3_ phi psi =>
    intro D I V E _
    simp only [Holds]
    tauto
  case mp_ Δ' phi psi _ _ ih_major ih_minor =>
    intro D I V E a1
    simp only [Holds] at ih_major
    apply ih_major
    · intro H' a2
      exact a1 H' a2
    · apply ih_minor
      exact a1
  case dt_ Δ' H phi _ ih_2 =>
    intro D I V E a1
    simp only [Holds]
    intro a2
    apply ih_2
    simp
    constructor
    · exact a2
    · exact a1
  case pred_1_ v phi psi =>
    intro D I V E _
    simp only [Holds]
    intro a2 a3 d
    apply a2 d
    exact a3 d
  case pred_2_ v t phi =>
    intro D I V E _
    obtain s1 := FOL.NV.Sub.Var.All.Rec.Fresh.substitution_theorem D I V E (Function.updateITE id v t) FreshChar phi

    simp only [Holds]
    intro a2
    simp only [s1]
    simp only [Function.updateITE_comp_left]
    simp
    exact a2 (V t)
  case pred_3_ v phi ih =>
    intro D I V E _
    simp only [Holds]
    intro a2 d

    have s1 : Holds D I (Function.updateITE V v d) E phi ↔ Holds D I V E phi
    {
      apply Holds_coincide_Var
      intro v' a1
      simp only [Function.updateITE]
      split_ifs
      case _ c1 =>
        subst c1
        contradiction
      case _ c1 =>
        rfl
    }

    simp only [s1]
    exact a2
  case gen_ v phi _ ih_2 =>
    intro D I V E _
    simp only [Holds]
    intro d
    apply ih_2
    simp
  case eq_1_ v =>
    intro D I V E _
    simp only [Holds]
    simp
  case eq_2_eq_ x_0 x_1 y_0 y_1 =>
    intro D I V E _
    simp only [Holds]
    intro x_0_d x_1_d y_0_d y_1_d a2
    simp only [Function.updateITE] at a2
    simp at a2

    simp only [Function.updateITE]
    simp

    split_ifs at *
    any_goals
      tauto
    any_goals
      aesop
  case def_false_ =>
    intro D I V E _
    simp only [Holds]
    tauto
  case def_and_ phi psi =>
    intro D I V E _
    simp only [Holds]
    tauto
  case def_or_ phi psi =>
    intro D I V E _
    simp only [Holds]
    tauto
  case def_iff_ phi psi =>
    intro D I V E _
    simp only [Holds]
    tauto
  case def_exists_ v phi =>
    intro D I V E _
    simp only [Holds]
    simp


example
  (proofList : List Proof)
  (h1 : (checkProofList proofList).isOk) :
  ∀ (proof : Proof), proof ∈ proofList → IsDeduct proof.assertion.hypotheses proof.assertion.conclusion :=
  by
  sorry


#eval checkProofList []

def P := pred_var_ (PredName.mk "P") []

#eval checkProofList [
  {
    label := "id"
    assertion := { hypotheses := [], conclusion := imp_ P P },
    step_list :=
    [
      {
        label := "s1",
        assertion := { hypotheses := [], conclusion := (imp_ (imp_ P (imp_ (imp_ P P) P)) (imp_ (imp_ P (imp_ P P)) (imp_ P P))) },
        rule := (prop_2_ P (P.imp_ P) P),
      },

      {
        label := "s2",
        assertion := { hypotheses := [], conclusion := (imp_ P (imp_ (imp_ P P) P)) },
        rule := (prop_1_ P (P.imp_ P))
      },

      {
        label := "s3",
        assertion := { hypotheses := [], conclusion := (imp_ (imp_ P (imp_ P P)) (imp_ P P)) },
        rule := (mp_ [] (imp_ P (imp_ (imp_ P P) P)) (imp_ (imp_ P (imp_ P P)) (imp_ P P)) "s1" "s2")
      },

      {
        label := "s4",
        assertion := { hypotheses := [], conclusion := (imp_ P (imp_ P P)) },
        rule := (prop_1_ P P)
      },

      {
        label := "s5",
        assertion := { hypotheses := [], conclusion := (imp_ P P) },
        rule := (mp_ [] (imp_ P (imp_ P P)) (imp_ P P) "s3" "s4")
      }
    ]
  }
]


abbrev Context : Type := Std.HashMap String Step

def Context.find
  (context : Context)
  (label : String) :
  Except String Step :=
  let opt := context.find? label
  if h : Option.isSome opt
  then Except.ok (Option.get opt h)
  else Except.error s! "{label} not found in local context."


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
