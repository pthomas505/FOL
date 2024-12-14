import MathlibExtra.Except
import FOL.NV.Sub.Var.All.Rec.Sub
import FOL.NV.Sub.Pred.All.Rec.Option.Sub

import Batteries


set_option autoImplicit false


namespace FOL.NV.Program.Backend

open Formula_


def freshChar : Char := '+'


inductive IsDeduct : List Formula_ → Formula_ → Prop
  | struct_1_
    (Δ : List Formula_)
    (H phi : Formula_) :
    IsDeduct Δ phi →
    IsDeduct (H :: Δ) phi

  | struct_2_
    (Δ : List Formula_)
    (H phi : Formula_) :
    IsDeduct (H :: H :: Δ) phi →
    IsDeduct (H :: Δ) phi

  | struct_3_
    (Δ_1 Δ_2 : List Formula_)
    (H_1 H_2 phi : Formula_) :
    IsDeduct (Δ_1 ++ [H_1] ++ [H_2] ++ Δ_2) phi →
    IsDeduct (Δ_1 ++ [H_2] ++ [H_1] ++ Δ_2) phi

  /-
    phi ⊢ phi
  -/
  | assume_
    (phi : Formula_) :
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
    (phi psi : Formula_) :
    IsDeduct [] (phi.imp_ (psi.imp_ phi))

  /-
    ⊢ (phi → (psi → chi)) → ((phi → psi) → (phi → chi))
  -/
  | prop_2_
    (phi psi chi : Formula_) :
    IsDeduct []
      ((phi.imp_ (psi.imp_ chi)).imp_
        ((phi.imp_ psi).imp_ (phi.imp_ chi)))

  /-
    ⊢ (¬ phi → ¬ psi) → (psi → phi)
  -/
  | prop_3_
    (phi psi : Formula_) :
    IsDeduct []
      (((not_ phi).imp_ (not_ psi)).imp_
        (psi.imp_ phi))

  /-
    Δ ⊢ phi → psi ⇒
    Δ ⊢ phi ⇒
    Δ ⊢ psi
  -/
  | mp_
    (Δ : List Formula_)
    (phi psi : Formula_) :
    IsDeduct Δ (phi.imp_ psi) →
    IsDeduct Δ phi →
    IsDeduct Δ psi

  /-
    H :: Δ ⊢ phi ⇒
    Δ ⊢ H → phi
  -/
  | dt_
    (Δ : List Formula_)
    (H : Formula_)
    (phi : Formula_) :
    IsDeduct (H :: Δ) phi →
    IsDeduct Δ (H.imp_ phi)

  /-
    ⊢ (∀ v (phi → psi)) → ((∀ v phi) → (∀ v psi))
  -/
  | pred_1_
    (v : VarName_)
    (phi psi : Formula_) :
    IsDeduct [] ((forall_ v (phi.imp_ psi)).imp_ ((forall_ v phi).imp_ (forall_ v psi)))

  /-
    ⊢ (∀ v phi) → phi(t/v)  provided phi admits t for v
  -/
  | pred_2_
    (v t : VarName_)
    (phi : Formula_) :
    IsDeduct [] ((forall_ v phi).imp_ (Sub.Var.All.Rec.Fresh.sub_var_all_rec (Function.updateITE id v t) freshChar phi))

  /-
    ⊢ phi → (∀ v phi)  provided v is not free in phi
  -/
  | pred_3_
    (v : VarName_)
    (phi : Formula_) :
    ¬ var_is_free_in v phi →
    IsDeduct [] (phi.imp_ (forall_ v phi))

  /-
    ⊢ phi ⇒ ⊢ ∀ v phi
  -/
  | gen_
    (v : VarName_)
    (phi : Formula_) :
    IsDeduct [] phi →
    IsDeduct [] (forall_ v phi)

  /-
    ⊢ v = v
  -/
  | eq_1_
    (v : VarName_) :
    IsDeduct [] (eq_ v v)

  /-
    ⊢ ((x_0 = y_0) ∧ ... ∧ (x_n = y_n) ∧ ⊤) → (pred_var_ name [x_0 ... x_n] ↔ pred_var_ name [y_0 ... y_n])
  -/
  | eq_2_pred_var_
    (name : PredName_)
    (xs ys : List VarName_) :
    xs.length = ys.length →
    IsDeduct [] ((List.foldr and_ true_ (List.zipWith eq_ xs ys)).imp_ ((pred_var_ name xs).iff_ (pred_var_ name ys)))

  /-
    ⊢ ((x_0 = y_0) ∧ (x_1 = y_1)) → ((eq_ x_0 x_1) ↔ (eq_ y_0 y_1))
  -/
  | eq_2_eq_
    (x_0 x_1 y_0 y_1 : VarName_) :
    IsDeduct [] ((and_ (eq_ x_0 y_0) (eq_ x_1 y_1)).imp_ ((eq_ x_0 x_1).iff_ (eq_ y_0 y_1)))

  /-
    ⊢ ⊥ ↔ ¬ ⊤
  -/
  | def_false_ :
    IsDeduct [] (false_.iff_ (not_ true_))

  /-
    ⊢ (phi ∧ psi) ↔ ¬ (phi → ¬ psi)
  -/
  | def_and_
    (phi psi : Formula_) :
    IsDeduct [] ((phi.and_ psi).iff_ (not_ (phi.imp_ (not_ psi))))

  /-
    ⊢ (phi ∨ psi) ↔ ((¬ phi) → psi)
  -/
  | def_or_
    (phi psi : Formula_) :
    IsDeduct [] ((phi.or_ psi).iff_ ((not_ phi).imp_ psi))

  /-
    ⊢ (phi ↔ psi) ↔ ((phi → psi) ∧ (psi → phi))
    ⊢ (phi ↔ psi) ↔ ¬ ((phi → psi) → ¬ (psi → phi))
    ⊢ ((phi ↔ psi) → (¬ ((phi → psi) → ¬ (psi → phi)))) ∧ (¬ ((phi → psi) → ¬ (psi → phi)) → (phi ↔ psi))
    ⊢ ¬ (((phi ↔ psi) → (¬ ((phi → psi) → ¬ (psi → phi)))) → ¬ (¬ ((phi → psi) → ¬ (psi → phi)) → (phi ↔ psi)))
  -/
  | def_iff_
    (phi psi : Formula_) :
    IsDeduct [] (not_ (((phi.iff_ psi).imp_ (not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi))))).imp_ (not_ ((not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi)))).imp_ (phi.iff_ psi)))))

  /-
    ⊢ (∃ v phi) ↔ ¬ (∀ v ¬ phi)
  -/
  | def_exists_
    (v : VarName_)
    (phi : Formula_) :
    IsDeduct [] ((exists_ v phi).iff_ (not_ (forall_ v (not_ phi))))

  | sub_
    (Δ : List Formula_)
    (phi : Formula_)
    (τ : PredName_ → ℕ → Option (List VarName_ × Formula_)) :
    IsDeduct Δ phi →
    IsDeduct (Δ.map (Sub.Pred.All.Rec.Option.Fresh.sub_pred_all_rec_opt freshChar τ)) (Sub.Pred.All.Rec.Option.Fresh.sub_pred_all_rec_opt freshChar τ phi)


inductive Rule : Type
  | struct_1_ : List Formula_ → Formula_ → Formula_ → ℕ → Rule
  | struct_2_ : List Formula_ → Formula_ → Formula_ → ℕ → Rule
  | struct_3_ : List Formula_ → List Formula_ → Formula_ → Formula_ → Formula_ → ℕ → Rule
  | assume_ : Formula_ → Rule
  | prop_0_ : Rule
  | prop_1_ : Formula_ → Formula_ → Rule
  | prop_2_ : Formula_ → Formula_ → Formula_ → Rule
  | prop_3_ : Formula_ → Formula_ → Rule
  | mp_ : List Formula_ → Formula_ → Formula_ → ℕ → ℕ → Rule
  | dt_ : List Formula_ → Formula_ → Formula_ → ℕ → Rule
  | pred_1_ : VarName_ → Formula_ → Formula_ → Rule
  | pred_2_ : VarName_ → VarName_ → Formula_ → Rule
  | pred_3_ : VarName_ → Formula_ → Rule
  | gen_ : VarName_ → Formula_ → ℕ → Rule
  | eq_1_ : VarName_ → Rule
  | eq_2_eq_ : VarName_ → VarName_ → VarName_ → VarName_ → Rule
  | eq_2_pred_var_ : PredName_ → List VarName_ → List VarName_ → Rule
  | def_false_ : Rule
  | def_and_ : Formula_ → Formula_ → Rule
  | def_or_ : Formula_ → Formula_ → Rule
  | def_iff_ : Formula_ → Formula_ → Rule
  | def_exists_ : VarName_ → Formula_ → Rule
  | sub_ : List Formula_ → Formula_ → List (PredName_ × (List VarName_) × Formula_) → ℕ → Rule
  | thm_ : String → Rule
  deriving Lean.ToJson, Lean.FromJson

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
  | eq_2_pred_var_ name xs ys => s! "eq_2_pred_var_ {name} {xs} {ys}"
  | def_false_ => s! "def_false_"
  | def_and_ phi psi => s! "def_and_ {phi} {psi}"
  | def_or_ phi psi => s! "def_or_ {phi} {psi}"
  | def_iff_ phi psi => s! "def_iff_ {phi} {psi}"
  | def_exists_ v phi => s! "def_exists_ {v} {phi}"
  | sub_ Δ phi xs label => s! "sub_ {Δ} {phi} {xs} {label}"
  | thm_ label => s! "thm_ {label}"

instance : ToString Rule :=
  { toString := fun (x : Rule) => x.toString }


structure Sequent : Type where
  (hypotheses : List Formula_)
  (conclusion : Formula_)
  deriving Inhabited, DecidableEq, Lean.ToJson, Lean.FromJson

def Sequent.toString (x : Sequent) : String :=
  s! "{x.hypotheses} ⊢ {x.conclusion}"

instance : ToString Sequent :=
  { toString := fun (x : Sequent) => x.toString }


structure CheckedSequent : Type where
  (val : Sequent)
  (prop : IsDeduct val.hypotheses val.conclusion)

def CheckedSequent.toString (x : CheckedSequent) : String := x.val.toString

instance : ToString CheckedSequent :=
  { toString := fun (x : CheckedSequent) => x.toString }


structure Step : Type where
  (assertion : Sequent)
  (rule : Rule)
  deriving Lean.ToJson, Lean.FromJson

def Step.toString (x : Step) : String :=
  s! "{x.assertion} : {x.rule}"

instance : ToString Step :=
  { toString := fun (x : Step) => x.toString }


structure CheckedStep : Type where
  (assertion : CheckedSequent)
  (rule : Rule)

def CheckedStep.toString (x : CheckedStep) : String :=
  s! "{x.assertion} : {x.rule}"

instance : ToString CheckedStep :=
  { toString := fun (x : CheckedStep) => x.toString }


structure Proof : Type where
  (label : String)
  (assertion : Sequent)
  (step_list : List Step)
  deriving Lean.ToJson, Lean.FromJson


def List.toLFStringAux
  {α : Type}
  [ToString α]
  (i : ℕ) :
  List α → String
  | [] => ""
  | hd :: tl =>
    let x := List.toLFStringAux (i + 1) tl
    s! "{i}. {hd}\n{x}"

def List.toLFString
  {α : Type}
  [ToString α]
  (xs : List α) :
  String := List.toLFStringAux 0 xs

def Proof.toString (x : Proof) : String :=
  s! "{x.label} : {x.assertion}\n{List.toLFString x.step_list}"

instance : ToString Proof :=
  { toString := fun (x : Proof) => x.toString }


structure CheckedProof : Type where
  (label : String)
  (assertion : CheckedSequent)
  (step_list : List CheckedStep)

def CheckedProof.toString (x : CheckedProof) : String :=
  s! "{x.label} : {x.assertion}\n{List.toLFString x.step_list}"

instance : ToString CheckedProof :=
  { toString := fun (x : CheckedProof) => x.toString }


abbrev GlobalContext : Type := Batteries.HashMap String CheckedProof

def GlobalContext.find
  (context : GlobalContext)
  (label : String) :
  Except String CheckedProof :=
  let opt : Option CheckedProof := context.find? label
  opt.toExcept s! "{label} not found in global context."


abbrev LocalContext : Type := Array CheckedStep

def LocalContext.get
  (context : LocalContext)
  (index : ℕ) :
  Except String CheckedStep :=
  let opt : Option CheckedStep := context.get? index
  opt.toExcept s! "{index} not found in local context."


def PredReplaceListToFun : List (PredName_ × (List VarName_) × Formula_) → PredName_ → ℕ → Option ((List VarName_) × Formula_)
  | [] => fun (_ : PredName_) (_ : ℕ) => Option.none
  | (X, zs, H) :: tl =>
    fun (P : PredName_) (n : ℕ) =>
      if P = X ∧ n = zs.length
      then Option.some (zs, H)
      else PredReplaceListToFun tl P n


def checkRule
  (globalContext : GlobalContext)
  (localContext : LocalContext) :
  Rule → Except String CheckedSequent

  | struct_1_ Δ H phi label => do
    let found : CheckedStep ← localContext.get label

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
    else Except.error s! "Expected :\n{expected_val}\nFound :\n{found.assertion.val}"

  | struct_2_ Δ H phi label => do
    let found : CheckedStep ← localContext.get label

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
    else Except.error s! "Expected :\n{expected_val}\nFound :\n{found.assertion.val}"

  | struct_3_ Δ_1 Δ_2 H_1 H_2 phi label => do
    let found : CheckedStep ← localContext.get label

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
    else Except.error s! "Expected :\n{expected_val}\nFound :\n{found.assertion.val}"

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
    let found_1 : CheckedStep ← localContext.get label_1
    let found_2 : CheckedStep ← localContext.get label_2

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
      else Except.error s! "Expected :\n{expected_val_2}\nFound :\n{found_2.assertion.val}"
    else Except.error s! "Expected :\n{expected_val_1}\nFound :\n{found_1.assertion.val}"

  | dt_ Δ H phi label => do
    let found : CheckedStep ← localContext.get label

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
    else Except.error s! "Expected :\n{expected_val}\nFound :\n{found.assertion.val}"

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
      conclusion := ((forall_ v phi).imp_ (Sub.Var.All.Rec.Fresh.sub_var_all_rec (Function.updateITE id v t) freshChar phi)) }

    Except.ok {
      val := return_val
      prop := IsDeduct.pred_2_ v t phi
    }

  | pred_3_ v phi =>
    let return_val : Sequent := {
      hypotheses := []
      conclusion := phi.imp_ (forall_ v phi) }

    if h : ¬ var_is_free_in v phi
    then Except.ok {
      val := return_val
      prop := IsDeduct.pred_3_ v phi h
    }
    else Except.error s! "{v} must not be free in {phi}."

  | gen_ v phi label => do
    let found : CheckedStep ← localContext.get label

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
    else Except.error s! "Expected :\n{expected_val}\nFound :\n{found.assertion.val}"

  | eq_1_ v =>
    let return_val : Sequent := {
      hypotheses := []
      conclusion := eq_ v v }

    Except.ok {
      val := return_val
      prop := IsDeduct.eq_1_ v
    }

  | eq_2_eq_ x_0 x_1 y_0 y_1 =>
    let return_val : Sequent := {
      hypotheses := []
      conclusion := ((and_ (eq_ x_0 y_0) (eq_ x_1 y_1)).imp_ ((eq_ x_0 x_1).iff_ (eq_ y_0 y_1))) }

    Except.ok {
      val := return_val
      prop := IsDeduct.eq_2_eq_ x_0 x_1 y_0 y_1
    }

  | eq_2_pred_var_ name xs ys =>
    let return_val : Sequent := {
      hypotheses := []
      conclusion := ((List.foldr and_ true_ (List.zipWith eq_ xs ys)).imp_ ((pred_var_ name xs).iff_ (pred_var_ name ys))) }

    if h : xs.length = ys.length
    then Except.ok {
        val := return_val
        prop := IsDeduct.eq_2_pred_var_ name xs ys h
      }
    else Except.error "The lists of variables must have the same length."

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

  | sub_ Δ phi xs label => do
    let τ : PredName_ → ℕ → Option ((List VarName_) × Formula_) := PredReplaceListToFun xs

    let found : CheckedStep ← localContext.get label

    let expected_val : Sequent := {
      hypotheses := Δ
      conclusion := phi }

    let return_val : Sequent := {
      hypotheses := Δ.map (Sub.Pred.All.Rec.Option.Fresh.sub_pred_all_rec_opt freshChar τ)
      conclusion := Sub.Pred.All.Rec.Option.Fresh.sub_pred_all_rec_opt freshChar τ phi }

    if h : found.assertion.val = expected_val
    then Except.ok {
      val := return_val
      prop := by {
        apply IsDeduct.sub_
        obtain s1 := found.assertion.prop
        simp only [h] at s1
        exact s1
      }
    }
    else Except.error s! "Expected :\n{expected_val}\nFound :\n{found.assertion.val}"

  | thm_ label => do
    let step : CheckedProof ← globalContext.find label
    Except.ok step.assertion


def checkStep
  (globalContext : GlobalContext)
  (localContext : LocalContext)
  (step : Step) :
  Except String CheckedStep := do
  let checkedSequent : CheckedSequent ← checkRule globalContext localContext step.rule

  if checkedSequent.val = step.assertion
  then Except.ok {
    assertion := checkedSequent
    rule := step.rule
  }
  else Except.error s! "Step assertion :\n{step.assertion}\nRule assertion :\n{checkedSequent.val}"


def checkStepListAux
  (globalContext : GlobalContext)
  (localContext : LocalContext)
  (acc : List CheckedStep) :
  List Step → Except String (List CheckedStep)
  | [] => Except.ok acc
  | hd :: tl => do
    let checkedStep : CheckedStep ← checkStep globalContext localContext hd
      |>.mapError fun (message : String) => s! "rule : {hd.rule}\n{message}"
    checkStepListAux globalContext (localContext.push checkedStep) (acc.append [checkedStep]) tl

def checkStepList
  (globalContext : GlobalContext)
  (step_list : List Step) :
  Except String (List CheckedStep) :=
  checkStepListAux globalContext #[] [] step_list


def checkProof
  (globalContext : GlobalContext)
  (proof : Proof) :
  Except String CheckedProof := do
  let checkedStepList : List CheckedStep ← checkStepList globalContext proof.step_list

  let opt := checkedStepList.getLast?
  let last ← opt.toExcept "The step list is empty."

  if last.assertion.val = proof.assertion
  then Except.ok {
    label := proof.label
    assertion := last.assertion
    step_list := checkedStepList
  }
  else Except.error s! "Proof assertion :\n{proof.assertion}\nLast step assertion :\n{last.assertion.val}"


def checkProofListAux
  (globalContext : GlobalContext)
  (acc : List CheckedProof) :
  List Proof → Except String (List CheckedProof)
  | [] => Except.ok acc
  | hd :: tl => do
  let checkedProof : CheckedProof ← checkProof globalContext hd
    |>.mapError fun (message : String) => s! "proof label : {hd.label}\n{message}"

  checkProofListAux (globalContext.insert checkedProof.label checkedProof) (acc.append [checkedProof]) tl

def checkProofList
  (proofList : List Proof) :
  Except String (List CheckedProof) :=
  checkProofListAux {} [] proofList


theorem soundness
  (Δ : List Formula_)
  (F : Formula_)
  (h1 : IsDeduct Δ F) :
  ∀ (D : Type) (I : Interpretation_ D) (V : Valuation_ D) (E : Env_),
  ((∀ (H : Formula_), H ∈ Δ → holds D I V E H) → holds D I V E F) :=
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
    simp only [holds]
  case prop_1_ phi psi =>
    intro D I V E _
    simp only [holds]
    tauto
  case prop_2_ phi psi chi =>
    intro D I V E _
    simp only [holds]
    tauto
  case prop_3_ phi psi =>
    intro D I V E _
    simp only [holds]
    tauto
  case mp_ Δ' phi psi _ _ ih_major ih_minor =>
    intro D I V E a1
    simp only [holds] at ih_major
    apply ih_major
    · intro H' a2
      exact a1 H' a2
    · apply ih_minor
      exact a1
  case dt_ Δ' H phi _ ih_2 =>
    intro D I V E a1
    simp only [holds]
    intro a2
    apply ih_2
    simp
    constructor
    · exact a2
    · exact a1
  case pred_1_ v phi psi =>
    intro D I V E _
    simp only [holds]
    intro a2 a3 d
    apply a2 d
    exact a3 d
  case pred_2_ v t phi =>
    intro D I V E _
    obtain s1 := FOL.NV.Sub.Var.All.Rec.Fresh.substitution_theorem_sub_var_all_rec D I V E (Function.updateITE id v t) freshChar phi

    simp only [holds]
    intro a2
    simp only [s1]
    simp only [Function.updateITE_comp_left]
    simp
    exact a2 (V t)
  case pred_3_ v phi ih =>
    intro D I V E _
    simp only [holds]
    intro a2 d

    have s1 : holds D I (Function.updateITE V v d) E phi ↔ holds D I V E phi :=
    by
      apply holds_coincide_var
      intro v' a1
      simp only [Function.updateITE]
      split_ifs
      case _ c1 =>
        subst c1
        contradiction
      case _ c1 =>
        rfl

    simp only [s1]
    exact a2
  case gen_ v phi _ ih_2 =>
    intro D I V E _
    simp only [holds]
    intro d
    apply ih_2
    simp
  case eq_1_ v =>
    intro D I V E _
    simp only [holds]
  case eq_2_eq_ x_0 x_1 y_0 y_1 =>
    intro D I V E _
    simp only [holds]
    intro a2

    cases a2
    case _ a2_left a2_right =>
      simp only [a2_left]
      simp only [a2_right]
  case eq_2_pred_var_ X xs ys ih_1 =>
    intro D I V E _

    simp only [holds]
    intro a1
    congr! 1

    induction xs generalizing ys
    case _ =>
      cases ys
      case _ =>
        simp only [holds]
      case cons ys_hd ys_tl =>
        simp at ih_1
    case _ xs_hd xs_tl xs_ih =>
      cases ys
      case nil =>
        simp at ih_1
      case cons ys_hd ys_tl =>
        simp at ih_1

        simp at a1
        simp only [holds] at a1
        cases a1
        case _ a1_left a1_right =>
          simp
          constructor
          · exact a1_left
          · apply xs_ih ys_tl ih_1 a1_right
  case def_false_ =>
    intro D I V E _
    simp only [holds]
    tauto
  case def_and_ phi psi =>
    intro D I V E _
    simp only [holds]
    tauto
  case def_or_ phi psi =>
    intro D I V E _
    simp only [holds]
    tauto
  case def_iff_ phi psi =>
    intro D I V E _
    simp only [holds]
    tauto
  case def_exists_ v phi =>
    intro D I V E _
    simp only [holds]
    simp
  case sub_ Δ' phi τ _ ih_2 =>
    intro D I V E a1
    simp at a1

    obtain s1 := Sub.Pred.All.Rec.Option.Fresh.substitution_theorem_sub_pred_all_rec_opt D I V E freshChar τ
    simp only [← s1] at a1
    simp only [← s1]

    apply ih_2
    exact a1


lemma not_IsDeduct_false :
  ¬ IsDeduct [] false_ :=
  by
  intro contra
  obtain s1 := soundness [] false_ contra Unit default default default
  simp at s1
  simp only [holds] at s1


example :
  ∀ (P : Proof) (b : CheckedProof), P.assertion.hypotheses = [] ∧ P.assertion.conclusion = false_ → checkProof {} P = .ok b -> False :=
  by
  intro P b a1 a2
  simp only [checkProof] at a2
  simp only [bind] at a2
  simp only [Except.bind_eq_ok] at a2
  apply Exists.elim a2
  intro xs a3
  clear a2
  cases a3
  case _ a3_left a3_right =>
    apply Exists.elim a3_right
    intro last a4
    clear a3_right
    cases a4
    case _ a4_left a4_right =>
      split_ifs at a4_right
      case _ c1 =>
        obtain s1 := last.assertion.prop
        simp only [c1] at s1
        cases a1
        case _ a1_left a1_right =>
          simp only [a1_left] at s1
          simp only [a1_right] at s1
          simp only [not_IsDeduct_false] at s1


example
  (globalContext : GlobalContext)
  (P : Proof)
  (b : CheckedProof)
  (h1 : checkProof globalContext P = .ok b) :
  IsDeduct P.assertion.hypotheses P.assertion.conclusion :=
  by
  simp only [checkProof] at h1
  simp only [bind] at h1
  simp only [Except.bind_eq_ok] at h1
  apply Exists.elim h1
  intro xs a2
  clear h1
  cases a2
  case _ a2_left a2_right =>
    apply Exists.elim a2_right
    intro last a3
    clear a2_right
    cases a3
    case _ a3_left a3_right =>
      split_ifs at a3_right
      case _ c1 =>
        obtain s1 := last.assertion.prop
        simp only [c1] at s1
        exact s1
