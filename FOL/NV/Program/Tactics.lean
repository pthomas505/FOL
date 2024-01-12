import Std
import Mathlib.Util.CompileInductive
import Lean.Data.Json.Basic


set_option autoImplicit false


/--
  The type of variable names.
-/
structure VarName extends String
  deriving Inhabited, DecidableEq

instance : ToString VarName :=
  { toString := fun (x : VarName) => x.toString }

instance : Repr VarName :=
  { reprPrec := fun (x : VarName) _ => x.toString.toFormat }

instance : Lean.ToJson VarName :=
  { toJson := fun (x : VarName) => Lean.toJson x.toString }

instance : Lean.FromJson VarName :=
  { fromJson? := fun (json : Lean.Json) => do
    let str ← Lean.fromJson? json
    Except.ok (VarName.mk str) }


/--
  The type of predicate names.
-/
structure PredName extends String
  deriving Inhabited, DecidableEq

instance : ToString PredName :=
  { toString := fun (X : PredName) => X.toString }

instance : Repr PredName :=
  { reprPrec := fun (X : PredName) _ => X.toString.toFormat }

instance : Lean.ToJson PredName :=
  { toJson := fun (X : PredName) => Lean.toJson X.toString }

instance : Lean.FromJson PredName :=
  { fromJson? := fun (json : Lean.Json) => do
    let str ← Lean.fromJson? json
    Except.ok (PredName.mk str) }


/--
  The type of definition names.
-/
structure DefName extends String
  deriving Inhabited, DecidableEq

instance : ToString DefName :=
  { toString := fun (X : DefName) => X.toString }

instance : Repr DefName :=
  { reprPrec := fun (X : DefName) _ => X.toString.toFormat }

instance : Lean.ToJson DefName :=
  { toJson := fun (X : DefName) => Lean.toJson X.toString }

instance : Lean.FromJson DefName :=
  { fromJson? := fun (json : Lean.Json) => do
    let str ← Lean.fromJson? json
    Except.ok (DefName.mk str) }


/--
  The type of terms.
-/
inductive Term : Type
  | var_ : VarName → Term
  | meta_ : Nat → Term
  deriving Inhabited, DecidableEq, Lean.ToJson, Lean.FromJson

compile_inductive% Term

open Term

/--
  The string representation of terms.
-/
def Term.toString : Term → String
  | var_ x => x.toString
  | meta_ n => n.repr


instance : ToString Term :=
  { toString := fun (t : Term) => t.toString }

instance : Repr Term :=
  { reprPrec := fun (t : Term) _ => t.toString.toFormat }


/--
  The type of formulas.
-/
inductive Formula : Type
  | pred_const_ : PredName → List Term → Formula
  | pred_var_ : PredName → List Term → Formula
  | eq_ : Term → Term → Formula
  | true_ : Formula
  | false_ : Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  | and_ : Formula → Formula → Formula
  | or_ : Formula → Formula → Formula
  | iff_ : Formula → Formula → Formula
  | forall_ : VarName → Formula → Formula
  | exists_ : VarName → Formula → Formula
  | def_ : DefName → List Term → Formula
  | meta_ : Nat → Formula
  deriving Inhabited, DecidableEq, Lean.ToJson, Lean.FromJson

compile_inductive% Formula

open Formula

/--
  The string representation of formulas.
-/
def Formula.toString : Formula → String
  | pred_const_ X ts =>
    if ts.isEmpty
    then s! "{X}"
    else s! "({X} {ts})"
  | pred_var_ X ts =>
    if ts.isEmpty
    then s! "{X}"
    else s! "({X} {ts})"
  | eq_ s t => s! "({s} = {t})"
  | true_ => "T"
  | false_ => "F"
  | not_ phi => s! "(¬ {phi.toString})"
  | imp_ phi psi => s! "({phi.toString} → {psi.toString})"
  | and_ phi psi => s! "({phi.toString} ∧ {psi.toString})"
  | or_ phi psi => s! "({phi.toString} ∨ {psi.toString})"
  | iff_ phi psi => s! "({phi.toString} ↔ {psi.toString})"
  | forall_ x phi => s! "(∀ {x}. {phi.toString})"
  | exists_ x phi => s! "(∃ {x}. {phi.toString})"
  | def_ X ts => s! "def ({X} {ts})"
  | meta_ n => n.repr


instance : ToString Formula :=
  { toString := fun (F : Formula) => F.toString }

instance : Repr Formula :=
  { reprPrec := fun (F : Formula) _ => F.toString.toFormat }


inductive Deduct : Type
  | struct_1_ : List Formula → Formula → Formula → Deduct → Deduct
  | struct_2_ : List Formula → Formula → Formula → Deduct → Deduct
  | struct_3_ : List Formula → List Formula → Formula → Formula → Formula → Deduct → Deduct
  | assume_ : Formula → Deduct
  | prop_0_ : Deduct
  | prop_1_ : Formula → Formula → Deduct
  | prop_2_ : Formula → Formula → Formula → Deduct
  | prop_3_ : Formula → Formula → Deduct
  | mp_ : List Formula → Formula → Formula → Deduct → Deduct → Deduct
  | dt_ : List Formula → Formula → Formula → Deduct → Deduct
  | pred_1_ : VarName → Formula → Formula → Deduct
  | pred_2_ : VarName → VarName → Formula → Deduct
  | pred_3_ : VarName → Formula → Deduct
  | gen_ : VarName → Formula → Deduct → Deduct
  | eq_1_ : VarName → Deduct
  | eq_2_eq_ : VarName → VarName → VarName → VarName → Deduct
  | eq_2_pred_var_ : PredName → List VarName → List VarName → Deduct
  | def_false_ : Deduct
  | def_and_ : Formula → Formula → Deduct
  | def_or_ : Formula → Formula → Deduct
  | def_iff_ : Formula → Formula → Deduct
  | def_exists_ : VarName → Formula → Deduct
  | sub_ : List Formula → Formula → List (PredName × (List VarName) × Formula) → Deduct → Deduct
  | thm_ : String → Deduct
  deriving Lean.ToJson, Lean.FromJson

open Deduct

def Deduct.toString : Deduct → String
  | struct_1_ Δ H phi D => s! "struct_1_ {Δ} {H} {phi} {D.toString}"
  | struct_2_ Δ H phi D => s! "struct_2_ {Δ} {H} {phi} {D.toString}"
  | struct_3_ Δ_1 Δ_2 H_1 H_2 phi D => s! "struct_3_ {Δ_1} {Δ_2} {H_1} {H_2} {phi} {D.toString}"
  | assume_ phi => s! "assume_ {phi}"
  | prop_0_ => "prop_0_"
  | prop_1_ phi psi => s! "prop_1_ {phi} {psi}"
  | prop_2_ phi psi chi => s! "prop_2_ {phi} {psi} {chi}"
  | prop_3_ phi psi => s! "prop_3_ {phi} {psi}"
  | mp_ Δ phi psi D_1 D_2 => s! "mp_ {Δ} {phi} {psi} {D_1.toString} {D_2.toString}"
  | dt_ Δ H phi D => s! "dt_ {Δ} {H} {phi} {D.toString}"
  | pred_1_ v phi psi => s! "pred_1_ {v} {phi} {psi}"
  | pred_2_ v t phi => s! "pred_2_ {v} {t} {phi}"
  | pred_3_ v phi => s! "pred_3_ {v} {phi}"
  | gen_ v phi D => s! "gen_ {v} {phi} {D.toString}"
  | eq_1_ v => s! "eq_1_ {v}"
  | eq_2_eq_ x_0 x_1 y_0 y_1 => s! "eq_2_eq_ {x_0} {x_1} {y_0} {y_1}"
  | eq_2_pred_var_ name xs ys => s! "eq_2_pred_var_ {name} {xs} {ys}"
  | def_false_ => s! "def_false_"
  | def_and_ phi psi => s! "def_and_ {phi} {psi}"
  | def_or_ phi psi => s! "def_or_ {phi} {psi}"
  | def_iff_ phi psi => s! "def_iff_ {phi} {psi}"
  | def_exists_ v phi => s! "def_exists_ {v} {phi}"
  | sub_ Δ phi xs D => s! "sub_ {Δ} {phi} {xs} {D.toString}"
  | thm_ label => s! "thm_ {label}"

instance : ToString Deduct :=
  { toString := fun (D : Deduct) => D.toString }


structure Sequent : Type :=
  (hypotheses : List Formula)
  (conclusion : Formula)
  deriving Inhabited, DecidableEq, Lean.ToJson, Lean.FromJson

def Sequent.toString (x : Sequent) : String :=
  s! "{x.hypotheses} ⊢ {x.conclusion}"

instance : ToString Sequent :=
  { toString := fun (x : Sequent) => x.toString }


structure State : Type :=
  (meta_to_sequent_map : Std.HashMap Nat Sequent)
  (meta_to_deduct_map : Std.HashMap Nat Deduct)
  (remaining_goal_list : List Nat)
