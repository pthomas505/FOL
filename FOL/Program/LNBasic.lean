import Std.Tactic.Lint.Frontend
import Std.Data.HashMap.Basic

import Mathlib.Data.String.Lemmas
import Mathlib.Util.CompileInductive

import FOL.FunctionUpdateIte
import FOL.List
import FOL.Tactics

set_option autoImplicit false


-- If a bound variable has a de Bruijn index of 0 then its binder is the first binder to its left.

/--
  The type of locally nameless variables.
-/
inductive Var
| F : String → Var
| B : ℕ → Var
  deriving Inhabited, DecidableEq

compile_inductive% Var

open Var

/--
  The string representation of locally nameless variables.
-/
def Var.toString : Var → String
  | F a => a
  | B n => s! "{n}"

instance : ToString Var :=
  { toString := fun x => x.toString }


/--
  The type of locally nameless formulas.
-/
inductive Formula : Type
  | pred_ : String → List Var → Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  | forall_ : Formula → Formula
  deriving Inhabited, DecidableEq

compile_inductive% Formula

open Formula

/--
  The string representation of locally nameless formulas.
-/
def Formula.toString : Formula → String
  | pred_ X xs => s! "({X} {xs})"
  | not_ phi => s! "(¬ {phi.toString})"
  | imp_ phi psi => s! "({phi.toString} → {psi.toString})"
  | forall_ phi => s! "(∀ {phi.toString})"


instance : ToString Formula :=
  { toString := fun F => F.toString }


def Var.freeVarSet : Var → Finset String
  | F a => {a}
  | B _ => ∅


/--
  Formula.freeVarSet F := The set of all of the variables that have a free occurrence in the formula F.
-/
def Formula.freeVarSet : Formula → Finset String
  | pred_ _ xs => xs.toFinset.biUnion Var.freeVarSet
  | not_ phi => phi.freeVarSet
  | imp_ phi psi => phi.freeVarSet ∪ psi.freeVarSet
  | forall_ phi => phi.freeVarSet


/--
  Helper function for openFormulaAux.
-/
def openVar
  (k : ℕ)
  (x : String) :
  Var → Var
  | F a => F a
  | B n => if k = n then F x else B n

/--
  Helper function for openFormula.
-/
def openFormulaAux
  (k : ℕ)
  (x : String) :
  Formula → Formula
  | pred_ X xs => pred_ X (xs.map (openVar k x))
  | not_ phi => not_ (openFormulaAux k x phi)
  | imp_ phi psi => imp_ (openFormulaAux k x phi) (openFormulaAux k x psi)
  | forall_ phi => forall_ (openFormulaAux (k + 1) x phi)

/--
  openFormula x F := Each of the bound variables in the formula F that indexes one more than the outermost binder is replaced by a free variable named x.
-/
def openFormula
  (x : String)
  (F : Formula) :
  Formula :=
  openFormulaAux 0 x F


def closeVar
  (k : ℕ)
  (x : String) :
  Var → Var
  | F a => if x = a then B k else F a
  | B n => B n

def closeFormulaAux
  (k : ℕ)
  (x : String) :
  Formula → Formula
  | pred_ X xs => pred_ X (xs.map (closeVar k x))
  | not_ phi => not_ (closeFormulaAux k x phi)
  | imp_ phi psi => imp_ (closeFormulaAux k x phi) (closeFormulaAux k x psi)
  | forall_ phi => forall_ (closeFormulaAux (k + 1) x phi)

def closeFormula
  (x : String)
  (F : Formula) :
  Formula :=
  closeFormulaAux 0 x F


def Var.isFree : Var → Prop
  | F _ => True
  | B _ => False


inductive Formula.lc' : Formula → Prop
  | pred_
    (X : String)
    (xs : List Var) :
    (∀ (v : Var), v ∈ xs → v.isFree) →
    lc' (pred_ X xs)

  | not_
    (phi : Formula) :
    lc' phi →
    lc' (not_ phi)

  | imp_
    (phi psi : Formula) :
    lc' phi →
    lc' psi →
    lc' (imp_ phi psi)

  | forall_
    (phi : Formula)
    (x : String) :
    lc' (openFormula x phi) →
    lc' (forall_ phi)


inductive Formula.lc : Formula → Prop
  | pred_
    (X : String)
    (xs : List Var) :
    (∀ (v : Var), v ∈ xs → v.isFree) →
    lc (pred_ X xs)

  | not_
    (phi : Formula) :
    lc phi →
    lc (not_ phi)

  | imp_
    (phi psi : Formula) :
    lc phi →
    lc psi →
    lc (imp_ phi psi)

  | forall_
    (phi : Formula)
    (L : Finset String) :
    (∀ (x : String), x ∉ L → lc (openFormula x phi)) →
    lc (forall_ phi)


def Var.lc_at
  (k : ℕ) :
  Var → Prop
  | F _ => True
  | B n => n < k

instance (k : ℕ) (v : Var) : Decidable (Var.lc_at k v) :=
  by
  cases v
  all_goals
    simp only [lc_at]
    infer_instance

def Formula.lc_at
  (k : ℕ) :
  Formula → Prop
  | pred_ _ xs => ∀ (v : Var), v ∈ xs → (v.lc_at k)
  | not_ phi => phi.lc_at k
  | imp_ phi psi => (phi.lc_at k) ∧ (psi.lc_at k)
  | forall_ phi => phi.lc_at (k + 1)

instance (k : ℕ) (F : Formula) : Decidable (Formula.lc_at k F) :=
  by
  induction F generalizing k
  all_goals
    unfold Formula.lc_at
    infer_instance

#eval Formula.lc_at 0 (forall_ (pred_ "X" [B 0]))
#eval Formula.lc_at 0 (forall_ (pred_ "X" [B 1]))


def Formula.body (F : Formula) : Prop :=
  ∃ (L : Finset String), ∀ (x : String), x ∉ L → Formula.lc (openFormula x F)


def Formula.closed (F : Formula) : Prop :=
  F.freeVarSet = ∅


def Var.sub (σ : String → String) : Var → Var
  | F a => F (σ a) 
  | B n => B n

def Formula.sub (σ : String → String) : Formula → Formula
  | pred_ X xs => pred_ X (xs.map (Var.sub σ))
  | not_ phi => not_ (phi.sub σ)
  | imp_ phi psi => imp_ (phi.sub σ) (psi.sub σ)
  | forall_ phi => forall_ (phi.sub σ)


structure Interpretation (D : Type) : Type :=
  (nonempty : Nonempty D)
  (pred_ : String → (List D → Prop))

def VarAssignment (D : Type) : Type := Var → D

def shift
  (D : Type)
  (V : VarAssignment D)
  (d : D) :
  VarAssignment D
  | F x => V (F x)
  | B 0 => d
  | B (n + 1) => V (B n)

def Holds
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D) :
  Formula → Prop
  | pred_ X xs => I.pred_ X (xs.map V)
  | not_ phi => ¬ Holds D I V phi
  | imp_ phi psi => Holds D I V phi → Holds D I V psi
  | forall_ phi =>
      ∀ d : D, Holds D I (shift D V d) phi


lemma CloseVarOpenVarComp
  (v : Var)
  (x : String)
  (k : ℕ)
  (h1 : x ∉ Var.freeVarSet v) :
  (closeVar k x ∘ openVar k x) v = v :=
  by
  cases v
  case F a =>
    simp only [Var.freeVarSet] at h1
    simp at h1

    simp
    simp only [openVar]
    simp only [closeVar]
    simp only [if_neg h1]
  case B n =>
    simp
    simp only [openVar]
    split_ifs
    case _ c1 =>
      simp only [closeVar]
      simp
      exact c1
    case _ c1 =>
      simp only [closeVar]

lemma OpenVarCloseVarComp
  (v : Var)
  (x : String)
  (k : ℕ)
  (h1 : Var.lc_at k v) :
  (openVar k x ∘ closeVar k x) v = v :=
  by
  cases v
  case F a =>
    simp
    simp only [closeVar]
    split_ifs
    case pos c1 =>
      subst c1
      simp only [openVar]
      simp
    case neg c1 =>
      simp only [openVar]
  case B n =>
    simp only [Var.lc_at] at h1

    simp
    simp only [closeVar]
    simp only [openVar]
    split_ifs
    case pos c1 =>
      subst c1
      simp at h1
    case neg c1 =>
      rfl


lemma CloseFormulaOpenFormulaComp
  (F : Formula)
  (k : ℕ)
  (x : String)
  (h1 : x ∉ F.freeVarSet) :
  (closeFormulaAux k x ∘ openFormulaAux k x) F = F :=
  by
  induction F generalizing k
  case pred_ X xs =>
    unfold Formula.freeVarSet at h1
    simp at h1

    simp
    unfold openFormulaAux
    unfold closeFormulaAux
    simp
    simp only [List.map_eq_self_iff]
    intro v a1
    apply CloseVarOpenVarComp
    exact h1 v a1
  case not_ phi phi_ih =>
    unfold Formula.freeVarSet at h1

    simp at phi_ih

    simp
    unfold openFormulaAux
    unfold closeFormulaAux
    simp only [phi_ih k h1]
  case imp_ phi psi phi_ih psi_ih =>
    unfold Formula.freeVarSet at h1
    simp at h1
    push_neg at h1

    simp at phi_ih

    simp
    unfold openFormulaAux
    unfold closeFormulaAux
    cases h1
    case _ h1_left h1_right =>
      congr
      · exact phi_ih k h1_left
      · exact psi_ih k h1_right
  case forall_ phi phi_ih =>
    unfold Formula.freeVarSet at h1

    simp at phi_ih

    simp
    unfold openFormulaAux
    unfold closeFormulaAux
    congr
    exact phi_ih (k + 1) h1


lemma OpenFormulaCloseFormulaComp
  (F : Formula)
  (k : ℕ)
  (x : String)
  (h1 : Formula.lc_at k F) :
  (openFormulaAux k x ∘ closeFormulaAux k x) F = F :=
  by
  induction F generalizing k
  case pred_ X xs =>
    unfold Formula.lc_at at h1

    simp
    unfold closeFormulaAux
    unfold openFormulaAux
    simp
    simp only [List.map_eq_self_iff]
    intro v a1
    apply OpenVarCloseVarComp
    exact h1 v a1
  case not_ phi phi_ih =>
    unfold Formula.lc_at at h1

    simp at phi_ih

    simp
    unfold closeFormulaAux
    unfold openFormulaAux
    simp only [phi_ih k h1]
  case imp_ phi psi phi_ih psi_ih =>
    unfold Formula.lc_at at h1

    simp at phi_ih

    simp
    unfold closeFormulaAux
    unfold openFormulaAux
    cases h1
    case _ h1_left h1_right =>
      congr
      · exact phi_ih k h1_left
      · exact psi_ih k h1_right
  case forall_ phi phi_ih =>
    simp at phi_ih

    simp
    simp only [closeFormulaAux]
    simp only [openFormulaAux]
    congr
    exact phi_ih (k + 1) h1


lemma OpenVarLeftInvOn
  (x : String)
  (k : ℕ) :
  Set.LeftInvOn (closeVar k x) (openVar k x) {v | x ∉ v.freeVarSet} :=
  by
  simp only [Set.LeftInvOn]
  simp
  intro v a1
  exact CloseVarOpenVarComp v x k a1

lemma CloseVarLeftInvOn
  (x : String)
  (k : ℕ) :
  Set.LeftInvOn (openVar k x) (closeVar k x) {v | Var.lc_at k v} :=
  by
  simp only [Set.LeftInvOn]
  simp
  intro v a1
  exact OpenVarCloseVarComp v x k a1


lemma OpenVarInjOn
  (x : String)
  (k : ℕ) :
  Set.InjOn (openVar k x) {v | x ∉ v.freeVarSet} :=
  by
  apply Set.LeftInvOn.injOn
  apply OpenVarLeftInvOn

lemma CloseVarInjOn
  (x : String)
  (k : ℕ) :
  Set.InjOn (closeVar k x) {v | Var.lc_at k v} :=
  by
  apply Set.LeftInvOn.injOn
  apply CloseVarLeftInvOn


lemma OpenFormulaLeftInvOn
  (x : String)
  (k : ℕ) :
  Set.LeftInvOn (closeFormulaAux k x) (openFormulaAux k x) {F | x ∉ F.freeVarSet} :=
  by
  simp only [Set.LeftInvOn]
  simp
  intro F a1
  apply CloseFormulaOpenFormulaComp
  exact a1

lemma CloseFormulaLeftInvOn
  (x : String)
  (k : ℕ) :
  Set.LeftInvOn (openFormulaAux k x) (closeFormulaAux k x) {F | Formula.lc_at k F} :=
  by
  simp only [Set.LeftInvOn]
  simp
  intro F a1
  apply OpenFormulaCloseFormulaComp
  exact a1


lemma OpenFormulaInjOn
  (x : String)
  (k : ℕ) :
  Set.InjOn (openFormulaAux k x) {F | x ∉ F.freeVarSet} :=
  by
  apply Set.LeftInvOn.injOn
  apply OpenFormulaLeftInvOn

lemma CloseFormulaInjOn
  (x : String)
  (k : ℕ) :
  Set.InjOn (closeFormulaAux k x) {F | Formula.lc_at k F} :=
  by
  apply Set.LeftInvOn.injOn
  apply CloseFormulaLeftInvOn


example
  (F G : Formula)
  (x : String)
  (k : ℕ)
  (h1 : x ∉ F.freeVarSet)
  (h2 : x ∉ G.freeVarSet)
  (h3 : openFormulaAux k x F = openFormulaAux k x G) :
  F = G :=
  by
  apply OpenFormulaInjOn
  · simp
    exact h1
  · simp
    exact h2
  · exact h3


lemma BodyImpLCForall
  (F : Formula)
  (h1 : Formula.body F) :
  Formula.lc (forall_ F) :=
  by
    simp only [body] at h1
    apply Exists.elim h1
    intro L a1

    apply Formula.lc.forall_
    exact a1


lemma LCForallImpBody
  (F : Formula)
  (h1 : Formula.lc (forall_ F)) :
  Formula.body F :=
  by
    cases h1
    case _ L a1 =>
      simp only [body]
      apply Exists.intro L
      exact a1


lemma LCForallIffBody
  (F : Formula) :
  Formula.body F ↔ Formula.lc (forall_ F) :=
  by
  constructor
  · apply BodyImpLCForall
  · apply LCForallImpBody


lemma OpenVarFreeVar
  (v : Var)
  (x : String)
  (k : ℕ) :
  (openVar k x v).freeVarSet ⊆ v.freeVarSet ∪ {x} :=
  by
  cases v
  case F a =>
    simp only [openVar]
    simp only [Var.freeVarSet]
    simp
  case B n =>
    simp only [openVar]
    split
    case _ c1 =>
      simp only [Var.freeVarSet]
      simp
    case _ c1 =>
      simp only [Var.freeVarSet]
      simp


lemma CloseVarFreeVar
  (v : Var)
  (x : String)
  (k : ℕ) :
  (closeVar k x v).freeVarSet ⊆ v.freeVarSet \ {x} :=
  by
  cases v
  case F a =>
    simp only [closeVar]
    split
    case _ c1 =>
      simp only [Var.freeVarSet]
      simp
    case _ c1 =>
      simp only [Var.freeVarSet]
      simp
      exact ne_comm.mp c1
  case B n =>
    simp only [closeVar]
    simp only [Var.freeVarSet]
    simp


lemma OpenFormulaFreeVar
  (F : Formula)
  (x : String)
  (k : ℕ) :
  (openFormulaAux k x F).freeVarSet ⊆ F.freeVarSet ∪ {x} :=
  by
  induction F generalizing k
  case pred_ X xs =>
    simp only [openFormulaAux]
    simp only [Formula.freeVarSet]
    simp
    intro v a1
    trans (Var.freeVarSet v ∪ {x})
    · exact OpenVarFreeVar v x k
    · apply Finset.union_subset_union_left
      apply Finset.subset_biUnion_of_mem
      simp
      exact a1
  case not_ phi phi_ih =>
    simp only [openFormulaAux]
    simp only [Formula.freeVarSet]
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    specialize phi_ih k
    specialize psi_ih k
    simp only [openFormulaAux]
    simp only [Formula.freeVarSet]
    sorry
  case forall_ phi phi_ih =>
    simp only [openFormulaAux]
    simp only [Formula.freeVarSet]
    apply phi_ih


lemma CloseFormulaFreeVar
  (F : Formula)
  (x : String)
  (k : ℕ) :
  (closeFormulaAux k x F).freeVarSet ⊆ F.freeVarSet \ {x} :=
  by
  induction F generalizing k
  case pred_ X xs =>
    simp only [closeFormulaAux]
    simp only [Formula.freeVarSet]
    simp
    intro v a1
    trans (v.freeVarSet \ {x})
    · exact CloseVarFreeVar v x k
    · apply Finset.sdiff_subset_sdiff
      · apply Finset.subset_biUnion_of_mem
        simp
        exact a1
      · simp
  case not_ phi phi_ih =>
    simp only [closeFormulaAux]
    simp only [Formula.freeVarSet]
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    specialize phi_ih k
    specialize psi_ih k
    simp only [closeFormulaAux]
    simp only [Formula.freeVarSet]
    sorry
  case forall_ phi phi_ih =>
    simp only [closeFormulaAux]
    simp only [Formula.freeVarSet]
    apply phi_ih


lemma SubOpenVar
  (v : Var)
  (σ : String → String)
  (x : String)
  (k : ℕ)
  (h1 : σ x = x) :
  Var.sub σ (openVar k x v) = openVar k x (Var.sub σ v) :=
  by
  cases v
  case F a =>
    simp only [openVar]
    simp only [Var.sub]
  case B n =>
    simp only [openVar]
    split
    case _ c1 =>
      simp only [Var.sub]
      simp only [if_pos c1]
      simp
      exact h1
    case _ c1 =>
      simp only [Var.sub]
      simp only [if_neg c1]


lemma SubCloseVar
  (v : Var)
  (σ : String → String)
  (x : String)
  (k : ℕ)
  (h1 : σ x = x)
  (h2 : ∀ (y : String), ¬ x = σ y) :
  Var.sub σ (closeVar k x v) = closeVar k x (Var.sub σ v) :=
  by
  cases v
  case F a =>
    simp only [closeVar]
    by_cases c1 : x = a
    · subst c1
      simp only [Var.sub]
      simp only [h1]
      simp
    · simp only [if_neg c1]
      simp only [Var.sub]
      simp only [if_neg (h2 a)]
  case B n =>
    simp only [closeVar]
    simp only [Var.sub]


lemma SubOpenFormula
  (F : Formula)
  (σ : String → String)
  (x : String)
  (k : ℕ)
  (h1 : σ x = x) :
  Formula.sub σ (openFormulaAux k x F) = openFormulaAux k x (Formula.sub σ F) :=
  by
  induction F generalizing k
  case pred_ X xs =>
    simp only [openFormulaAux]
    simp only [Formula.sub]
    simp
    simp only [List.map_eq_map_iff]
    intro v _
    exact SubOpenVar v σ x k h1
  case not_ phi phi_ih =>
    simp only [openFormulaAux]
    simp only [Formula.sub]
    congr! 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [openFormulaAux]
    simp only [Formula.sub]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ phi phi_ih =>
    simp only [openFormulaAux]
    simp only [Formula.sub]
    congr! 1
    apply phi_ih


lemma SubCloseFormula
  (F : Formula)
  (σ : String → String)
  (x : String)
  (k : ℕ)
  (h1 : σ x = x)
  (h2 : ∀ (y : String), ¬ x = σ y) :
  Formula.sub σ (closeFormulaAux k x F) = closeFormulaAux k x (Formula.sub σ F) :=
  by
  induction F generalizing k
  case pred_ X xs =>
    simp only [closeFormulaAux]
    simp only [Formula.sub]
    simp
    simp only [List.map_eq_map_iff]
    intro v _
    exact SubCloseVar v σ x k h1 h2
  case not_ phi phi_ih =>
    simp only [closeFormulaAux]
    simp only [Formula.sub]
    congr! 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [closeFormulaAux]
    simp only [Formula.sub]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ phi phi_ih =>
    simp only [closeFormulaAux]
    simp only [Formula.sub]
    congr! 1
    apply phi_ih


lemma Var.lc_at_succ
  (v : Var)
  (k : ℕ)
  (h1 : Var.lc_at k v) :
  Var.lc_at (k + 1) v :=
  by
  cases v
  case F a =>
    simp only [Var.lc_at]
  case B n =>
    simp only [Var.lc_at] at h1

    simp only [Var.lc_at]
    transitivity k
    · exact h1
    · simp

lemma Formula.lc_at_succ
  (F : Formula)
  (k : ℕ)
  (h1 : Formula.lc_at k F) :
  Formula.lc_at (k + 1) F :=
  by
  induction F generalizing k
  case pred_ X xs =>
    simp only [Formula.lc_at] at h1

    simp only [Formula.lc_at]
    intro v a1
    apply Var.lc_at_succ
    exact h1 v a1
  case not_ phi phi_ih =>
    simp only [Formula.lc_at] at h1

    simp only [Formula.lc_at]
    exact phi_ih k h1
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.lc_at] at h1

    simp only [Formula.lc_at]
    cases h1
    case _ h1_left h1_right =>
      constructor
      · exact phi_ih k h1_left
      · exact psi_ih k h1_right
  case forall_ phi phi_ih =>
    simp only [Formula.lc_at] at h1

    simp only [Formula.lc_at]
    exact phi_ih (k + 1) h1


lemma LCAtSuccImpLCAtOpenVar
  (x : String)
  (k : ℕ)
  (v : Var)
  (h1 : Var.lc_at (k + 1) v) :
  Var.lc_at k (openVar k x v) :=
  by
  cases v
  case F a =>
    simp only [openVar]
    simp only [Var.lc_at]
  case B n =>
    simp only [openVar]
    split
    case inl c1 =>
      simp only [Var.lc_at]
    case inr c1 =>
      simp only [Var.lc_at] at h1
      simp only [Var.lc_at]
      refine lt_of_le_of_ne' ?_ c1
      exact Nat.lt_succ.mp h1


lemma LCAtOpenVarImpLCAtSucc
  (x : String)
  (k : ℕ)
  (v : Var)
  (h1 : Var.lc_at k (openVar k x v)) :
  Var.lc_at (k + 1) v :=
  by
  cases v
  case F a =>
    simp only [Var.lc_at]
  case B n =>
    simp only [Var.lc_at]
    simp only [openVar] at h1
    split at h1
    case inl c1 =>
      subst c1
      simp
    case inr c1 =>
      simp only [Var.lc_at] at h1
      trans k
      · exact h1
      · simp


lemma LCAtForallImpLCAtOpenFormula
  (F : Formula)
  (x : String)
  (k : ℕ)
  (h1 : Formula.lc_at k (forall_ F)) :
  Formula.lc_at k (openFormulaAux k x F) :=
  by
  induction F generalizing k
  case pred_ X xs =>
    simp only [Formula.lc_at] at h1

    unfold openFormulaAux
    unfold Formula.lc_at
    simp
    intro v a1
    specialize h1 v a1
    exact LCAtSuccImpLCAtOpenVar x k v h1
  case not_ phi phi_ih =>
    simp only [Formula.lc_at] at h1

    simp only [Formula.lc_at] at phi_ih

    simp only [openFormulaAux]
    simp only [Formula.lc_at]
    exact phi_ih k h1
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.lc_at] at h1

    simp only [Formula.lc_at] at phi_ih
    simp only [Formula.lc_at] at psi_ih

    simp only [openFormulaAux]
    simp only [Formula.lc_at]
    cases h1
    case _ h1_left h1_right =>
      constructor
      · exact phi_ih k h1_left
      · exact psi_ih k h1_right
  case forall_ phi phi_ih =>
    simp only [Formula.lc_at] at h1

    simp only [Formula.lc_at] at phi_ih

    simp only [openFormulaAux]
    simp only [Formula.lc_at]
    exact phi_ih (k + 1) h1


lemma LCAtOpenFormulaImpLCAtForall
  (F : Formula)
  (x : String)
  (k : ℕ)
  (h1 : Formula.lc_at k (openFormulaAux k x F)) :
  Formula.lc_at k (forall_ F) :=
  by
  induction F generalizing k
  case pred_ X xs =>
    unfold openFormulaAux at h1
    unfold Formula.lc_at at h1
    simp at h1

    simp only [Formula.lc_at]
    intro v a1
    specialize h1 v a1
    exact LCAtOpenVarImpLCAtSucc x k v h1
  case not_ phi phi_ih =>
    unfold openFormulaAux at h1
    unfold Formula.lc_at at h1

    simp only [Formula.lc_at] at phi_ih

    simp only [Formula.lc_at]
    exact phi_ih k h1
  case imp_ phi psi phi_ih psi_ih =>
    unfold openFormulaAux at h1
    unfold Formula.lc_at at h1

    simp only [Formula.lc_at] at phi_ih
    simp only [Formula.lc_at] at psi_ih

    simp only [Formula.lc_at]
    cases h1
    case _ h1_left h1_right =>
      constructor
      · exact phi_ih k h1_left
      · exact psi_ih k h1_right
  case forall_ phi phi_ih =>
    unfold openFormulaAux at h1
    unfold Formula.lc_at at h1

    simp only [Formula.lc_at] at phi_ih

    simp only [Formula.lc_at]
    exact phi_ih (k + 1) h1


example
  (F : Formula)
  (h1 : F.lc) :
  F.lc_at 0 :=
  by
  induction h1
  case pred_ X xs ih_1 =>
    unfold Formula.lc_at
    intro v a1
    cases v
    case F a =>
      simp only [Var.lc_at]
    case B n =>
      specialize ih_1 (B n) a1
      simp only [Var.isFree] at ih_1

  case not_ phi phi_ih ih_1 =>
    unfold Formula.lc_at
    exact ih_1

  case imp_ phi psi phi_ih_1 psi_ih_1 phi_ih_2 psi_ih_2 =>
    unfold Formula.lc_at
    simp only [phi_ih_2]
    simp only [psi_ih_2]

  case forall_ phi L _ ih_2 =>
    unfold openFormula at ih_2

    obtain s1 := Infinite.exists_not_mem_finset L
    apply Exists.elim s1
    intro x a1
    apply LCAtOpenFormulaImpLCAtForall
    exact ih_2 x a1


example
  (F : Formula)
  (h1 : F.lc_at 0) :
  F.lc :=
  by
  induction F
  case pred_ X xs =>
    unfold Formula.lc_at at h1

    apply lc.pred_
    intro v a1
    cases v
    case _ a =>
      simp only [Var.isFree]
    case _ n =>
      specialize h1 (B n) a1
      simp only [Var.lc_at] at h1
      contradiction
  case forall_ phi phi_ih =>
    apply lc.forall_ phi
    intro x a1
    obtain s1 := LCAtForallImpLCAtOpenFormula phi x 0 h1
    unfold openFormula
    sorry
    sorry

  all_goals
    sorry


lemma LCAtOpenFormulaImpLCPrimeForall
  (F : Formula)
  (x : String)
  (h1 : (openFormulaAux 0 x F).lc_at 0) :
  lc' (forall_ F) :=
  by
  induction F
  case pred_ X xs =>
    simp only [Formula.lc_at] at h1

    apply lc'.forall_
    simp only [openFormula]
    simp only [openFormulaAux]
    apply lc'.pred_
    intro v a1
    cases v
    case _ a =>
      simp only [isFree]
    case _ n =>
      specialize h1 (B n) a1
      simp only [Var.lc_at] at h1
      simp at h1
  case forall_ phi phi_ih =>
    simp only [Formula.lc_at] at h1
    sorry

  all_goals
    sorry

example
  (F : Formula)
  (h1 : F.lc_at 0) :
  F.lc' :=
  by
  induction F
  case pred_ X xs =>
    unfold Formula.lc_at at h1

    apply lc'.pred_
    intro v a1
    cases v
    case _ a =>
      simp only [Var.isFree]
    case _ n =>
      specialize h1 (B n) a1
      simp only [Var.lc_at] at h1
      contradiction
  case forall_ phi phi_ih =>
    apply LCAtOpenFormulaImpLCPrimeForall phi default
    exact LCAtForallImpLCAtOpenFormula phi default 0 h1

  all_goals
    sorry

example
  (F : Formula)
  (h1 : F.lc') :
  F.lc_at 0 :=
  by
  induction h1
  case pred_ X xs ih_1  =>
    unfold Formula.lc_at
    intro v a1
    cases v
    case F a =>
      simp only [Var.lc_at]
    case B n =>
      specialize ih_1 (B n) a1
      simp only [isFree] at ih_1
  case not_ phi phi_ih ih =>
    simp only [Formula.lc_at]
    exact ih
  case imp_ phi psi phi_ih psi_ih ih_1 ih_2 =>
    simp only [Formula.lc_at]
    constructor
    · exact ih_1
    · exact ih_2
  case forall_ phi x _ ih_2 =>
    simp only [openFormula] at ih_2

    apply LCAtOpenFormulaImpLCAtForall phi x 0 ih_2


theorem HoldsIffSubHolds
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (F : Formula)
  (σ : String → String)
  (k : ℕ) :
  Holds D I V F ↔ Holds D I V (sub σ F) :=
  by
  induction F
  case pred_ X xs =>
    simp only [Formula.sub]
    simp only [Holds]
    simp
    congr! 1
    sorry
  all_goals
    sorry
