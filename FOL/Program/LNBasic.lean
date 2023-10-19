import Std.Tactic.Lint.Frontend
import Std.Data.HashMap.Basic

import Mathlib.Data.String.Lemmas
import Mathlib.Util.CompileInductive

import FOL.FunctionUpdateIte
import FOL.List
import FOL.Tactics

set_option autoImplicit false


-- If a bound variable has a de Bruijn index of 0 then it is bound by the first binder to its left that it is in the scope of.


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
  | F x => x
  | B i => s! "{i}"

instance : ToString Var :=
  { toString := fun v => v.toString }


/--
  Var.isFree v := True if and only if v is a free variable.
-/
def Var.isFree : Var → Prop
  | F _ => True
  | B _ => False

/--
  Var.isBound v := True if and only if v is a bound variable.
-/
def Var.isBound : Var → Prop
  | F _ => False
  | B _ => True


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
  | pred_ X vs => s! "({X} {vs})"
  | not_ phi => s! "(¬ {phi.toString})"
  | imp_ phi psi => s! "({phi.toString} → {psi.toString})"
  | forall_ phi => s! "(∀ {phi.toString})"


instance : ToString Formula :=
  { toString := fun F => F.toString }


/--
  Useful for proving that some recursive functions terminate.
-/
def Formula.length  : Formula → ℕ
  | pred_ _ _ => 0
  | not_ phi => 1 + phi.length
  | imp_ phi psi => 1 + phi.length + psi.length
  | forall_ phi => 1 + phi.length


--------------------------------------------------


/--
  Formula.varSet F := The set of all of the variables in the formula F.
-/
def Formula.varSet : Formula → Finset Var
  | pred_ _ vs => vs.toFinset
  | not_ phi => phi.varSet
  | imp_ phi psi => phi.varSet ∪ psi.varSet
  | forall_ phi => phi.varSet


/--
  occursIn v F := True if and only if the variable v is in the formula F.
-/
def occursIn (v : Var) : Formula → Prop
  | pred_ _ vs => v ∈ vs
  | not_ phi => occursIn v phi
  | imp_ phi psi => occursIn v phi ∨ occursIn v psi
  | forall_ phi => occursIn v phi


/--
  Helper function for Formula.boundVarSet.
-/
def Var.boundVarSet : Var → Finset Var
  | F _ => ∅
  | B i => {B i}


/--
  Formula.boundVarSet F := The set of all of the bound variables in the formula F.
-/
def Formula.boundVarSet : Formula → Finset Var
  | pred_ _ vs => vs.toFinset.biUnion Var.boundVarSet
  | not_ phi => phi.boundVarSet
  | imp_ phi psi => phi.boundVarSet ∪ psi.boundVarSet
  | forall_ phi => phi.boundVarSet


/--
  isBoundIn v F := True if and only if v is a bound variable in the formula F.
-/
def isBoundIn (v : Var) (F : Formula) : Prop :=
  v.isBound ∧ occursIn v F


/--
  Helper function for Formula.freeVarSet.
-/
def Var.freeVarSet : Var → Finset Var
  | F x => {F x}
  | B _ => ∅


/--
  Formula.freeVarSet F := The set of all of the free variables in the formula F.
-/
def Formula.freeVarSet : Formula → Finset Var
  | pred_ _ vs => vs.toFinset.biUnion Var.freeVarSet
  | not_ phi => phi.freeVarSet
  | imp_ phi psi => phi.freeVarSet ∪ psi.freeVarSet
  | forall_ phi => phi.freeVarSet


/--
  isFreeIn v F := True if and only if v is a free variable in the formula F.
-/
def isFreeIn (v : Var) (F : Formula) : Prop :=
  v.isFree ∧ occursIn v F


/--
  Formula.closed F := True if and only if the formula F contains no free variables.
-/
def Formula.closed (F : Formula) : Prop :=
  F.freeVarSet = ∅


--------------------------------------------------

-- Single

/--
  Helper function for openFormulaAux.

  v is intended to be a free variable.
-/
def openVar
  (k : ℕ)
  (v : Var) :
  Var → Var
  | F x => F x
  | B i => if i = k then v else B i


/--
  Helper function for openFormula.

  v is intended to be a free variable.
-/
def openFormulaAux
  (k : ℕ)
  (v : Var) :
  Formula → Formula
  | pred_ X vs => pred_ X (vs.map (openVar k v))
  | not_ phi => not_ (openFormulaAux k v phi)
  | imp_ phi psi => imp_ (openFormulaAux k v phi) (openFormulaAux k v psi)
  | forall_ phi => forall_ (openFormulaAux (k + 1) v phi)


/--
  openFormula v F := Each of the bound variables in the formula F that has an index equal to the number of binders that it is under is replaced by the variable v. This means that each bound variable that is replaced by v has an index out of scope by exactly one.

  v is intended to be a free variable.
-/
def openFormula
  (v : Var)
  (F : Formula) :
  Formula :=
  openFormulaAux 0 v F


-- Multiple

/--
  Helper function for openFormulaListAux.

  This is a multiple variable version of openVar.

  zs is intended to be an array of free variables.
-/
def openVarList
  (k : Nat)
  (zs : Array Var) :
  Var → Var
  | F x => F x
  | B i =>
    if i < k
    -- i is in scope
    then B i
    else
    -- i is out of scope
      -- ¬ i < k -> i >= k -> i - k >= 0 -> 0 <= i - k
      if _ : i - k < zs.size
      -- 0 <= i - k < zs.size
      then zs[i - k]
      -- The index of each of the remaining out of scope bound variables is shifted to account for the removal of the zs.size number of out of scope variables that have been removed.
      -- ¬ i - k < zs.size -> i - k >= zs.size -> i >= zs.size + k -> i - zs.size >= k. Since k >= 0 then i - zs.size >= 0.
      else B (i - zs.size)


/--
  Helper function for openFormulaList.

  This is a multiple variable version of openFormulaAux.

  zs is intended to be an array of free variables.
-/
def openFormulaListAux
  (k : Nat)
  (zs : Array Var) :
  Formula → Formula
  | pred_ X vs => pred_ X (vs.map (openVarList k zs))
  | not_ phi => not_ (openFormulaListAux k zs phi)
  | imp_ phi psi => imp_ (openFormulaListAux k zs phi) (openFormulaListAux k zs psi)
  | forall_ phi => forall_ (openFormulaListAux (k + 1) zs phi)


/--
  This is a multiple variable version of openFormula.

  Let B i be a bound variable in F. Let k be the number of binders that it is under. Then

  i < k : B i -> B i
  k <= i < k + zs.size : B i -> zs[i - k]
  k + zs.size <= i : B i -> B (i - zs.size)

  zs is intended to be an array of free variables.
-/
def openFormulaList
  (zs : Array Var)
  (F : Formula) :
  Formula :=
  openFormulaListAux 0 zs F


--------------------------------------------------


/--
  Helper function for closeFormulaAux.

  v is intended to be a free variable.
-/
def closeVar
  (v : Var)
  (k : ℕ) :
  Var → Var
  | F x => if v = F x then B k else F x
  | B i => B i


/--
  Helper function for closeFormula.

  v is intended to be a free variable.
-/
def closeFormulaAux
  (v : Var)
  (k : ℕ) :
  Formula → Formula
  | pred_ X vs => pred_ X (vs.map (closeVar v k))
  | not_ phi => not_ (closeFormulaAux v k phi)
  | imp_ phi psi => imp_ (closeFormulaAux v k phi) (closeFormulaAux v k psi)
  | forall_ phi => forall_ (closeFormulaAux v (k + 1) phi)


/--
  closeFormula v F := If v is a free variable then each occurence of v in the formula F is replaced by a bound variable that has an index equal to the number of binders that it is under. This means that each of the bound variables that an occurence of v is replaced by is given an index out of scope by exactly one.

  v is intended to be a free variable.
-/
def closeFormula
  (v : Var)
  (F : Formula) :
  Formula :=
  closeFormulaAux v 0 F


--------------------------------------------------


/--
  Formula.lc' F := True if and only if every bound variable in the formula F has an index less than the number of binders that it is under.
-/
inductive Formula.lc' : Formula → Prop
  | pred_
    (X : String)
    (vs : List Var) :
    (∀ (v : Var), v ∈ vs → v.isFree) →
    lc' (pred_ X vs)

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
    (v : Var) :
    v.isFree →
    lc' (openFormula v phi) →
    lc' (forall_ phi)


inductive Formula.lc : Formula → Prop
  | pred_
    (X : String)
    (vs : List Var) :
    (∀ (v : Var), v ∈ vs → v.isFree) →
    lc (pred_ X vs)

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
    (L : Finset Var) :
    (∀ (v : Var), v.isFree → v ∉ L → lc (openFormula v phi)) →
    lc (forall_ phi)


def Formula.body (F : Formula) : Prop :=
  ∃ (L : Finset Var), ∀ (v : Var), v.isFree → v ∉ L → Formula.lc (openFormula v F)


--------------------------------------------------


/--
  Helper function for Formula.lc_at.
-/
def Var.lc_at
  (k : ℕ) :
  Var → Prop
  | F _ => True
  | B i => i < k

instance
  (k : ℕ) (v : Var) :
  Decidable (Var.lc_at k v) :=
  by
  cases v
  all_goals
    simp only [lc_at]
    infer_instance


/--
  Formula.lc_at k F := True if and only if every bound variable in the formula F has an index less than the number of binders that it is under plus k. If k is 0 then this is equivalent to being locally closed.
-/
def Formula.lc_at
  (k : ℕ) :
  Formula → Prop
  | pred_ _ vs => ∀ (v : Var), v ∈ vs → (v.lc_at k)
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


--------------------------------------------------


structure Interpretation (D : Type) : Type :=
  (nonempty_ : Nonempty D)
  (pred_ : String → (List D → Prop))


def VarAssignment (D : Type) : Type := Var → D


def shift
  (D : Type)
  (V : VarAssignment D)
  (d : D) :
  VarAssignment D
  | F x => V (F x)
  | B 0 => d
  | B (i + 1) => V (B i)


def Holds
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D) :
  Formula → Prop
  | pred_ X vs => I.pred_ X (vs.map V)
  | not_ phi => ¬ Holds D I V phi
  | imp_ phi psi => Holds D I V phi → Holds D I V psi
  | forall_ phi => ∀ (d : D), Holds D I (shift D V d) phi


--------------------------------------------------


def Var.sub (σ : Var → Var) : Var → Var
  | F x => σ (F x)
  | B i => B i


def Formula.sub (σ : Var → Var) : Formula → Formula
  | pred_ X xs => pred_ X (xs.map (Var.sub σ))
  | not_ phi => not_ (phi.sub σ)
  | imp_ phi psi => imp_ (phi.sub σ) (psi.sub σ)
  | forall_ phi => forall_ (phi.sub σ)


--------------------------------------------------


def Interpretation.subPred
  (D : Type)
  (I : Interpretation D)
  (pred_ : String → List D → Prop) :
  Interpretation D := {
    nonempty_ := I.nonempty_
    pred_ := pred_ }


def VarAssignment.subN_aux
  (D : Type)
  (f : ℕ → D) :
  List D → ℕ → D
  | [], n => f n
  | d :: _, 0 => d
  | _ :: ds, n + 1 => subN_aux D f ds n


def VarAssignment.subN
  (D : Type)
  (V : VarAssignment D)
  (ds : List D) :
  VarAssignment D
  | F a => V (F a)
  | B n => subN_aux D (V ∘ B) ds n


def Var.isLessThan (n : Nat) : Var → Prop
  | F _ => True
  | B i => i < n

instance (n : ℕ) (v : Var) : Decidable (Var.isLessThan n v) :=
  by
  cases v
  case F x =>
    simp only [Var.isLessThan]
    exact decidableTrue
  case B i =>
    simp only [Var.isLessThan]
    exact Nat.decLt i n


def Formula.isLessThan (n : Nat) : Formula → Prop
  | pred_ _ vs => vs.all (fun (v : Var) => (Var.isLessThan n v))
  | not_ phi => phi.isLessThan n
  | imp_ phi psi => phi.isLessThan n ∧ psi.isLessThan n
  | forall_ phi => phi.isLessThan (n + 1)


--------------------------------------------------


lemma IsFreeIffExistsString
  (v : Var) :
  v.isFree ↔ ∃ (x : String), v = F x :=
  by
  cases v
  case F x =>
    simp only [isFree]
    simp
  case B i =>
    simp only [isFree]
    simp


--------------------------------------------------


lemma CloseVarOpenVarComp
  (v : Var)
  (x : Var)
  (k : ℕ)
  (h1 : x ∉ Var.freeVarSet v)
  (h2 : x.isFree) :
  (closeVar x k ∘ openVar k x) v = v :=
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
    simp only [IsFreeIffExistsString] at h2
    apply Exists.elim h2
    intro a a1
    subst a1

    simp
    simp only [openVar]
    split_ifs
    case _ c1 =>
      simp only [closeVar]
      simp
      simp only [c1]
    case _ c1 =>
      simp only [closeVar]


lemma OpenVarCloseVarComp
  (v : Var)
  (x : Var)
  (k : ℕ)
  (h1 : Var.lc_at k v)
  (h2 : x.isFree) :
  (openVar k x ∘ closeVar x k) v = v :=
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
  (x : Var)
  (h1 : x ∉ F.freeVarSet)
  (h2 : x.isFree) :
  (closeFormulaAux x k ∘ openFormulaAux k x) F = F :=
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
    · exact h1 v a1
    · exact h2
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
  (x : Var)
  (h1 : Formula.lc_at k F)
  (h2 : x.isFree) :
  (openFormulaAux k x ∘ closeFormulaAux x k) F = F :=
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
    · exact h1 v a1
    · exact h2
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
  (x : Var)
  (k : ℕ)
  (h1 : x.isFree) :
  Set.LeftInvOn (closeVar x k) (openVar k x) {v | x ∉ v.freeVarSet} :=
  by
  simp only [Set.LeftInvOn]
  simp
  intro v a1
  exact CloseVarOpenVarComp v x k a1 h1

lemma CloseVarLeftInvOn
  (x : Var)
  (k : ℕ)
  (h1 : x.isFree) :
  Set.LeftInvOn (openVar k x) (closeVar x k) {v | Var.lc_at k v} :=
  by
  simp only [Set.LeftInvOn]
  simp
  intro v a1
  exact OpenVarCloseVarComp v x k a1 h1


lemma OpenVarInjOn
  (x : Var)
  (k : ℕ)
  (h1 : x.isFree) :
  Set.InjOn (openVar k x) {v | x ∉ v.freeVarSet} :=
  by
  apply Set.LeftInvOn.injOn
  exact OpenVarLeftInvOn x k h1

lemma CloseVarInjOn
  (x : Var)
  (k : ℕ)
  (h1 : x.isFree) :
  Set.InjOn (closeVar x k) {v | Var.lc_at k v} :=
  by
  apply Set.LeftInvOn.injOn
  apply CloseVarLeftInvOn x k h1


lemma OpenFormulaLeftInvOn
  (x : Var)
  (k : ℕ)
  (h1 : x.isFree) :
  Set.LeftInvOn (closeFormulaAux x k) (openFormulaAux k x) {F | x ∉ F.freeVarSet} :=
  by
  simp only [Set.LeftInvOn]
  simp
  intro F a1
  apply CloseFormulaOpenFormulaComp
  · exact a1
  · exact h1

lemma CloseFormulaLeftInvOn
  (x : Var)
  (k : ℕ)
  (h1 : x.isFree) :
  Set.LeftInvOn (openFormulaAux k x) (closeFormulaAux x k) {F | Formula.lc_at k F} :=
  by
  simp only [Set.LeftInvOn]
  simp
  intro F a1
  apply OpenFormulaCloseFormulaComp
  · exact a1
  · exact h1


lemma OpenFormulaInjOn
  (x : Var)
  (k : ℕ)
  (h1 : x.isFree) :
  Set.InjOn (openFormulaAux k x) {F | x ∉ F.freeVarSet} :=
  by
  apply Set.LeftInvOn.injOn
  exact OpenFormulaLeftInvOn x k h1

lemma CloseFormulaInjOn
  (x : Var)
  (k : ℕ)
  (h1 : x.isFree) :
  Set.InjOn (closeFormulaAux x k) {F | Formula.lc_at k F} :=
  by
  apply Set.LeftInvOn.injOn
  exact CloseFormulaLeftInvOn x k h1


example
  (F G : Formula)
  (x : Var)
  (k : ℕ)
  (h0 : x.isFree)
  (h1 : x ∉ F.freeVarSet)
  (h2 : x ∉ G.freeVarSet)
  (h3 : openFormulaAux k x F = openFormulaAux k x G) :
  F = G :=
  by
  apply OpenFormulaInjOn
  · exact h0
  · simp
    exact h1
  · simp
    exact h2
  · exact h3


--------------------------------------------------


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


theorem HoldsIffSubHoldsAux
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (F : Formula)
  (σ' : String → String)
  (h1 : ∀ (v : Var), v.isFree → V v = V' (Var.sub σ' v))
  (h2 : ∀ (v : Var), v.isBound → V v = V' v) :
  Holds D I V F ↔ Holds D I V' (sub σ' F) :=
  by
  induction F generalizing V V'
  case pred_ X xs =>
    simp only [Formula.sub]
    simp only [Holds]
    simp
    congr! 1
    simp only [List.map_eq_map_iff]
    intro v a1
    simp
    cases v
    case _ a =>
      simp only [Var.sub]
      apply h1
      simp only [Var.isFree]
    case _ n =>
      simp only [Var.sub]
      apply h2
      simp only [isBound]
  case not_ phi phi_ih =>
    simp only [Formula.sub]
    simp only [Holds]
    congr! 1
    exact phi_ih V V' h1 h2
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.sub]
    simp only [Holds]
    congr! 1
    · exact phi_ih V V' h1 h2
    · exact psi_ih V V' h1 h2
  case forall_ phi phi_ih =>
    simp only [Formula.sub]
    simp only [Holds]
    apply forall_congr'
    intro d
    apply phi_ih 
    · intro v a1
      specialize h1 v a1
      cases v
      case _ a =>
        simp only [Var.sub] at h1

        simp only [Var.sub]
        simp only [shift]
        exact h1
      case _ n =>
        simp only [isFree] at a1
    · intro v a1
      cases v
      case _ a =>
        simp only [isBound] at a1
      case _ n =>
        cases n
        case zero =>
          simp only [shift]
        case succ n =>
          simp only [shift]
          apply h2
          simp only [isBound]


theorem substitution_fun_theorem
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (σ : String → String)
  (F : Formula) :
  Holds D I (V ∘ (Var.sub σ)) F ↔
    Holds D I V (sub σ F) :=
  by
  apply HoldsIffSubHoldsAux D I (V ∘ (Var.sub σ)) V F σ
  · simp
  · intro v a1
    cases v
    case _ a =>
      simp only [isBound] at a1
    case _ n =>
      cases n
      case zero =>
        simp
        simp only [Var.sub]
      case succ n =>
        simp
        simp only [Var.sub]


theorem HoldsIffSubHoldsAux'
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (F : Formula)
  (σ' : Var → Var)
  (h1 : ∀ (v : Var), v.isFree → V v = V' (Var.sub' σ' v))
  (h2 : ∀ (v : Var), v.isBound → V v = V' v)
  (h3 : ∀ (v : Var), v.isFree → (σ' v).isFree) :
  Holds D I V F ↔ Holds D I V' (sub' σ' F) :=
  by
  induction F generalizing V V'
  case pred_ X xs =>
    simp only [Formula.sub']
    simp only [Holds]
    simp
    congr! 1
    simp only [List.map_eq_map_iff]
    intro v a1
    simp
    cases v
    case _ a =>
      simp only [Var.sub']
      apply h1
      simp only [Var.isFree]
    case _ n =>
      simp only [Var.sub']
      apply h2
      simp only [isBound]
  case not_ phi phi_ih =>
    simp only [Formula.sub']
    simp only [Holds]
    congr! 1
    exact phi_ih V V' h1 h2
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.sub']
    simp only [Holds]
    congr! 1
    · exact phi_ih V V' h1 h2
    · exact psi_ih V V' h1 h2
  case forall_ phi phi_ih =>
    simp only [Formula.sub']
    simp only [Holds]
    apply forall_congr'
    intro d
    apply phi_ih
    · intro v a1
      specialize h1 v a1
      cases v
      case _ a =>
        simp only [Var.sub'] at h1

        obtain s1 := h3 (F a) a1
        simp only [IsFreeIffExistsString] at s1
        apply Exists.elim s1
        intro a' a2

        simp only [Var.sub']
        simp only [a2]
        simp only [shift]
        simp only [h1]
        simp only [a2]
      case _ n =>
        simp only [isFree] at a1
    · intro v a1
      cases v
      case _ a =>
        simp only [isBound] at a1
      case _ n =>
        cases n
        case zero =>
          simp only [shift]
        case succ n =>
          simp only [shift]
          apply h2
          simp only [isBound]


theorem substitution_fun_theorem'
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (σ : Var → Var)
  (F : Formula)
  (h1 : ∀ (v : Var), isFree v → isFree (σ v)) :
  Holds D I (V ∘ (Var.sub' σ)) F ↔
    Holds D I V (sub' σ F) :=
  by
  apply HoldsIffSubHoldsAux' D I (V ∘ (Var.sub' σ)) V F σ
  · simp
  · intro v a1
    cases v
    case _ a =>
      simp only [isBound] at a1
    case _ n =>
      cases n
      case zero =>
        simp
        simp only [Var.sub']
      case succ n =>
        simp
        simp only [Var.sub']
  · exact h1


theorem HoldsIffSubHolds'
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (σ : Var → Var)
  (F : Formula)
  (h1 : ∀ (v : Var), isFree v → isFree (σ v)) :
  Holds D I (V ∘ (Var.sub' σ)) F ↔
    Holds D I V (sub' σ F) :=
  by
  induction F generalizing V
  case pred_ X xs =>
    simp only [Formula.sub']
    simp only [Holds]
    congr! 1
    simp
  case not_ phi phi_ih =>
    simp only [Formula.sub']
    simp only [Holds]
    congr! 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.sub']
    simp only [Holds]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ phi phi_ih =>
    simp only [Formula.sub']
    simp only [Holds]
    apply forall_congr'
    intro d
    simp only [← phi_ih]
    congr!
    funext v
    simp
    cases v
    case _ a =>
      have s1 : isFree (F a)
      simp only [isFree]

      specialize h1 (F a) s1
      simp only [IsFreeIffExistsString] at h1
      apply Exists.elim h1
      intro a' a1
      simp only [Var.sub']
      simp only [shift]
      simp
      simp only [a1]
    case _ n =>
      cases n
      case zero =>
        simp only [Var.sub']
        simp only [shift]
      case succ n =>
        simp only [Var.sub']
        simp only [shift]
        simp


theorem extracted_1
  (D : Type)
  (x : String)
  (V : VarAssignment D)
  (k : ℕ)
  (d : D) :
  shift D (V ∘ openVar k x) d =
    shift D V d ∘ openVar (k + 1) x :=
  by
  funext v
  simp
  cases v
  case _ a =>
    simp only [openVar]
    simp only [shift]
    simp
  case _ n =>
    cases n
    case zero =>
      simp only [openVar]
      simp only [shift]
      simp
    case succ n =>
      simp only [openVar]
      simp only [shift]
      simp
      split
      case _ c1 =>
        simp
      case _ c1 =>
        simp


example
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (F : Formula)
  (x : String)
  (k : Nat) :
  Holds D I (V ∘ openVar k x) F ↔
    Holds D I V (openFormulaAux k x F) :=
  by
  induction F generalizing V k
  case pred_ X xs =>
    simp only [openFormulaAux]
    simp only [Holds]
    simp
  case not_ phi phi_ih =>
    simp only [openFormulaAux]
    simp only [Holds]
    congr! 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [openFormulaAux]
    simp only [Holds]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ phi phi_ih =>
    simp only [openFormulaAux]
    simp only [Holds]
    apply forall_congr'
    intro d
    simp only [<- phi_ih]
    congr! 1
    apply extracted_1


theorem extracted_2
  (D : Type)
  (zs : Array String)
  (V : VarAssignment D)
  (k : ℕ)
  (d : D) :
  shift D (V ∘ Var.instantiate zs k) d = shift D V d ∘ Var.instantiate zs (k + 1) :=
  by
  funext v
  simp
  cases v
  case _ a =>
    simp only [Var.instantiate]
    simp only [shift]
    simp
  case _ n =>
    simp only [Var.instantiate]
    simp only [shift]
    simp
    cases n
    case zero =>
      simp
    case succ n =>
      simp
      split
      case _ c1 =>
        have s1 : n + 1 < k + 1
        exact Nat.add_lt_add_right c1 1
        simp only [if_pos s1]

      case _ c1 =>
        have s1 : ¬ n + 1 < k + 1
        intro contra
        apply c1
        exact Nat.succ_lt_succ_iff.mp contra

        split
        case _ c2 =>
          simp
        case _ c2 =>
          simp


example
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (zs : Array String)
  (k : Nat)
  (F : Formula) :
  Holds D I (V ∘ Var.instantiate zs k) F ↔
    Holds D I V (Formula.instantiate zs k F) :=
  by
  induction F generalizing V k
  case pred_ X xs =>
    simp only [Formula.instantiate]
    simp only [Holds]
    simp
  case not_ phi phi_ih =>
    simp only [Formula.instantiate]
    simp only [Holds]
    congr! 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.instantiate]
    simp only [Holds]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ phi phi_ih =>
    simp only [Formula.instantiate]
    simp only [Holds]
    apply forall_congr'
    intro d
    simp only [← phi_ih]
    congr! 1
    apply extracted_2


--------------------------------------------------




theorem extracted_3
  (D : Type)
  (V : VarAssignment D)
  (k : ℕ)
  (zs : Array Var)
  (d : D)
  (h1 : ∀ (z : Var), z ∈ zs.data → z.isFree) :
  shift D (V ∘ Var.instantiate' k zs) d = shift D V d ∘ Var.instantiate' (k + 1) zs :=
  by
  funext v
  simp
  cases v
  case _ a =>
    simp only [Var.instantiate']
    simp only [shift]
    simp
  case _ n =>
    simp only [Var.instantiate']
    simp only [shift]
    simp
    cases n
    case zero =>
      simp
    case succ n =>
      simp
      split
      case _ c1 =>
        have s1 : n + 1 < k + 1
        exact Nat.add_lt_add_right c1 1
        simp only [if_pos s1]

      case _ c1 =>
        have s1 : ¬ n + 1 < k + 1
        intro contra
        apply c1
        exact Nat.succ_lt_succ_iff.mp contra

        split
        case _ c2 =>
          specialize h1 (zs[n - k])
          have s1 : zs[n - k] ∈ zs.data
          apply Array.getElem_mem_data

          specialize h1 s1
          obtain s2 := IsFreeImpExistsString (zs[n - k]) h1
          apply Exists.elim s2
          intro a a1
          simp only [a1]
        case _ c2 =>
          simp


theorem SubHolds
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (k : Nat)
  (zs : Array Var)
  (F : Formula)
  (h1 : ∀ (z : Var), z ∈ zs.data → z.isFree) :
  Holds D I (V ∘ Var.instantiate' k zs) F ↔
    Holds D I V (Formula.instantiate' k zs F) :=
  by
  induction F generalizing V k
  case pred_ X xs =>
    simp only [Formula.instantiate']
    simp only [Holds]
    simp
  case not_ phi phi_ih =>
    simp only [Formula.instantiate']
    simp only [Holds]
    congr! 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.instantiate']
    simp only [Holds]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ phi phi_ih =>
    simp only [Formula.instantiate']
    simp only [Holds]
    apply forall_congr'
    intro d
    simp only [← phi_ih]
    congr! 1
    exact extracted_3 D V k zs d h1




lemma OpenFormulaLengthAux'
  (F : Formula)
  (v : Var)
  (k : ℕ) :
  length (openFormulaAux' k v F) = length F :=
  by
  induction F generalizing k
  case pred_ X xs =>
    simp only [openFormulaAux']
    simp only [Formula.length]
  case not_ phi phi_ih =>
    simp only [openFormulaAux']
    simp only [Formula.length]
    simp
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [openFormulaAux']
    simp only [Formula.length]
    congr! 1
    · simp
      apply phi_ih
    · apply psi_ih
  case forall_ phi phi_ih =>
    simp only [openFormulaAux']
    simp only [Formula.length]
    simp
    apply phi_ih


lemma OpenFormulaLength'
  (F : Formula)
  (v : Var) :
  length (openFormula' v F) = length F :=
  OpenFormulaLengthAux' F v 0

--------------------------------------------------



theorem extracted_4
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (F : Formula)
  (k : ℕ)
  (vs : List Var)
  (h1 : ∀ (v : Var), v ∈ F.varSet → isFree v)
  (h2 : ∀ (v : Var), v ∈ vs → isFree v)
  (h3 : ∀ (v : Var), v ∈ F.varSet → isFree v → V v = V' v)  :
  Holds D I V' F ↔ Holds D I (V ∘ Var.instantiate' k (List.toArray vs)) F :=
  by
  induction F generalizing k V V'
  case pred_ X xs =>
    simp only [varSet] at h1
    simp at h1

    simp only [Holds]
    congr! 1
    simp only [List.map_eq_map_iff]
    intro v a1
    specialize h1 v a1
    obtain s1 := IsFreeImpExistsString v h1
    apply Exists.elim s1
    intro a a2
    subst a2
    simp
    simp only [Var.instantiate']
    simp only [varSet] at h3
    simp at h3
    symm
    apply h3
    exact a1
    exact h1
  case forall_ phi phi_ih =>
    simp only [varSet] at h1
    simp only [varSet] at h3
    simp only [Holds]
    apply forall_congr'
    intro d
    specialize phi_ih (shift D V d) (shift D V' d) (k + 1) h1
    rw [extracted_3]
    apply phi_ih
    intro v a1 a2
    obtain s1 := IsFreeImpExistsString v a2
    apply Exists.elim s1
    intro a a3
    subst a3
    simp only [shift]
    apply h3
    · exact a1
    · simp only [isFree]
    · simp
      exact h2
  all_goals
    sorry


theorem predSub_aux
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (τ : String → ℕ → Formula)
  (F : Formula)
  (h1 : ∀ (v : Var), v ∈ F.varSet → v.isFree)
  (h2 : ∀ (X : String) (n : ℕ) (v : Var), v ∈ (τ X n).varSet → v.isFree)
  (h3 : ∀ (X : String) (n : ℕ) (v : Var), v ∈ varSet (τ X n) → isFree v → V v = V' v)
  :
  Holds D ⟨ 
      I.nonempty_,
      fun (X : String) (ds : List D) =>
        Holds D I V' (τ X ds.length)
      ⟩  V F ↔ Holds D I V (F.predSub τ) :=
  by
  induction F generalizing V V'
  case pred_ X xs =>
    simp only [varSet] at h1
    simp at h1

    simp only [predSub]
    simp only [Holds]
    obtain s1 := SubHolds D I V 0 xs.toArray (τ X (List.length xs))
    simp at s1
    simp only [<- s1 h1]
    clear s1
    simp

    apply extracted_4
    specialize h2 X (xs.length)
    exact h2
    exact h1
    intro v a1 a2
    apply h3 X (xs.length)
    exact a1
    exact a2
  case forall_ phi phi_ih =>
    simp only [varSet] at h1
    simp only [predSub]
    simp only [Holds]
    apply forall_congr'
    intro d
    specialize phi_ih (shift D V d) V' h1
    have s1 : (∀ (X : String) (n : ℕ) (v : Var), v ∈ varSet (τ X n) → isFree v → shift D V d v = V' v)
    intro X n v a1 a2
    obtain s2 := IsFreeImpExistsString v a2
    apply Exists.elim s2
    intro a a3
    subst a3
    simp only [shift]
    apply h3 X n
    exact a1
    exact a2
    specialize phi_ih s1
    simp only [phi_ih]
  all_goals
    sorry



theorem predSub_aux'
  {D : Type}
  (I : Interpretation D)
  (V : VarAssignment D)
  (τ : String → ℕ → Formula)
  (F : Formula)
  (h1 : ∀ (v : Var), v ∈ F.varSet → v.isFree) :
  Holds D I V (F.predSub τ) ↔
  Holds D (I.withPred fun P xs => Holds D I (V.subN xs) (τ P xs.length)) V F :=
sorry
