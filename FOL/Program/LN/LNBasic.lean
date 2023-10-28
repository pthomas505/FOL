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
| free_ : String → Var
| bound_ : ℕ → Var
  deriving Inhabited, DecidableEq

compile_inductive% Var

open Var

/--
  The string representation of locally nameless variables.
-/
def Var.toString : Var → String
  | free_ x => x
  | bound_ i => s! "{i}"

instance : ToString Var :=
  { toString := fun v => v.toString }


/--
  Var.isFree v := True if and only if v is a free variable.
-/
def Var.isFree : Var → Prop
  | free_ _ => True
  | bound_ _ => False

/--
  Var.isBound v := True if and only if v is a bound variable.
-/
def Var.isBound : Var → Prop
  | free_ _ => False
  | bound_ _ => True


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


--------------------------------------------------

-- Nat


/--
  Helper function for Formula.boundVarSet_Nat.
-/
def Var.boundVarSet_Nat : Var → Finset ℕ
  | free_ _ => ∅
  | bound_ i => {i}


/--
  Formula.boundVarSet_Nat F := The set of all of the bound variables in the formula F.
-/
def Formula.boundVarSet_Nat : Formula → Finset ℕ
  | pred_ _ vs => vs.toFinset.biUnion Var.boundVarSet_Nat
  | not_ phi => phi.boundVarSet_Nat
  | imp_ phi psi => phi.boundVarSet_Nat ∪ psi.boundVarSet_Nat
  | forall_ phi => phi.boundVarSet_Nat


def NatIsBoundInFormula (n : ℕ) (F : Formula) : Prop :=
  occursIn (bound_ n) F


-- Var


/--
  Helper function for Formula.boundVarSet_Var.
-/
def Var.boundVarSet_Var : Var → Finset Var
  | free_ _ => ∅
  | bound_ i => {bound_ i}


/--
  Formula.boundVarSet_Var F := The set of all of the bound variables in the formula F.
-/
def Formula.boundVarSet_Var : Formula → Finset Var
  | pred_ _ vs => vs.toFinset.biUnion Var.boundVarSet_Var
  | not_ phi => phi.boundVarSet_Var
  | imp_ phi psi => phi.boundVarSet_Var ∪ psi.boundVarSet_Var
  | forall_ phi => phi.boundVarSet_Var


/--
  isBoundIn_Var v F := True if and only if v is a bound variable in the formula F.
-/
def VarIsBoundInFormula (v : Var) (F : Formula) : Prop :=
  v.isBound ∧ occursIn v F


--------------------------------------------------


/--
  Helper function for Formula.freeVarSet_Str.
-/
def Var.freeVarSet_Str : Var → Finset String
  | free_ x => {x}
  | bound_ _ => ∅


/--
  Formula.freeVarSet_Str F := The set of all of the free variables in the formula F.
-/
def Formula.freeVarSet_Str : Formula → Finset String
  | pred_ _ vs => vs.toFinset.biUnion Var.freeVarSet_Str
  | not_ phi => phi.freeVarSet_Str
  | imp_ phi psi => phi.freeVarSet_Str ∪ psi.freeVarSet_Str
  | forall_ phi => phi.freeVarSet_Str


def StrIsFreeInFormula (v : String) (F : Formula) : Prop :=
  occursIn (free_ v) F


--------------------------------------------------

/--
  Helper function for Formula.freeVarSet_Var.
-/
def Var.freeVarSet_Var : Var → Finset Var
  | free_ x => {free_ x}
  | bound_ _ => ∅


/--
  Formula.freeVarSet_Var F := The set of all of the free variables in the formula F.
-/
def Formula.freeVarSet_Var : Formula → Finset Var
  | pred_ _ vs => vs.toFinset.biUnion Var.freeVarSet_Var
  | not_ phi => phi.freeVarSet_Var
  | imp_ phi psi => phi.freeVarSet_Var ∪ psi.freeVarSet_Var
  | forall_ phi => phi.freeVarSet_Var


/--
  VarIsFreeInFormula v F := True if and only if v is a free variable in the formula F.
-/
def VarIsFreeInFormula (v : Var) (F : Formula) : Prop :=
  v.isFree ∧ occursIn v F


/--
  Formula.closed F := True if and only if the formula F contains no free variables.
-/
def Formula.closed (F : Formula) : Prop :=
  F.freeVarSet_Var = ∅


--------------------------------------------------

-- Single

/--
  Helper function for openFormulaAux.

  v is intended to be a free variable.
-/
def openVar
  (k : ℕ)
  (v : String) :
  Var → Var
  | free_ x => free_ x
  | bound_ i => if i = k then free_ v else bound_ i


/--
  Helper function for openFormula.

  v is intended to be a free variable.
-/
def openFormulaAux
  (k : ℕ)
  (v : String) :
  Formula → Formula
  | pred_ X vs => pred_ X (vs.map (openVar k v))
  | not_ phi => not_ (openFormulaAux k v phi)
  | imp_ phi psi => imp_ (openFormulaAux k v phi) (openFormulaAux k v psi)
  | forall_ phi => forall_ (openFormulaAux (k + 1) v phi)


/--
  openFormula v F := Each of the bound variables in the formula F that has an index equal to the number of binders that it is under is replaced by the variable v. This means that v replaces each bound variable that has an index out of scope by exactly one.

  v is intended to be a free variable.
-/
def openFormula
  (v : String)
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
  (zs : Array String) :
  Var → Var
  | free_ x => free_ x
  | bound_ i =>
    if i < k
    -- i is in scope
    then bound_ i
    else
    -- i is out of scope
      -- ¬ i < k -> i >= k -> i - k >= 0 -> 0 <= i - k
      if _ : i - k < zs.size
      -- 0 <= i - k < zs.size
      then free_ zs[i - k]
      -- The index of each of the remaining out of scope bound variables is shifted to account for the removal of the zs.size number of out of scope indexes that have been removed.
      -- ¬ i - k < zs.size -> i - k >= zs.size -> i >= zs.size + k -> i - zs.size >= k. Since k >= 0 then i - zs.size >= 0.
      else bound_ (i - zs.size)


/--
  Helper function for openFormulaList.

  This is a multiple variable version of openFormulaAux.

  zs is intended to be an array of free variables.
-/
def openFormulaListAux
  (k : Nat)
  (zs : Array String) :
  Formula → Formula
  | pred_ X vs => pred_ X (vs.map (openVarList k zs))
  | not_ phi => not_ (openFormulaListAux k zs phi)
  | imp_ phi psi => imp_ (openFormulaListAux k zs phi) (openFormulaListAux k zs psi)
  | forall_ phi => forall_ (openFormulaListAux (k + 1) zs phi)


/--
  This is a multiple variable version of openFormula.

  Let B i be a bound variable in the formula F. Let k be the number of binders that an occurrence of B i is under. Then that occurrence of B i is changed according to:

  i < k : B i -> B i
  k <= i < k + zs.size : B i -> zs[i - k]
  k + zs.size <= i : B i -> B (i - zs.size)

  zs is intended to be an array of free variables.
-/
def openFormulaList
  (zs : Array String)
  (F : Formula) :
  Formula :=
  openFormulaListAux 0 zs F


--------------------------------------------------


/--
  Helper function for closeFormulaAux.

  v is intended to be a free variable.
-/
def closeVar
  (v : String)
  (k : ℕ) :
  Var → Var
  | free_ x => if v = x then bound_ k else free_ x
  | bound_ i => bound_ i


/--
  Helper function for closeFormula.

  v is intended to be a free variable.
-/
def closeFormulaAux
  (v : String)
  (k : ℕ) :
  Formula → Formula
  | pred_ X vs => pred_ X (vs.map (closeVar v k))
  | not_ phi => not_ (closeFormulaAux v k phi)
  | imp_ phi psi => imp_ (closeFormulaAux v k phi) (closeFormulaAux v k psi)
  | forall_ phi => forall_ (closeFormulaAux v (k + 1) phi)


/--
  closeFormula v F := If v is a free variable then each occurence of v in the formula F is replaced by a bound variable that has an index equal to the number of binders that it is under. This means that each occurence of v is replaced by a bound variable that has an index out of scope by exactly one.

  v is intended to be a free variable.
-/
def closeFormula
  (v : String)
  (F : Formula) :
  Formula :=
  closeFormulaAux v 0 F


--------------------------------------------------


/--
  This is an inductive definition of locally closed.

  Formula.lc' F := True if and only if every bound variable in the formula F has an index less than the number of binders that it is under. This means that no bound variable in the formula F is out of scope.
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
    (v : String) :
    lc' (openFormula v phi) →
    lc' (forall_ phi)


/--
  This is an alternative inductive definition of locally closed.
-/
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
    (∀ (v : String), free_ v ∉ L → lc (openFormula v phi)) →
    lc (forall_ phi)


def Formula.body (F : Formula) : Prop :=
  ∃ (L : Finset Var), ∀ (v : String), free_ v ∉ L → Formula.lc (openFormula v F)


--------------------------------------------------


/--
  Helper function for Formula.lc_at.
-/
def Var.lc_at
  (k : ℕ) :
  Var → Prop
  | free_ _ => True
  | bound_ i => i < k

instance
  (k : ℕ) (v : Var) :
  Decidable (Var.lc_at k v) :=
  by
  cases v
  all_goals
    simp only [lc_at]
    infer_instance


/--
  For k = 0 this is a recursive definition of locally closed.

  Formula.lc_at k F := True if and only if every bound variable in the formula F has an index less than the number of binders that it is under plus k. If this holds for k = 0 then this means that no bound variable in F is out of scope and hence that F is locally closed.
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


#eval Formula.lc_at 0 (forall_ (pred_ "X" [bound_ 0]))
#eval Formula.lc_at 0 (forall_ (pred_ "X" [bound_ 1]))


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
  | free_ x => V (free_ x)
  | bound_ 0 => d
  | bound_ (i + 1) => V (bound_ i)


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


def Var.sub_Var (σ : Var → Var) : Var → Var
  | free_ x => σ (free_ x)
  | bound_ i => bound_ i


def Formula.sub_Var (σ : Var → Var) : Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.sub_Var σ))
  | not_ phi => not_ (phi.sub_Var σ)
  | imp_ phi psi => imp_ (phi.sub_Var σ) (psi.sub_Var σ)
  | forall_ phi => forall_ (phi.sub_Var σ)


--------------------------------------------------


def Var.sub_Str (σ : String → String) : Var → Var
  | free_ x => free_ (σ x)
  | bound_ i => bound_ i


def Formula.sub_Str (σ : String → String) : Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.sub_Str σ))
  | not_ phi => not_ (phi.sub_Str σ)
  | imp_ phi psi => imp_ (phi.sub_Str σ) (psi.sub_Str σ)
  | forall_ phi => forall_ (phi.sub_Str σ)


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
  | free_ a => V (free_ a)
  | bound_ n => subN_aux D (V ∘ bound_) ds n


--------------------------------------------------


lemma IsFreeIffExistsString
  (v : Var) :
  v.isFree ↔ ∃ (x : String), v = free_ x :=
  by
  cases v
  case free_ x =>
    simp only [isFree]
    simp
  case bound_ i =>
    simp only [isFree]
    simp


--------------------------------------------------


lemma CloseVarOpenVarComp
  (v : Var)
  (y : String)
  (k : ℕ)
  (h1 : ¬ (free_ y) = v) :
  (closeVar y k ∘ openVar k y) v = v :=
  by
  cases v
  case free_ x =>
    simp at h1

    simp
    simp only [openVar]
    simp only [closeVar]
    simp
    simp only [h1]
  case bound_ i =>
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
  (k : ℕ)
  (y : String)
  (h1 : Var.lc_at k v) :
  (openVar k y ∘ closeVar y k) v = v :=
  by
  cases v
  case free_ x =>
    simp
    simp only [closeVar]
    split_ifs
    case pos c1 =>
      simp only [c1]
      simp only [openVar]
      simp
    case neg c1 =>
      simp only [openVar]
  case bound_ i =>
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
  (y : String)
  (k : ℕ)
  (h1 : ¬ occursIn (free_ y) F) :
  (closeFormulaAux y k ∘ openFormulaAux k y) F = F :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [occursIn] at h1

    simp
    unfold openFormulaAux
    unfold closeFormulaAux
    simp
    simp only [List.map_eq_self_iff]
    intro v a1
    apply CloseVarOpenVarComp
    intro contra
    simp only [← contra] at a1
    contradiction
  case not_ phi phi_ih =>
    simp only [occursIn] at h1

    simp at phi_ih

    simp
    unfold openFormulaAux
    unfold closeFormulaAux
    simp only [phi_ih k h1]
  case imp_ phi psi phi_ih psi_ih =>
    simp only [occursIn] at h1
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
    simp only [occursIn] at h1

    simp at phi_ih

    simp
    unfold openFormulaAux
    unfold closeFormulaAux
    congr
    exact phi_ih (k + 1) h1


lemma OpenFormulaCloseFormulaComp
  (F : Formula)
  (k : ℕ)
  (y : String)
  (h1 : Formula.lc_at k F) :
  (openFormulaAux k y ∘ closeFormulaAux y k) F = F :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [Formula.lc_at] at h1

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
  (k : ℕ)
  (y : String) :
  Set.LeftInvOn (closeVar y k) (openVar k y) {v | y ∉ v.freeVarSet_Str} :=
  by
  simp only [Set.LeftInvOn]
  simp
  intro v a1
  apply CloseVarOpenVarComp v y k


lemma CloseVarLeftInvOn
  (y : String)
  (k : ℕ) :
  Set.LeftInvOn (openVar k y) (closeVar y k) {v | Var.lc_at k v} :=
  by
  simp only [Set.LeftInvOn]
  simp
  intro v a1
  exact OpenVarCloseVarComp v k y a1


lemma OpenVarInjOn
  (k : ℕ)
  (y : String) :
  Set.InjOn (openVar k y) {v | y ∉ v.freeVarSet} :=
  by
  apply Set.LeftInvOn.injOn
  exact OpenVarLeftInvOn k y


lemma CloseVarInjOn
  (y : String)
  (k : ℕ) :
  Set.InjOn (closeVar y k) {v | Var.lc_at k v} :=
  by
  apply Set.LeftInvOn.injOn
  apply CloseVarLeftInvOn y k


lemma OpenFormulaLeftInvOn
  (k : ℕ)
  (y : String) :
  Set.LeftInvOn (closeFormulaAux y k) (openFormulaAux k y) {F | y ∉ F.freeVarSet_Str} :=
  by
  simp only [Set.LeftInvOn]
  simp
  intro F a1
  apply CloseFormulaOpenFormulaComp
  exact a1


lemma CloseFormulaLeftInvOn
  (y : String)
  (k : ℕ) :
  Set.LeftInvOn (openFormulaAux k y) (closeFormulaAux y k) {F | Formula.lc_at k F} :=
  by
  simp only [Set.LeftInvOn]
  simp
  intro F a1
  apply OpenFormulaCloseFormulaComp
  · exact a1


lemma OpenFormulaInjOn
  (k : ℕ)
  (y : String) :
  Set.InjOn (openFormulaAux k y) {F | y ∉ F.freeVarSet} :=
  by
  apply Set.LeftInvOn.injOn
  exact OpenFormulaLeftInvOn k y


lemma CloseFormulaInjOn
  (y : String)
  (k : ℕ) :
  Set.InjOn (closeFormulaAux y k) {F | Formula.lc_at k F} :=
  by
  apply Set.LeftInvOn.injOn
  exact CloseFormulaLeftInvOn y k


example
  (F G : Formula)
  (k : ℕ)
  (y : String)
  (h1 : y ∉ F.freeVarSet)
  (h2 : y ∉ G.freeVarSet)
  (h3 : openFormulaAux k y F = openFormulaAux k y G) :
  F = G :=
  by
  apply OpenFormulaInjOn
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


--------------------------------------------------


lemma OpenVarFreeVarSet
  (v : Var)
  (k : ℕ)
  (y : String) :
  (openVar k y v).freeVarSet ⊆ v.freeVarSet ∪ {y} :=
  by
  cases v
  case F x =>
    simp only [openVar]
    simp only [Var.freeVarSet]
    simp
  case B i =>
    simp only [openVar]
    split
    case _ c1 =>
      simp only [Var.freeVarSet]
      simp
    case _ c1 =>
      simp only [Var.freeVarSet]
      simp


lemma CloseVarFreeVarSet
  (v : Var)
  (y : String)
  (k : ℕ) :
  (closeVar y k v).freeVarSet ⊆ v.freeVarSet \ {y} :=
  by
  cases v
  case F x =>
    simp only [closeVar]
    split
    case _ c1 =>
      simp only [Var.freeVarSet]
      simp
    case _ c1 =>
      simp only [Var.freeVarSet]
      simp
      exact ne_comm.mp c1
  case B i =>
    simp only [closeVar]
    simp only [Var.freeVarSet]
    simp


lemma OpenFormulaFreeVarSet
  (F : Formula)
  (k : ℕ)
  (y : String) :
  (openFormulaAux k y F).freeVarSet ⊆ F.freeVarSet ∪ {y} :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [openFormulaAux]
    simp only [Formula.freeVarSet]
    simp
    intro v a1
    trans (Var.freeVarSet v ∪ {y})
    · exact OpenVarFreeVarSet v k y
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


lemma CloseFormulaFreeVarSet
  (F : Formula)
  (y : String)
  (k : ℕ) :
  (closeFormulaAux y k F).freeVarSet ⊆ F.freeVarSet \ {y} :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [closeFormulaAux]
    simp only [Formula.freeVarSet]
    simp
    intro v a1
    trans (v.freeVarSet \ {y})
    · exact CloseVarFreeVarSet v y k
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


--------------------------------------------------


lemma SubOpenVar
  (v : Var)
  (σ : String → String)
  (k : ℕ)
  (y : String)
  (h1 : σ y = y) :
  Var.sub σ (openVar k y v) = openVar k y (Var.sub σ v) :=
  by
  cases v
  case F x =>
    simp only [openVar]
    simp only [Var.sub]
  case B i =>
    simp only [openVar]
    split
    case _ c1 =>
      simp only [Var.sub]
      simp only [if_pos c1]
      simp only [h1]
    case _ c1 =>
      simp only [Var.sub]
      simp only [if_neg c1]


lemma SubCloseVar
  (v : Var)
  (σ : String → String)
  (u : Var)
  (k : ℕ)
  (h1 : σ u = u)
  (h2 : ∀ (y : Var), ¬ u = σ y)
  (h3 : u.isFree)
  (h4 : ∀ (v : Var), v.isFree → (σ v).isFree) :
  Var.sub σ (closeVar u k v) = closeVar u k (Var.sub σ v) :=
  by
  simp only [IsFreeIffExistsString] at h3
  apply Exists.elim h3
  intro y a1
  clear h3

  cases v
  case F x =>
    have s1 : isFree (F x)
    simp only [isFree]

    specialize h4 (F x) s1
    clear s1
    simp only [IsFreeIffExistsString] at h4
    apply Exists.elim h4
    intro x' a2
    clear h4

    simp only [closeVar]
    by_cases c1 : u = F x
    · subst c1
      simp only [Var.sub]
      simp only [h1]
      simp
    · simp only [if_neg c1]
      simp only [Var.sub]
      specialize h2 (F x)
      simp only [a2]
      simp only [← a2]
      simp only [if_neg h2]
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