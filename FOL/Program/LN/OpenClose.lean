import FOL.Program.LN.Binders
import FOL.Program.LN.LC
import FOL.Program.LN.Semantics
import FOL.List
import FOL.Tactics

set_option autoImplicit false


namespace LN

open Var Formula


-- Single

/--
  Helper function for openFormulaAux.

  v is intended to be a free variable.
-/
def openVar
  (k : ℕ)
  (v : Var) :
  Var → Var
  | free_ x => free_ x
  | bound_ i => if i = k then v else bound_ i


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
  | forall_ x phi => forall_ x (openFormulaAux (k + 1) v phi)


/--
  openFormula v F := Each of the bound variables in the formula F that has an index equal to the number of binders that it is under is replaced by the variable v. This means that v replaces each bound variable that has an index out of scope by exactly one.

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
  (zs : List Var) :
  Var → Var
  | free_ x => free_ x
  | bound_ i =>
    if i < k
    -- i is in scope
    then bound_ i
    else
    -- i is out of scope
      -- ¬ i < k -> i >= k -> i - k >= 0 -> 0 <= i - k
      if _ : i - k < zs.length
      -- 0 <= i - k < zs.length
      then zs[i - k]
      -- The index of each of the remaining out of scope bound variables is reduced to account for the zs.length number of out of scope indexes that have been removed.
      -- ¬ i - k < zs.length -> i - k >= zs.length -> i >= zs.length + k -> i - zs.length >= k. Since k >= 0 then i - zs.length >= 0.
      else bound_ (i - zs.length)


/--
  Helper function for openFormulaList.

  This is a multiple variable version of openFormulaAux.

  zs is intended to be an array of free variables.
-/
def openFormulaListAux
  (k : Nat)
  (zs : List Var) :
  Formula → Formula
  | pred_ X vs => pred_ X (vs.map (openVarList k zs))
  | not_ phi => not_ (openFormulaListAux k zs phi)
  | imp_ phi psi => imp_ (openFormulaListAux k zs phi) (openFormulaListAux k zs psi)
  | forall_ x phi => forall_ x (openFormulaListAux (k + 1) zs phi)


/--
  This is a multiple variable version of openFormula.

  Let zs be an array of variables. Let (bound_ i) be a bound variable in the formula F. Let k be the number of binders that an occurrence of (bound_ i) is under. Then that occurrence of (bound_ i) is changed according to:

  i < k : (bound_ i) -> (bound_ i)
  k <= i < k + zs.size : (bound_ i) -> zs[i - k]
  k + zs.size <= i : (bound_ i) -> bound_ (i - zs.size)

  zs is intended to be an array of free variables.
-/
def openFormulaList
  (zs : List Var)
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
  | free_ x => if v = free_ x then bound_ k else free_ x
  | bound_ i => bound_ i


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
  | forall_ x phi => forall_ x (closeFormulaAux v (k + 1) phi)


/--
  closeFormula v F := If v is a free variable then each occurence of v in the formula F is replaced by a bound variable that has an index equal to the number of binders that it is under. This means that each occurence of v is replaced by a bound variable that has an index out of scope by exactly one.

  v is intended to be a free variable.
-/
def closeFormula
  (v : Var)
  (F : Formula) :
  Formula :=
  closeFormulaAux v 0 F

--------------------------------------------------

lemma CloseVarOpenVarComp
  (v : Var)
  (y : String)
  (k : ℕ)
  (h1 : ¬ free_ y = v) :
  (closeVar (free_ y) k ∘ openVar k (free_ y)) v = v :=
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
  (openVar k (free_ y) ∘ closeVar (free_ y) k) v = v :=
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
  (closeFormulaAux (free_ y) k ∘ openFormulaAux k (free_ y)) F = F :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [occursIn] at h1

    simp
    simp only [openFormulaAux]
    simp only [closeFormulaAux]
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
    simp only [openFormulaAux]
    simp only [closeFormulaAux]
    simp only [phi_ih k h1]
  case imp_ phi psi phi_ih psi_ih =>
    simp only [occursIn] at h1
    push_neg at h1

    simp at phi_ih

    simp
    simp only [openFormulaAux]
    simp only [closeFormulaAux]
    cases h1
    case _ h1_left h1_right =>
      congr
      · exact phi_ih k h1_left
      · exact psi_ih k h1_right
  case forall_ phi phi_ih =>
    simp only [occursIn] at h1

    simp at phi_ih

    simp
    simp only [openFormulaAux]
    simp only [closeFormulaAux]
    congr
    exact phi_ih (k + 1) h1


lemma OpenFormulaCloseFormulaComp
  (F : Formula)
  (k : ℕ)
  (y : String)
  (h1 : Formula.lc_at k F) :
  (openFormulaAux k (free_ y) ∘ closeFormulaAux (free_ y) k) F = F :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [Formula.lc_at] at h1

    simp
    simp only [closeFormulaAux]
    simp only [openFormulaAux]
    simp
    simp only [List.map_eq_self_iff]
    intro v a1
    apply OpenVarCloseVarComp
    exact h1 v a1
  case not_ phi phi_ih =>
    simp only [Formula.lc_at] at h1

    simp at phi_ih

    simp
    simp only [closeFormulaAux]
    simp only [openFormulaAux]
    simp only [phi_ih k h1]
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.lc_at] at h1

    simp at phi_ih

    simp
    simp only [closeFormulaAux]
    simp only [openFormulaAux]
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

--------------------------------------------------

lemma OpenVarLeftInvOn
  (k : ℕ)
  (y : String) :
  Set.LeftInvOn (closeVar (free_ y) k) (openVar k (free_ y)) {v : Var | ¬ (free_ y) = v} :=
  by
  simp only [Set.LeftInvOn]
  simp
  intro v a1
  apply CloseVarOpenVarComp v y k a1


lemma CloseVarLeftInvOn
  (y : String)
  (k : ℕ) :
  Set.LeftInvOn (openVar k (free_ y)) (closeVar (free_ y) k) {v : Var | Var.lc_at k v} :=
  by
  simp only [Set.LeftInvOn]
  simp
  intro v a1
  exact OpenVarCloseVarComp v k y a1


lemma OpenVarInjOn
  (k : ℕ)
  (y : String) :
  Set.InjOn (openVar k (free_ y)) {v : Var | ¬ (free_ y) = v} :=
  by
  apply Set.LeftInvOn.injOn
  exact OpenVarLeftInvOn k y


lemma CloseVarInjOn
  (y : String)
  (k : ℕ) :
  Set.InjOn (closeVar (free_ y) k) {v : Var | Var.lc_at k v} :=
  by
  apply Set.LeftInvOn.injOn
  apply CloseVarLeftInvOn y k


lemma OpenFormulaLeftInvOn
  (k : ℕ)
  (y : String) :
  Set.LeftInvOn (closeFormulaAux (free_ y) k) (openFormulaAux k (free_ y)) {F : Formula | ¬ occursIn (free_ y) F} :=
  by
  simp only [Set.LeftInvOn]
  simp
  intro F a1
  apply CloseFormulaOpenFormulaComp
  exact a1


lemma CloseFormulaLeftInvOn
  (y : String)
  (k : ℕ) :
  Set.LeftInvOn (openFormulaAux k (free_ y)) (closeFormulaAux (free_ y) k) {F : Formula | Formula.lc_at k F} :=
  by
  simp only [Set.LeftInvOn]
  simp
  intro F a1
  apply OpenFormulaCloseFormulaComp
  exact a1


lemma OpenFormulaInjOn
  (k : ℕ)
  (y : String) :
  Set.InjOn (openFormulaAux k (free_ y)) {F : Formula | ¬ occursIn (free_ y) F} :=
  by
  apply Set.LeftInvOn.injOn
  exact OpenFormulaLeftInvOn k y


lemma CloseFormulaInjOn
  (y : String)
  (k : ℕ) :
  Set.InjOn (closeFormulaAux (free_ y) k) {F : Formula | Formula.lc_at k F} :=
  by
  apply Set.LeftInvOn.injOn
  exact CloseFormulaLeftInvOn y k


example
  (F G : Formula)
  (k : ℕ)
  (y : String)
  (h1 : ¬ occursIn (free_ y) F)
  (h2 : ¬ occursIn (free_ y) G)
  (h3 : openFormulaAux k (free_ y) F = openFormulaAux k (free_ y) G) :
  F = G :=
  by
  apply OpenFormulaInjOn
  · simp
    exact h1
  · simp
    exact h2
  · exact h3

--------------------------------------------------

lemma OpenVarFreeStringSet
  (v : Var)
  (k : ℕ)
  (y : String) :
  (openVar k (free_ y) v).freeStringSet ⊆ v.freeStringSet ∪ {y} :=
  by
  cases v
  case free_ x =>
    simp only [openVar]
    simp only [Var.freeStringSet]
    simp
  case bound_ i =>
    simp only [openVar]
    split
    case _ c1 =>
      simp only [Var.freeStringSet]
      simp
    case _ c1 =>
      simp only [Var.freeStringSet]
      simp


lemma CloseVarFreeStringSet
  (v : Var)
  (y : String)
  (k : ℕ) :
  (closeVar (free_ y) k v).freeStringSet ⊆ v.freeStringSet \ {y} :=
  by
  cases v
  case free_ x =>
    simp only [closeVar]
    split
    case _ c1 =>
      simp only [Var.freeStringSet]
      simp
    case _ c1 =>
      simp at c1
      simp only [Var.freeStringSet]
      simp
      exact ne_comm.mp c1
  case bound_ i =>
    simp only [closeVar]
    simp only [Var.freeStringSet]
    simp

--------------------------------------------------

lemma OpenVarFreeVarSet
  (v : Var)
  (k : ℕ)
  (y : String) :
  (openVar k (free_ y) v).freeVarSet ⊆ v.freeVarSet ∪ {free_ y} :=
  by
  cases v
  case free_ x =>
    simp only [openVar]
    simp only [Var.freeVarSet]
    simp
  case bound_ i =>
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
  (closeVar (free_ y) k v).freeVarSet ⊆ v.freeVarSet \ {free_ y} :=
  by
  cases v
  case free_ x =>
    simp only [closeVar]
    split
    case _ c1 =>
      simp only [Var.freeVarSet]
      simp
    case _ c1 =>
      simp only [Var.freeVarSet]
      simp
      simp at c1
      exact ne_comm.mp c1
  case bound_ i =>
    simp only [closeVar]
    simp only [Var.freeVarSet]
    simp


lemma OpenFormulaFreeVarSet
  (F : Formula)
  (k : ℕ)
  (y : String) :
  (openFormulaAux k (free_ y) F).freeVarSet ⊆ F.freeVarSet ∪ {free_ y} :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [openFormulaAux]
    simp only [Formula.freeVarSet]
    simp
    intro v a1
    trans (Var.freeVarSet v ∪ {free_ y})
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
  (closeFormulaAux (free_ y) k F).freeVarSet ⊆ F.freeVarSet \ {free_ y} :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [closeFormulaAux]
    simp only [Formula.freeVarSet]
    simp
    intro v a1
    trans (v.freeVarSet \ {free_ y})
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

lemma shift_openVar
  (D : Type)
  (V : VarAssignment D)
  (k : ℕ)
  (y : String)
  (d : D) :
  shift D (V ∘ openVar k (free_ y)) d =
    shift D V d ∘ openVar (k + 1) (free_ y) :=
  by
  funext v
  simp
  cases v
  case _ x =>
    simp only [openVar]
    simp only [shift]
    simp
  case _ i =>
    cases i
    case zero =>
      simp only [openVar]
      simp only [shift]
      rfl
    case succ i =>
      simp only [openVar]
      simp only [shift]
      simp
      split
      case _ c1 =>
        simp
      case _ c1 =>
        simp


lemma Holds_openFormulaAux
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (F : Formula)
  (k : Nat)
  (y : String) :
  Holds D I (V ∘ openVar k (free_ y)) F ↔
    Holds D I V (openFormulaAux k (free_ y) F) :=
  by
  induction F generalizing V k
  case pred_ X vs =>
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
    apply shift_openVar

--------------------------------------------------

lemma shift_openVarList
  (D : Type)
  (V : VarAssignment D)
  (k : ℕ)
  (zs : List String)
  (d : D) :
  shift D (V ∘ openVarList k (zs.map Var.free_)) d = shift D V d ∘ openVarList (k + 1) (zs.map Var.free_) :=
  by
  funext v
  simp
  cases v
  case _ a =>
    simp only [openVarList]
    simp only [shift]
    simp
  case _ n =>
    simp only [openVarList]
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
          have s2 : zs.length ≤ n
          simp at c2
          trans (n - k)
          · exact c2
          · exact Nat.sub_le n k

          simp only [Nat.succ_sub s2]


lemma Holds_openFormulaListAux
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (zs : List String)
  (k : Nat)
  (F : Formula) :
  Holds D I (V ∘ openVarList k (zs.map Var.free_)) F ↔
    Holds D I V (openFormulaListAux k (zs.map Var.free_) F) :=
  by
  induction F generalizing V k
  case pred_ X vs =>
    simp only [openFormulaListAux]
    simp only [Holds]
    simp
  case not_ phi phi_ih =>
    simp only [openFormulaListAux]
    simp only [Holds]
    congr! 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [openFormulaListAux]
    simp only [Holds]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ phi phi_ih =>
    simp only [openFormulaListAux]
    simp only [Holds]
    apply forall_congr'
    intro d
    simp only [← phi_ih]
    congr! 1
    apply shift_openVarList

--------------------------------------------------

def Formula.predSub
  (τ : String → ℕ → Formula) :
  Formula → Formula
  | pred_ X vs => openFormulaListAux 0 vs (τ X vs.length)
  | not_ phi => not_ (phi.predSub τ)
  | imp_ phi psi => imp_ (phi.predSub τ) (psi.predSub τ)
  | forall_ x phi => forall_ x (phi.predSub τ)


def Interpretation.usingPred
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
  | free_ x => V (free_ x)
  | bound_ i => subN_aux D (V ∘ bound_) ds i


lemma free_var_list_to_string_list
  (vs : List Var)
  (h1 : ∀ (v : Var), v ∈ vs → Var.lc_at 0 v) :
  ∃ xs, vs = List.map free_ xs :=
  by
  induction vs
  case nil =>
    apply Exists.intro []
    simp
  case cons hd tl ih =>
    simp at h1
    cases h1
    case intro h1_left h1_right =>
      specialize ih h1_right
      apply Exists.elim ih
      intro xs a1
      cases hd
      case free_ x =>
        apply Exists.intro (x :: xs)
        simp
        exact a1
      case bound_ i =>
        simp only [Var.lc_at] at h1_left
        simp at h1_left


theorem predSub_aux
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (τ : String → ℕ → Formula)
  (F : Formula)
  (h1 : F.lc_at 0) :
  Holds D I V (F.predSub τ) ↔
    Holds D (Interpretation.usingPred D I fun (X : String) (ds : List D) => Holds D I (VarAssignment.subN D V ds) (τ X ds.length)) V F :=
  by
  induction F generalizing V
  case pred_ X vs =>
    simp only [Formula.lc_at] at h1

    simp only [predSub]
    simp only [Interpretation.usingPred]
    simp only [Holds]
    simp

    obtain s1 := free_var_list_to_string_list vs h1
    apply Exists.elim s1
    intro xs a1
    clear s1

    subst a1
    simp

    obtain s2 := Holds_openFormulaListAux D I V xs 0 (τ X (List.length xs))
    simp only [← s2]
    clear s2

    sorry
  case forall_ _ phi phi_ih =>
    simp only [Holds]
    apply forall_congr'
    intro d
    specialize phi_ih (shift D V d)
    sorry

  all_goals
    sorry


--#lint