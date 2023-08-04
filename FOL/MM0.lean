import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Util.CompileInductive

import FOL.FunctionUpdateIte
import FOL.Tactics


namespace MM0


/--
  The type of variable names.
-/
inductive VarName : Type
  | mk : String → VarName
  deriving Inhabited, DecidableEq

/--
  The string representation of variable names.
-/
def VarName.toString : VarName → String
  | VarName.mk x => x

instance : ToString VarName :=
  { toString := fun x => x.toString }

instance : Repr VarName :=
  { reprPrec := fun x _ => x.toString.toFormat }


/--
  The type of meta variable names.
-/
inductive MetaVarName : Type
  | mk : String → MetaVarName
  deriving Inhabited, DecidableEq

/--
  The string representation of meta variable names.
-/
def MetaVarName.toString : MetaVarName → String
  | MetaVarName.mk x => x

instance : ToString MetaVarName :=
  { toString := fun x => x.toString }

instance : Repr MetaVarName :=
  { reprPrec := fun x _ => x.toString.toFormat }


/--
  The type of predicate names.
-/
inductive PredName : Type
  | mk : String → PredName
  deriving Inhabited, DecidableEq

/--
  The string representation of predicate names.
-/
def PredName.toString : PredName → String
  | PredName.mk X => X

instance : ToString PredName :=
  { toString := fun X => X.toString }

instance : Repr PredName :=
  { reprPrec := fun X _ => X.toString.toFormat }


/--
  The type of definition names.
-/
inductive DefName : Type
  | mk : String → DefName
  deriving Inhabited, DecidableEq

/--
  The string representation of definition names.
-/
def DefName.toString : DefName → String
  | DefName.mk X => X

instance : ToString DefName :=
  { toString := fun X => X.toString }

instance : Repr DefName :=
  { reprPrec := fun X _ => X.toString.toFormat }


/--
  The type of formulas.
-/
inductive Formula : Type
  | meta_var_ : MetaVarName → Formula
  | pred_ : PredName → List VarName → Formula
  | eq_ : VarName → VarName → Formula
  | true_ : Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  | forall_ : VarName → Formula → Formula
  | def_ : DefName → List VarName → Formula
  deriving Inhabited, DecidableEq

compile_inductive% Formula

open Formula


/--
  (v, X) ∈ Γ if and only if v is not free in X.

  notFree Γ v F := True if and only if v is not free in F in the context Γ.
-/
def notFree
  (Γ : List (VarName × MetaVarName))
  (v : VarName) :
  Formula → Prop
  | meta_var_ X => (v, X) ∈ Γ
  | pred_ _ xs => v ∉ xs
  | eq_ x y => ¬ x = v ∧ ¬ y = v
  | true_ => True
  | not_ phi => notFree Γ v phi
  | imp_ phi psi => notFree Γ v phi ∧ notFree Γ v psi
  | forall_ x phi => x = v ∨ notFree Γ v phi
  | def_ _ xs => v ∉ xs


instance
  (Γ : List (VarName × MetaVarName))
  (v : VarName)
  (F : Formula) :
  Decidable (notFree Γ v F) :=
  by
  induction F
  all_goals
    unfold notFree
    infer_instance


/--
  Formula.metaVarSet F := The set of all of the meta variables that have an occurrence in the formula F.
-/
def Formula.metaVarSet :
  Formula → Finset MetaVarName
  | meta_var_ X => {X}
  | pred_ _ _ => ∅
  | eq_ _ _ => ∅
  | true_ => ∅
  | not_ phi => phi.metaVarSet
  | imp_ phi psi => phi.metaVarSet ∪ psi.metaVarSet
  | forall_ _ phi => phi.metaVarSet
  | def_ _ _ => ∅


/--
  NoMetaVarAndAllFreeInList vs F := True if and only if F contains no meta variables and all of the variables that occur free in F are in vs.
-/
def NoMetaVarAndAllFreeInList
  (vs : List VarName) :
  Formula → Prop
  | meta_var_ _ => False
  | pred_ _ xs => xs ⊆ vs
  | eq_ x y => x ∈ vs ∧ y ∈ vs
  | true_ => True
  | not_ phi => NoMetaVarAndAllFreeInList vs phi
  | imp_ phi psi =>
      NoMetaVarAndAllFreeInList vs phi ∧
      NoMetaVarAndAllFreeInList vs psi
  | forall_ x phi =>
      NoMetaVarAndAllFreeInList (x :: vs) phi
  | def_ _ xs => xs ⊆ vs


example
  (F : Formula)
  (vs vs' : List VarName)
  (h1 : NoMetaVarAndAllFreeInList vs F)
  (h2 : vs ⊆ vs') :
  NoMetaVarAndAllFreeInList vs' F :=
  by
  induction F generalizing vs vs'
  case meta_var_ X =>
    unfold NoMetaVarAndAllFreeInList at h1

    contradiction
  case pred_ X xs =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold NoMetaVarAndAllFreeInList
    exact Set.Subset.trans h1 h2
  case eq_ x y =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold NoMetaVarAndAllFreeInList
    cases h1
    case intro h1_left h1_right =>
    constructor
    · exact h2 h1_left
    · exact h2 h1_right
  case true_ =>
    unfold NoMetaVarAndAllFreeInList
    simp
  case not_ phi phi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold NoMetaVarAndAllFreeInList
    exact phi_ih vs vs' h1 h2
  case imp_ phi psi phi_ih psi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold NoMetaVarAndAllFreeInList
    cases h1
    case intro h1_left h1_right =>
    constructor
    · exact phi_ih vs vs' h1_left h2
    · exact psi_ih vs vs' h1_right h2
  case forall_ x phi phi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold NoMetaVarAndAllFreeInList
    apply phi_ih (x :: vs) (x :: vs') h1
    exact List.cons_subset_cons x h2
  case def_ X xs =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold NoMetaVarAndAllFreeInList
    exact Set.Subset.trans h1 h2


theorem all_free_in_list_and_not_in_list_imp_notFree
  (F : Formula)
  (vs : List VarName)
  (v : VarName)
  (Γ : List (VarName × MetaVarName))
  (h1 : NoMetaVarAndAllFreeInList vs F)
  (h2 : v ∉ vs) :
  notFree Γ v F :=
  by
  induction F generalizing vs
  case meta_var_ X =>
    unfold NoMetaVarAndAllFreeInList at h1

    contradiction
  case pred_ X xs =>
    unfold NoMetaVarAndAllFreeInList at h1 

    unfold notFree
    tauto
  case eq_ x y =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold notFree
    cases h1
    case intro h1_left h1_right =>
      constructor
      · intro contra
        apply h2
        subst contra
        exact h1_left
      · intro contra
        apply h2
        subst contra
        exact h1_right
  case true_ =>
    unfold notFree
    simp
  case not_ phi phi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold notFree
    exact phi_ih vs h1 h2
  case imp_ phi psi phi_ih psi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold notFree
    cases h1
    case intro h1_left h1_right =>
      constructor
      · exact phi_ih vs h1_left h2
      · exact psi_ih vs h1_right h2
  case forall_ x phi phi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold notFree
    by_cases c1 : x = v
    · left
      exact c1
    · right
      apply phi_ih (x :: vs) h1
      simp
      push_neg
      constructor
      · tauto
      · exact h2
  case def_ X xs =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold notFree
    tauto


theorem no_meta_var_imp_metaVarSet_is_empty
  (F : Formula)
  (vs : List VarName)
  (h1 : NoMetaVarAndAllFreeInList vs F) :
  F.metaVarSet = ∅ :=
  by
  induction F generalizing vs
  case meta_var_ X =>
    unfold NoMetaVarAndAllFreeInList at h1

    contradiction
  case pred_ X xs =>
    rfl
  case eq_ x y =>
    rfl
  case true_ =>
    rfl
  case not_ phi phi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold Formula.metaVarSet
    exact phi_ih vs h1
  case imp_ phi psi phi_ih psi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold Formula.metaVarSet
    cases h1
    case intro h1_left h1_right =>
      simp only [phi_ih vs h1_left]
      simp only [psi_ih vs h1_right]
  case forall_ x phi phi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold Formula.metaVarSet
    exact phi_ih (x :: vs) h1
  case def_ X xs =>
    rfl


/--
  A substitution mapping.
  A bijective function mapping variable names to variable names.
-/
def Instantiation :=
  { σ : VarName → VarName // ∃ σ' : VarName → VarName, σ ∘ σ' = id ∧ σ' ∘ σ = id }


theorem Instantiation.HasLeftRightInverse
  (σ : Instantiation) :
  ∃ σ_inv : Instantiation, σ.1 ∘ σ_inv.1 = id ∧ σ_inv.1 ∘ σ.1 = id :=
  by
  apply Exists.elim σ.2
  intro σ' a1
  cases a1
  case intro a1_left a1_right =>
    let σ_inv : Instantiation :=
    {
      val := σ'
      property :=
      by
        apply Exists.intro σ.1
        constructor
        · exact a1_right
        · exact a1_left
    }
    apply Exists.intro σ_inv
    constructor
    · exact a1_left
    · exact a1_right


theorem Instantiation.Injective
  (σ : Instantiation) :
  Function.Injective σ.1 :=
  by
  obtain ⟨σ', a1⟩ := σ.2
  cases a1
  case intro a1_left a1_right =>
    have s1 : Function.LeftInverse σ' σ.1 := congr_fun a1_right
    exact Function.LeftInverse.injective s1


theorem Instantiation.Surjective
  (σ : Instantiation) :
  Function.Surjective σ.1 :=
  by
  obtain ⟨σ', a1⟩ := σ.2
  cases a1
  case intro a1_left a1_right =>
    have s1 : Function.RightInverse σ' σ.1 := congr_fun a1_left
    exact Function.RightInverse.surjective s1


theorem Instantiation.Bijective
  (σ : Instantiation) :
  Function.Bijective σ.1 :=
  by
  unfold Function.Bijective
  constructor
  · exact Instantiation.Injective σ
  · exact Instantiation.Surjective σ


def Instantiation.comp
  (σ σ' : Instantiation) :
  Instantiation :=
  {
    val := σ.val ∘ σ'.val
    property :=
    by
      obtain ⟨σ_inv_val, σ_inv_prop⟩ := σ.2
      obtain ⟨σ'_inv_val, σ'_inv_prop⟩ := σ'.2
      cases σ_inv_prop
      case intro σ_inv_prop_left σ_inv_prop_right =>
        cases σ'_inv_prop
        case intro σ'_inv_prop_left σ'_inv_prop_right =>
        apply Exists.intro (σ'_inv_val ∘ σ_inv_val)
        constructor
        · change σ.val ∘ (σ'.val ∘ σ'_inv_val) ∘ σ_inv_val = id
          simp only [σ'_inv_prop_left]
          simp
          exact σ_inv_prop_left
        · change σ'_inv_val ∘ (σ_inv_val ∘ σ.val) ∘ σ'.val = id
          simp only [σ_inv_prop_right]
          simp
          exact σ'_inv_prop_right
  }


/--
  A meta variable substitution mapping.
  A function mapping meta variable names to formulas.
-/
def MetaInstantiation :
  Type :=
  MetaVarName → Formula


def Sub
  (σ : Instantiation)
  (τ : MetaInstantiation) :
  Formula → Formula
  | meta_var_ X => τ X
  | pred_ X xs => pred_ X (xs.map σ.1)
  | eq_ x y => eq_ (σ.1 x) (σ.1 y)
  | true_ => true_
  | not_ phi => not_ (Sub σ τ phi)
  | imp_ phi psi => imp_ (Sub σ τ phi) (Sub σ τ psi)
  | forall_ x phi => forall_ (σ.1 x) (Sub σ τ phi)
  | def_ X xs => def_ X (xs.map σ.1)


theorem Sub_Instantiation_comp
  (F : Formula)
  (σ σ' : Instantiation) :
  Sub σ Formula.meta_var_ (Sub σ' Formula.meta_var_ F) =
    Sub (Instantiation.comp σ σ') Formula.meta_var_ F :=
  by
  induction F
  case meta_var_ X =>
    rfl
  case pred_ X xs =>
    simp only [Sub]
    unfold Instantiation.comp
    simp
  case eq_ x y =>
    rfl
  case true_ =>
    rfl
  case not_ phi phi_ih =>
    simp only [Sub]
    unfold Instantiation.comp
    congr! 1
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Sub]
    unfold Instantiation.comp
    congr! 1
  case forall_ x phi phi_ih =>
    simp only [Sub]
    unfold Instantiation.comp
    congr! 1
  case def_ X xs =>
    simp only [Sub]
    unfold Instantiation.comp
    simp


theorem Sub_no_metaVar
  (F : Formula)
  (σ : Instantiation)
  (τ : MetaInstantiation)
  (h1 : F.metaVarSet = ∅) :
  (Sub σ τ F).metaVarSet = ∅ :=
  by
  induction F
  case meta_var_ X =>
    unfold Formula.metaVarSet at h1
    simp at h1
  case pred_ X xs =>
    rfl
  case eq_ x y =>
    rfl
  case true_ =>
    rfl
  case not_ phi phi_ih =>
    unfold Formula.metaVarSet at h1

    unfold Sub
    unfold Formula.metaVarSet
    exact phi_ih h1
  case imp_ phi psi phi_ih psi_ih =>
    unfold Formula.metaVarSet at h1
    simp only [Finset.union_eq_empty_iff] at h1

    unfold Sub
    unfold Formula.metaVarSet
    cases h1
    case intro h1_left h1_right =>
      simp only [Finset.union_eq_empty_iff]
      constructor
      · exact phi_ih h1_left
      · exact psi_ih h1_right
  case forall_ x phi phi_ih =>
    unfold Formula.metaVarSet at h1

    unfold Sub
    unfold Formula.metaVarSet
    exact phi_ih h1
  case def_ X xs =>
    rfl


theorem no_meta_var_sub
  (F : Formula)
  (σ : Instantiation)
  (τ τ' : MetaInstantiation)
  (h1 : F.metaVarSet = ∅) :
  Sub σ τ F = Sub σ τ' F :=
  by
  induction F
  case meta_var_ X =>
    unfold Formula.metaVarSet at h1
    simp at h1
  case pred_ X xs =>
    rfl
  case eq_ x y =>
    rfl
  case true_ =>
    rfl
  case not_ phi phi_ih =>
    unfold Formula.metaVarSet at h1

    unfold Sub
    congr! 1
    exact phi_ih h1
  case imp_ phi psi phi_ih psi_ih =>
    unfold Formula.metaVarSet at h1 
    simp only [Finset.union_eq_empty_iff] at h1

    unfold Sub
    cases h1
    case intro h1_left h1_right =>
    congr! 1
    · exact phi_ih h1_left
    · exact psi_ih h1_right
  case forall_ x phi phi_ih =>
    unfold Formula.metaVarSet at h1

    unfold Sub
    congr! 1
    exact phi_ih h1
  case def_ X xs =>
    rfl


theorem NoMetaVarAndAllFreeInList_Sub
  (F : Formula)
  (vs : List VarName)
  (σ : Instantiation)
  (τ : MetaInstantiation)
  (h1 : NoMetaVarAndAllFreeInList vs F) :
  NoMetaVarAndAllFreeInList (vs.map σ.1) (Sub σ τ F) :=
  by
  induction F generalizing vs
  case meta_var_ X =>
    unfold NoMetaVarAndAllFreeInList at h1

    contradiction
  case pred_ X xs =>
    unfold Sub
    unfold NoMetaVarAndAllFreeInList
    exact List.map_subset σ.1 h1
  case true_ =>
    unfold Sub
    unfold NoMetaVarAndAllFreeInList
    simp
  case not_ phi phi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold Sub
    unfold NoMetaVarAndAllFreeInList
    exact phi_ih vs h1
  case imp_ phi psi phi_ih psi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold Sub
    unfold NoMetaVarAndAllFreeInList
    cases h1
    case intro h1_left h1_right =>
      constructor
      · exact phi_ih vs h1_left
      · exact psi_ih vs h1_right
  case eq_ x y =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold Sub
    unfold NoMetaVarAndAllFreeInList
    cases h1
    case intro h1_left h1_right =>
      constructor
      · exact List.mem_map_of_mem σ.val h1_left
      · exact List.mem_map_of_mem σ.val h1_right
  case forall_ x phi phi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold Sub
    unfold NoMetaVarAndAllFreeInList
    simp only [← List.map_cons]
    exact phi_ih (x :: vs) h1
  case def_ X xs =>
    unfold Sub
    unfold NoMetaVarAndAllFreeInList
    exact List.map_subset σ.val h1


structure Definition_ : Type :=
  name : DefName
  args : List VarName
  F : Formula
  nodup : args.Nodup
  nf : NoMetaVarAndAllFreeInList args F
  deriving DecidableEq


abbrev Env : Type := List Definition_

def Env.Nodup : Env → Prop :=
  List.Pairwise fun d1 d2 : Definition_ =>
    d1.name = d2.name → d1.args.length = d2.args.length → False


/--
  IsMetaVarOrAllDefInEnv E F := True if and only if F is a meta variable or every definition in F is defined in E.
-/
def IsMetaVarOrAllDefInEnv
  (E : Env) :
  Formula → Prop
  | meta_var_ _ => True
  | pred_ _ _ => True
  | eq_ _ _ => True
  | true_ => True
  | not_ phi => IsMetaVarOrAllDefInEnv E phi
  | imp_ phi psi =>
    IsMetaVarOrAllDefInEnv E phi ∧
    IsMetaVarOrAllDefInEnv E psi
  | forall_ _ phi => IsMetaVarOrAllDefInEnv E phi
  | def_ X xs =>
      ∃ d : Definition_,
        d ∈ E ∧
        X = d.name ∧
        xs.length = d.args.length


theorem Sub_IsMetaVarOrAllDefInEnv
  (F : Formula)
  (E : Env)
  (σ : Instantiation)
  (h1 : IsMetaVarOrAllDefInEnv E F) :
  IsMetaVarOrAllDefInEnv E (Sub σ Formula.meta_var_ F) :=
  by
  induction F
  case meta_var_ X =>
    unfold Sub
    unfold IsMetaVarOrAllDefInEnv
    simp only
  case pred_ X xs =>
    unfold Sub
    unfold IsMetaVarOrAllDefInEnv
    simp only
  case eq_ x y =>
    unfold Sub
    unfold IsMetaVarOrAllDefInEnv
    simp only
  case true_ =>
    unfold Sub
    unfold IsMetaVarOrAllDefInEnv
    simp only
  case not_ phi phi_ih =>
    unfold IsMetaVarOrAllDefInEnv at h1

    unfold Sub
    unfold IsMetaVarOrAllDefInEnv
    exact phi_ih h1
  case imp_ phi psi phi_ih psi_ih =>
    unfold IsMetaVarOrAllDefInEnv at h1

    unfold Sub
    unfold IsMetaVarOrAllDefInEnv
    cases h1
    case intro h1_left h1_right =>
    constructor
    · exact phi_ih h1_left
    · exact psi_ih h1_right
  case forall_ x phi phi_ih =>
    unfold IsMetaVarOrAllDefInEnv at h1

    unfold Sub
    unfold IsMetaVarOrAllDefInEnv
    exact phi_ih h1
  case def_ X xs =>
    unfold IsMetaVarOrAllDefInEnv at h1

    unfold Sub
    unfold IsMetaVarOrAllDefInEnv
    simp
    exact h1


def Env.WellFormed : Env → Prop
  | List.nil => True
  | d :: E =>
    (∀ d' : Definition_, d' ∈ E →
      d.name = d'.name → d.args.length = d'.args.length → False) ∧
        IsMetaVarOrAllDefInEnv E d.F ∧ Env.WellFormed E


theorem WellFormed_Env_Nodup
  (E : Env)
  (h1 : E.WellFormed) :
  E.Nodup :=
  by
  induction E
  case nil =>
    unfold Env.Nodup
    simp
  case cons hd tl ih =>
    unfold Env.Nodup at ih

    unfold Env.WellFormed at h1

    cases h1
    case intro h1_left h1_right =>
      cases h1_right
      case intro h1_right_left h1_right_right =>
        unfold Env.Nodup
        simp
        constructor
        · exact h1_left
        · exact ih h1_right_right


theorem Concat_IsMetaVarOrAllDefInEnv
  (E E' : Env)
  (F : Formula)
  (h1 : ∃ E1 : Env, E' = E1 ++ E)
  (h2 : IsMetaVarOrAllDefInEnv E F) :
  IsMetaVarOrAllDefInEnv E' F :=
  by
  induction E generalizing F
  all_goals
    induction F
    case meta_var_ X =>
      unfold IsMetaVarOrAllDefInEnv
      simp only
    case pred_ X xs =>
      unfold IsMetaVarOrAllDefInEnv
      simp only
    case eq_ x y =>
      unfold IsMetaVarOrAllDefInEnv
      simp only
    case true_ =>
      unfold IsMetaVarOrAllDefInEnv
      simp only
    case not_ phi phi_ih =>
      unfold IsMetaVarOrAllDefInEnv at h2

      unfold IsMetaVarOrAllDefInEnv
      exact phi_ih h2
    case imp_ phi psi phi_ih psi_ih =>
      unfold IsMetaVarOrAllDefInEnv at h2

      unfold IsMetaVarOrAllDefInEnv
      cases h2
      case intro h2_left h2_right =>
      constructor
      · exact phi_ih h2_left
      · exact psi_ih h2_right
    case forall_ x phi phi_ih =>
      unfold IsMetaVarOrAllDefInEnv at h2

      unfold IsMetaVarOrAllDefInEnv
      exact phi_ih h2

  case nil.def_ X xs =>
    unfold IsMetaVarOrAllDefInEnv at h2
    simp at h2
  case cons.def_ E_hd E_tl E_ih X xs =>
    unfold IsMetaVarOrAllDefInEnv at h2

    apply Exists.elim h1
    intro E1 h1_1

    apply Exists.elim h2
    intro d h2_1

    cases h2_1
    case intro h2_1_left h2_1_right =>
      simp at h2_1_left
      cases h2_1_left
      case inl c1 =>
        unfold IsMetaVarOrAllDefInEnv
        apply Exists.intro E_hd
        simp only [h1_1]
        constructor
        · simp
        · simp only [← c1]
          exact h2_1_right
      case inr c1 =>
        apply E_ih
        · apply Exists.intro (E1 ++ [E_hd])
          simp
          exact h1_1

        · unfold IsMetaVarOrAllDefInEnv
          apply Exists.intro d
          constructor
          · exact c1
          · exact h2_1_right


theorem def_in_Env_imp_isMetaVarOrAllDefInEnv
  (E : Env)
  (d : Definition_)
  (h1 : E.WellFormed)
  (h2 : d ∈ E) :
  IsMetaVarOrAllDefInEnv E d.F :=
  by
  induction E
  case nil =>
    simp at h2
  case cons hd tl ih =>
    unfold Env.WellFormed at h1

    simp at h2

    cases h1
    case intro h1_left h1_right =>
      cases h1_right
      case intro h1_right_left h1_right_right =>
        apply Concat_IsMetaVarOrAllDefInEnv tl (hd :: tl)
        · apply Exists.intro [hd]
          simp
        · cases h2
          case _ c1 =>
            subst c1
            exact h1_right_left
          case _ c1 =>
            exact ih h1_right_right c1


inductive IsConv (E : Env) : Formula → Formula → Prop
  | conv_refl
    (phi : Formula) :
    IsConv E phi phi

  | conv_symm
    (phi phi' : Formula) :
    IsConv E phi phi' →
    IsConv E phi' phi

  | conv_trans
    (phi phi' phi'' : Formula) :
    IsConv E phi phi' →
    IsConv E phi' phi'' →
    IsConv E phi phi''

  | conv_not
    (phi phi' : Formula) :
    IsConv E phi phi' →
    IsConv E (not_ phi) (not_ phi')

  | conv_imp
    (phi phi' psi psi' : Formula) :
    IsConv E phi phi' →
    IsConv E psi psi' →
    IsConv E (imp_ phi psi) (imp_ phi' psi')

  | conv_forall
    (x : VarName)
    (phi phi' : Formula) :
    IsConv E phi phi' →
    IsConv E (forall_ x phi) (forall_ x phi')

  | conv_unfold
    (d : Definition_)
    (σ : Instantiation) :
    d ∈ E →
    IsConv E (def_ d.name (d.args.map σ.1)) (Sub σ meta_var_ d.F)


def Formula.false_ : Formula := not_ true_

def Formula.and_
  (phi psi : Formula) :
  Formula :=
  not_ (phi.imp_ psi.not_)

def Formula.exists_
  (x : VarName)
  (phi : Formula) :
  Formula :=
  not_ (forall_ x (not_ phi))


def Formula.And_
  (l : List Formula) :
  Formula :=
  List.foldr Formula.and_ true_ l

def eqSubPred
  (name : PredName)
  (n : ℕ)
  (xs ys : Fin n → VarName) :
  Formula :=
  (And_ (List.ofFn fun i : Fin n => eq_ (xs i) (ys i))).imp_
    ((pred_ name (List.ofFn xs)).imp_ (pred_ name (List.ofFn ys)))


/-
  (v, X) ∈ Γ if and only if v is not free in X.

  Δ is a list of hypotheses.
-/
inductive IsProof
  (E : Env) :
  List (VarName × MetaVarName) → List Formula → Formula → Prop

  | hyp
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (phi : Formula) :
    IsMetaVarOrAllDefInEnv E phi →
    phi ∈ Δ →
    IsProof E Γ Δ phi

  | mp
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (phi psi : Formula) :
    IsProof E Γ Δ phi →
    IsProof E Γ Δ (phi.imp_ psi) →
    IsProof E Γ Δ psi

  | prop_1
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (phi psi : Formula) :
    IsMetaVarOrAllDefInEnv E phi →
    IsMetaVarOrAllDefInEnv E psi →
    IsProof E Γ Δ (phi.imp_ (psi.imp_ phi))

  | prop_2
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (phi psi chi : Formula) :
    IsMetaVarOrAllDefInEnv E phi →
    IsMetaVarOrAllDefInEnv E psi →
    IsMetaVarOrAllDefInEnv E chi →
    IsProof E Γ Δ ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi)))

  | prop_3
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (phi psi : Formula) :
    IsMetaVarOrAllDefInEnv E phi →
    IsMetaVarOrAllDefInEnv E psi →
    IsProof E Γ Δ (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi))

  | gen
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (phi : Formula)
    (x : VarName) :
    IsProof E Γ Δ phi →
    IsProof E Γ Δ (forall_ x phi)

  | pred_1
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (phi psi : Formula)
    (x : VarName) :
    IsMetaVarOrAllDefInEnv E phi →
    IsMetaVarOrAllDefInEnv E psi →
    IsProof E Γ Δ ((forall_ x (phi.imp_ psi)).imp_ ((forall_ x phi).imp_ (forall_ x psi)))

  | pred_2
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (phi : Formula)
    (x : VarName) :
    IsMetaVarOrAllDefInEnv E phi →
    notFree Γ x phi →
    IsProof E Γ Δ (phi.imp_ (forall_ x phi))

  | eq_1
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (x y : VarName) :
    ¬ y = x →
    IsProof E Γ Δ (exists_ x (eq_ x y))

  | eq_2
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (x y z : VarName) :
    IsProof E Γ Δ ((eq_ x y).imp_ ((eq_ x z).imp_ (eq_ y z)))

  | eq_3
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (n : ℕ)
    (name : PredName)
    (xs ys : Fin n → VarName) :
    IsProof E Γ Δ (eqSubPred name n xs ys)

  | thm
    (Γ Γ' : List (VarName × MetaVarName))
    (Δ Δ' : List Formula)
    (phi : Formula)
    (σ : Instantiation)
    (τ : MetaInstantiation) :
    (∀ X : MetaVarName, X ∈ phi.metaVarSet →
    IsMetaVarOrAllDefInEnv E (τ X)) →
    (∀ (x : VarName) (X : MetaVarName), (x, X) ∈ Γ → notFree Γ' (σ.1 x) (τ X)) →
    (∀ psi : Formula, psi ∈ Δ → IsProof E Γ' Δ' (Sub σ τ phi)) →
    IsProof E Γ Δ phi →
    IsProof E Γ' Δ' (Sub σ τ phi)

  | conv
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (phi phi' : Formula) :
    IsMetaVarOrAllDefInEnv E phi' →
    IsProof E Γ Δ phi →
    IsConv E phi phi' →
    IsProof E Γ Δ phi'


-- Semantics

def Interpretation (D : Type) : Type :=
  PredName → List D → Prop

def Valuation (D : Type) : Type :=
  VarName → D

def MetaValuation (D : Type) : Type :=
  MetaVarName → Valuation D → Prop


def Holds
  (D : Type)
  (I : Interpretation D)
  (V : Valuation D)
  (M : MetaValuation D) : Env → Formula → Prop
  | _, meta_var_ X => M X V
  | _, pred_ X xs => I X (xs.map V)
  | _, eq_ x y => V x = V y
  | _, true_ => True
  | E, not_ phi => ¬ Holds D I V M E phi
  | E, imp_ phi psi =>
    have : sizeOf psi < sizeOf (imp_ phi psi) := by simp
    Holds D I V M E phi → Holds D I V M E psi
  | E, forall_ x phi =>
    have : sizeOf phi < sizeOf (forall_ x phi) := by simp
    ∀ d : D, Holds D I (Function.updateIte V x d) M E phi
  | ([] : Env), def_ _ _ => False
  | d :: E, def_ name args =>
    if name = d.name ∧ args.length = d.args.length
    then Holds D I (Function.updateListIte V d.args (List.map V args)) M E d.F
    else Holds D I V M E (def_ name args)
termination_by _ E phi => (E.length, phi)


theorem Holds_coincide_Var
  (D : Type)
  (I : Interpretation D)
  (V V' : Valuation D)
  (M : MetaValuation D)
  (E : Env)
  (F : Formula)
  (vs : List VarName)
  (h1 : NoMetaVarAndAllFreeInList vs F)
  (h2 : ∀ v : VarName, v ∈ vs → V v = V' v) :
  Holds D I V M E F ↔ Holds D I V' M E F :=
  by
  induction E generalizing F vs V V'
  all_goals
    induction F generalizing vs V V'
    case meta_var_ X =>
      unfold NoMetaVarAndAllFreeInList at h1

      contradiction
    case pred_ X xs =>
      unfold NoMetaVarAndAllFreeInList at h1

      simp only [Holds]
      congr! 1
      simp only [List.map_eq_map_iff]
      tauto
    case eq_ x y =>
      unfold NoMetaVarAndAllFreeInList at h1

      cases h1
      case intro h1_left h1_right =>
        simp only [Holds]
        congr! 1
        · exact h2 x h1_left
        · exact h2 y h1_right
    case true_ =>
      simp only [Holds]
    case not_ phi phi_ih =>
      unfold NoMetaVarAndAllFreeInList at h1

      simp only [Holds]
      congr! 1
      exact phi_ih V V' vs h1 h2
    case imp_ phi psi phi_ih psi_ih =>
      unfold NoMetaVarAndAllFreeInList at h1

      simp only [Holds]
      cases h1
      case intro h1_left h1_right =>
        congr! 1
        · exact phi_ih V V' vs h1_left h2
        · exact psi_ih V V' vs h1_right h2
    case forall_ x phi phi_ih =>
      unfold NoMetaVarAndAllFreeInList at h1

      simp only [Holds]
      apply forall_congr'
      intro a
      apply phi_ih
      · exact h1
      · intro v a1
        unfold Function.updateIte
        split_ifs
        case _ c1 =>
          rfl
        case _ c1 =>
          simp at a1
          tauto

  case nil.def_ X xs =>
    simp only [Holds]

  case cons.def_ E_hd E_tl E_ih X xs =>
    unfold NoMetaVarAndAllFreeInList at h1

    simp only [Holds]
    split_ifs
    case _ c1 =>
      apply E_ih (Function.updateListIte V E_hd.args (List.map V xs)) (Function.updateListIte V' E_hd.args (List.map V' xs)) E_hd.F E_hd.args E_hd.nf
      intro v a1
      apply Function.updateListIte_fun_coincide_mem_eq_len
      · tauto
      · exact a1
      · tauto
    case _ c1 =>
      apply E_ih V V' (def_ X xs) vs
      · unfold NoMetaVarAndAllFreeInList
        exact h1
      · exact h2


theorem Holds_coincide_MetaVar
  (D : Type)
  (I : Interpretation D)
  (V : Valuation D)
  (M M' : MetaValuation D)
  (E : Env)
  (F : Formula)
  (h1 : ∀ (V' : Valuation D) (X : MetaVarName), X ∈ F.metaVarSet → (M X V' ↔ M' X V')) :
    Holds D I V M E F ↔ Holds D I V M' E F :=
  by
  induction E generalizing F V M M'
  all_goals
    induction F generalizing V M M'
    case meta_var_ X =>
      unfold Formula.metaVarSet at h1
      simp at h1

      simp only [Holds]
      exact h1 V
    case pred_ X xs =>
      simp only [Holds]
    case eq_ x y =>
      simp only [Holds]
    case true_ =>
      simp only [Holds]
    case not_ phi phi_ih =>
      unfold Formula.metaVarSet at h1

      simp only [Holds]
      congr! 1
      exact phi_ih V M M' h1
    case imp_ phi psi phi_ih psi_ih =>
      unfold Formula.metaVarSet at h1
      simp at h1

      simp only [Holds]
      congr! 1
      · apply phi_ih
        intro V' X a1
        apply h1
        left
        exact a1
      · apply psi_ih
        intro V' X a1
        apply h1
        right
        exact a1
    case forall_ x phi phi_ih =>
      unfold Formula.metaVarSet at h1

      simp only [Holds]
      apply forall_congr'
      intro a
      exact phi_ih (Function.updateIte V x a) M M' h1

  case nil.def_ X xs =>
    simp only [Holds]

  case cons.def_ E_hd E_tl E_ih X xs =>
    simp only [Holds]
    split_ifs
    · apply E_ih
      simp only [no_meta_var_imp_metaVarSet_is_empty E_hd.F E_hd.args E_hd.nf]
      simp
    · apply E_ih
      unfold Formula.metaVarSet
      simp


theorem Holds_coincide_MetaVar_no_MetaVar
  (D : Type)
  (I : Interpretation D)
  (V : Valuation D)
  (M M' : MetaValuation D)
  (E : Env)
  (F : Formula)
  (h1 : F.metaVarSet = ∅) :
  Holds D I V M E F ↔ Holds D I V M' E F :=
  by
  apply Holds_coincide_MetaVar
  simp only [h1]
  simp


theorem holds_def_imp_ex_def {D : Type} (P : PredInterpretation D) (M : MetaValuation D) (E : Env)
    (V : Valuation D) (name : VarName) (args : List VarName)
    (h1 : Holds D P M E (def_ Name args) V) :
    ∃ d : Definition_, d ∈ E ∧ Name = d.Name ∧ args.length = d.args.length :=
  by
  induction E
  case nil =>
    simp only [holds_nil_def] at h1 
    contradiction
  case cons E_hd E_tl E_ih =>
    simp only [holds_not_nil_def] at h1 
    split_ifs at h1 
    · apply Exists.intro E_hd
      simp only [List.mem_cons, eq_self_iff_true, true_or_iff, true_and_iff]
      exact h
    · specialize E_ih h1
      apply Exists.elim E_ih
      intro d E_ih_1
      cases E_ih_1
      apply Exists.intro d
      constructor
      · simp only [List.mem_cons]
        apply Or.intro_right
        exact E_ih_1_left
      · exact E_ih_1_right

example {D : Type} (P : PredInterpretation D) (M : MetaValuation D) (E E' : Env) (name : VarName)
    (args : List VarName) (V : Valuation D) (h1 : ∃ E1 : Env, E' = E1 ++ E) (h2 : E'.Nodup_)
    (h3 : Holds D P M E (def_ Name args) V) : Holds D P M E' (def_ Name args) V :=
  by
  apply Exists.elim h1
  intro E1 h1_1
  clear h1
  unfold env.nodup_ at h2 
  subst h1_1
  induction E1
  case nil =>
    simp only [List.nil_append]
    exact h3
  case cons E1_hd E1_tl
    E1_ih =>
    simp only [List.cons_append, List.pairwise_cons, List.mem_append] at h2 
    cases h2
    specialize E1_ih h2_right
    simp only [List.cons_append, holds_not_nil_def]
    split_ifs
    · have s1 : ∃ d : definition_, d ∈ E1_tl ++ E ∧ Name = d.Name ∧ args.length = d.args.length :=
        holds_def_imp_ex_def P M (E1_tl ++ E) V Name args E1_ih
      apply Exists.elim s1
      intro d s1_1
      cases s1_1
      simp only [List.mem_append] at s1_1_left 
      cases s1_1_right
      cases h
      exfalso
      apply h2_left d s1_1_left
      · rw [← h_left]
        exact s1_1_right_left
      · rw [← h_right]
        exact s1_1_right_right
    · exact E1_ih

theorem holds_env_ext {D : Type} (P : PredInterpretation D) (M : MetaValuation D) (E E' : Env)
    (phi : Formula) (V : Valuation D) (h1 : ∃ E1 : Env, E' = E1 ++ E)
    (h2 : phi.IsMetaVarOrAllDefInEnv E) (h3 : E'.Nodup_) : Holds D P M E' phi V ↔ Holds D P M E phi V :=
  by
  induction phi generalizing V
  case meta_var_ X V => simp only [holds_meta_var]
  case false_ V => simp only [holds_false]
  case pred_ name args V => simp only [holds_pred]
  case not_ phi phi_ih V =>
    unfold Formula.is_meta_var_or_all_def_in_env at h2 
    simp only [holds_not]
    apply not_congr
    exact phi_ih h2 V
  case imp_ phi psi phi_ih psi_ih
    V =>
    unfold Formula.is_meta_var_or_all_def_in_env at h2 
    cases h2
    simp only [holds_imp]
    apply imp_congr
    · exact phi_ih h2_left V
    · exact psi_ih h2_right V
  case eq_ x y V => simp only [holds_eq]
  case forall_ x phi phi_ih
    V =>
    unfold Formula.is_meta_var_or_all_def_in_env at h2 
    simp only [holds_forall]
    apply forall_congr'
    intro a
    exact phi_ih h2 (Function.update V x a)
  case def_ name args V =>
    apply Exists.elim h1
    intro E1 h1_1
    clear h1
    unfold Formula.is_meta_var_or_all_def_in_env at h2 
    apply Exists.elim h2
    intro a h2_1
    cases h2_1
    cases h2_1_right
    clear h2
    unfold env.nodup_ at h3 
    subst h1_1
    induction E1
    case nil => simp only [List.nil_append]
    case cons E1_hd E1_tl
      E1_ih =>
      simp only [List.cons_append, List.pairwise_cons, List.mem_append] at h3 
      cases h3
      simp only [List.cons_append, holds_not_nil_def]
      split_ifs
      · cases h
        exfalso
        apply h3_left a
        · apply Or.intro_right
          exact h2_1_left
        · rw [← h2_1_right_left]
          rw [h_left]
        · rw [← h2_1_right_right]
          rw [h_right]
      · exact E1_ih h3_right

theorem holds_subst {D : Type} (P : PredInterpretation D) (M : MetaValuation D) (E : Env)
    (σ : Instantiation) (σ' : VarName → VarName) (τ : MetaInstantiation) (phi : Formula)
    (V : Valuation D) (h1 : phi.IsMetaVarOrAllDefInEnv E) (h2 : σ.1 ∘ σ' = id ∧ σ' ∘ σ.1 = id) :
    Holds D P (fun (X' : MetaVarName) (V' : Valuation D) => Holds D P M E (τ X') (V' ∘ σ')) E phi
        (V ∘ σ.1) ↔
      Holds D P M E (phi.subst σ τ) V :=
  by
  induction phi generalizing V
  case meta_var_ X V =>
    cases h2
    unfold Formula.subst
    simp only [holds_meta_var]
    rw [Function.comp.assoc]
    rw [h2_left]
    rw [Function.comp.right_id]
  case pred_ name args V =>
    unfold Formula.subst
    simp only [holds_pred, List.map_map]
  case false_ V =>
    unfold Formula.subst
    simp only [holds_false]
  case not_ phi phi_ih V =>
    unfold Formula.is_meta_var_or_all_def_in_env at h1 
    unfold Formula.subst
    simp only [holds_not]
    apply not_congr
    exact phi_ih h1 V
  case imp_ phi psi phi_ih psi_ih
    V =>
    unfold Formula.is_meta_var_or_all_def_in_env at h1 
    cases h1
    unfold Formula.subst
    simp only [holds_imp]
    apply imp_congr
    · exact phi_ih h1_left V
    · exact psi_ih h1_right V
  case eq_ x y V =>
    unfold Formula.subst
    simp only [holds_eq]
  case forall_ x phi phi_ih
    V =>
    unfold Formula.is_meta_var_or_all_def_in_env at h1 
    cases h2
    unfold Formula.subst
    simp only [holds_forall]
    apply forall_congr'
    intro a
    rw [← aux_1 V σ.val σ' x a h2_right]
    exact phi_ih h1 (Function.update V (σ.val x) a)
  case def_ name args V =>
    induction E
    case nil =>
      unfold Formula.is_meta_var_or_all_def_in_env at h1 
      simp only [List.not_mem_nil, false_and_iff, exists_false] at h1 
      contradiction
    case cons E_hd E_tl
      E_ih =>
      have s1 : E_hd.q.meta_var_set = ∅ :=
        no_meta_var_imp_meta_var_set_is_empty E_hd.q E_hd.args E_hd.nf
      unfold Formula.subst
      simp only [holds_meta_var, holds_not_nil_def, List.length_map, List.map_map]
      split_ifs
      · cases h
        rw [holds_valuation_ext P M E_tl
            (Function.updateList V (E_hd.args.zip (List.map (V ∘ σ.val) args)))
            (Function.updateList (V ∘ σ.val) (E_hd.args.zip (List.map (V ∘ σ.val) args))) E_hd.q
            E_hd.args E_hd.nf]
        · apply holds_meta_valuation_ext
          rw [s1]
          simp only [Finset.not_mem_empty, IsEmpty.forall_iff, forall_forall_const, imp_true_iff]
        · intro v a1
          apply Function.updateList_zip_map_mem_ext
          · rw [h_right]
          · exact a1
      · unfold Formula.is_meta_var_or_all_def_in_env at h1 
        apply Exists.elim h1
        intro d h1_1
        clear h1
        cases h1_1
        simp only [List.mem_cons] at h1_1_left 
        cases h1_1_left
        · rw [← h1_1_left] at h 
          exfalso
          apply h
          exact h1_1_right
        · unfold Formula.subst at E_ih 
          rw [← E_ih]
          apply holds_meta_valuation_ext
          unfold Formula.metaVarSet
          simp only [Finset.not_mem_empty, IsEmpty.forall_iff, forall_forall_const, imp_true_iff]
          unfold Formula.is_meta_var_or_all_def_in_env
          apply Exists.intro d
          constructor
          · exact h1_1_left
          · exact h1_1_right

/-
  Changing v does not cause the value of phi to change.
-/
def IsnotFree (D : Type) (P : PredInterpretation D) (M : MetaValuation D) (E : Env) (v : VarName)
    (phi : Formula) : Prop :=
  ∀ (V : Valuation D) (a : D), Holds D P M E phi V ↔ Holds D P M E phi (Function.update V v a)

example {D : Type} (P : PredInterpretation D) (M : MetaValuation D) (E : Env) (v : VarName)
    (phi : Formula) :
    IsnotFree D P M E v phi ↔
      ∀ V V' : Valuation D,
        (∀ y : VarName, ¬y = v → V y = V' y) → (Holds D P M E phi V ↔ Holds D P M E phi V') :=
  by
  unfold is_notFree
  constructor
  · intro a1 V V' a2
    rw [← aux_3 V V' v a2]
    exact a1 V (V' v)
  · intro a1 V a
    apply a1
    intro a' a2
    simp only [Function.update_noteq a2]

theorem notFree_imp_isnotFree {D : Type} (P : PredInterpretation D) (M : MetaValuation D) (E : Env)
    (Γ : List (VarName × MetaVarName)) (v : VarName) (phi : Formula) (h1 : notFree Γ v phi)
    (h2 : ∀ X : MetaVarName, (v, X) ∈ Γ → IsnotFree D P M E v (meta_var_ X)) :
    IsnotFree D P M E v phi := by
  induction phi
  case meta_var_ X =>
    unfold notFree at h1 
    exact h2 X h1
  case false_ =>
    unfold is_notFree
    simp only [holds_false, iff_self_iff, forall₂_true_iff]
  case pred_ name args =>
    unfold notFree at h1 
    unfold is_notFree at *
    simp only [holds_pred]
    intro V a
    have s1 : List.map (Function.update V v a) args = List.map V args
    apply List.map_congr
    intro x a1
    have s2 : ¬x = v
    intro contra
    apply h1
    rw [← contra]
    exact a1
    simp only [Function.update_noteq s2]
    rw [s1]
  case not_ phi phi_ih =>
    unfold notFree at h1 
    unfold is_notFree at *
    simp only [holds_not]
    intro V a
    apply not_congr
    exact phi_ih h1 V a
  case imp_ phi psi phi_ih psi_ih =>
    unfold notFree at h1 
    cases h1
    unfold is_notFree at *
    simp only [holds_imp]
    intro V a
    apply imp_congr
    · exact phi_ih h1_left V a
    · exact psi_ih h1_right V a
  case eq_ x y =>
    unfold notFree at h1 
    cases h1
    unfold is_notFree at *
    simp only [holds_eq]
    intro V a
    simp only [Function.update_noteq h1_left, Function.update_noteq h1_right]
  case forall_ x phi phi_ih =>
    unfold notFree at h1 
    unfold is_notFree at *
    simp only [holds_forall]
    intro V a
    apply forall_congr'
    intro a'
    cases h1
    · rw [h1]
      simp only [Function.update_idem]
    · by_cases c1 : v = x
      · rw [c1]
        simp only [Function.update_idem]
      · simp only [Function.update_comm c1]
        exact phi_ih h1 (Function.update V x a') a
  case def_ name args =>
    induction E
    case nil =>
      intro V a
      simp only [holds_nil_def]
    case cons E_hd E_tl E_ih =>
      unfold is_notFree at *
      simp only [holds_not_nil_def, holds_meta_var] at *
      intro V a
      split_ifs
      · apply
          holds_valuation_ext P M E_tl (Function.updateList V (E_hd.args.zip (List.map V args)))
            (Function.updateList (Function.update V v a)
              (E_hd.args.zip (List.map (Function.update V v a) args)))
            E_hd.q E_hd.args E_hd.nf
        · intro v' a1
          symm
          apply Function.updateList_update V (Function.update V v a)
          · unfold notFree at h1 
            intro y a2 contra
            apply h1
            rw [← contra]
            exact a2
          · cases h
            rw [h_right]
          · exact a1
      · exact E_ih h2 V a

theorem lem_1 {D : Type} (P : PredInterpretation D) (M : MetaValuation D) (E : Env)
    (Γ Γ' : List (VarName × MetaVarName)) (σ : Instantiation) (σ' : VarName → VarName)
    (τ : MetaInstantiation) (h1 : σ.1 ∘ σ' = id ∧ σ' ∘ σ.1 = id)
    (h2 : ∀ (v : VarName) (X : MetaVarName), (v, X) ∈ Γ' → IsnotFree D P M E v (meta_var_ X))
    (h3 : ∀ (v : VarName) (X : MetaVarName), (v, X) ∈ Γ → notFree Γ' (σ.1 v) (τ X)) :
    ∀ (v : VarName) (X : MetaVarName),
      (v, X) ∈ Γ →
        IsnotFree D P (fun (X : MetaVarName) (V' : Valuation D) => Holds D P M E (τ X) (V' ∘ σ')) E
          v (meta_var_ X) :=
  by
  cases h1
  intro v X a1
  unfold is_notFree
  simp only [holds_meta_var]
  intro V a
  rw [aux_2 V σ' σ.1 v a h1_left h1_right]
  apply notFree_imp_is_notFree P M E Γ'
  · exact h3 v X a1
  · intro X' a2
    exact h2 (σ.1 v) X' a2

theorem lem_2_a (E : Env) (σ : Instantiation) (τ : MetaInstantiation) (phi : Formula)
    (h1 : phi.IsMetaVarOrAllDefInEnv E)
    (h2 : ∀ X : MetaVarName, X ∈ phi.metaVarSet → (τ X).IsMetaVarOrAllDefInEnv E) :
    (phi.subst σ τ).IsMetaVarOrAllDefInEnv E :=
  by
  induction phi
  case meta_var_ X =>
    unfold Formula.metaVarSet at h2 
    simp only [Finset.mem_singleton, forall_eq] at h2 
    unfold Formula.subst
    exact h2
  case false_ => unfold Formula.subst
  case pred_ name args => unfold Formula.subst
  case not_ phi phi_ih =>
    unfold Formula.is_meta_var_or_all_def_in_env at h1 
    unfold Formula.metaVarSet at h2 
    unfold Formula.subst
    unfold Formula.is_meta_var_or_all_def_in_env
    exact phi_ih h1 h2
  case imp_ phi psi phi_ih
    psi_ih =>
    unfold Formula.is_meta_var_or_all_def_in_env at h1 
    cases h1
    unfold Formula.metaVarSet at h2 
    simp only [Finset.mem_union] at h2 
    unfold Formula.subst
    unfold Formula.is_meta_var_or_all_def_in_env
    constructor
    · apply phi_ih h1_left
      intro X a1
      apply h2
      apply Or.intro_left
      exact a1
    · apply psi_ih h1_right
      intro X a1
      apply h2
      apply Or.intro_right
      exact a1
  case eq_ x y => unfold Formula.subst
  case forall_ x phi phi_ih =>
    unfold Formula.is_meta_var_or_all_def_in_env at h1 
    unfold Formula.metaVarSet at h2 
    unfold Formula.subst
    unfold Formula.is_meta_var_or_all_def_in_env
    exact phi_ih h1 h2
  case def_ name args =>
    unfold Formula.is_meta_var_or_all_def_in_env at h1 
    unfold Formula.subst
    unfold Formula.is_meta_var_or_all_def_in_env
    simp only [List.length_map]
    exact h1

theorem lem_2_b (E : Env) (σ : Instantiation) (τ : MetaInstantiation) (phi : Formula)
    (h1 : (phi.subst σ τ).IsMetaVarOrAllDefInEnv E) : phi.IsMetaVarOrAllDefInEnv E :=
  by
  induction phi
  case meta_var_ X => unfold Formula.subst at h1 
  case false_ => unfold Formula.is_meta_var_or_all_def_in_env
  case pred_ name args => unfold Formula.subst at h1 
  case not_ phi phi_ih =>
    unfold Formula.subst at h1 
    unfold Formula.is_meta_var_or_all_def_in_env at h1 
    unfold Formula.is_meta_var_or_all_def_in_env
    exact phi_ih h1
  case imp_ phi psi phi_ih psi_ih =>
    unfold Formula.subst at h1 
    unfold Formula.is_meta_var_or_all_def_in_env at h1 
    cases h1
    unfold Formula.is_meta_var_or_all_def_in_env
    constructor
    · exact phi_ih h1_left
    · exact psi_ih h1_right
  case eq_ x y => unfold Formula.subst at h1 
  case forall_ x phi phi_ih =>
    unfold Formula.subst at h1 
    unfold Formula.is_meta_var_or_all_def_in_env at h1 
    unfold Formula.is_meta_var_or_all_def_in_env
    exact phi_ih h1
  case def_ name args =>
    unfold Formula.subst at h1 
    unfold Formula.is_meta_var_or_all_def_in_env at h1 
    simp only [List.length_map] at h1 
    unfold Formula.is_meta_var_or_all_def_in_env
    exact h1

theorem lem_3 (E : Env) (Γ : List (VarName × MetaVarName)) (Δ : List Formula) (phi : Formula)
    (h1 : IsProof E Γ Δ phi) : phi.IsMetaVarOrAllDefInEnv E :=
  by
  induction h1
  case hyp h1_Γ h1_Δ h1_phi h1_1 h1_2 => exact h1_1
  case mp h1_Γ h1_Δ h1_phi h1_psi h1_1 h1_2 h1_ih_1
    h1_ih_2 =>
    unfold Formula.is_meta_var_or_all_def_in_env at h1_ih_2 
    cases h1_ih_2
    exact h1_ih_2_right
  case prop_1 h1_Γ h1_Δ h1_phi h1_psi h1_1
    h1_2 =>
    unfold Formula.is_meta_var_or_all_def_in_env at *
    repeat'
      first
      | constructor
      | assumption
  case prop_2 h1_Γ h1_Δ h1_phi h1_psi h1_chi h1_1 h1_2
    h1_3 =>
    unfold Formula.is_meta_var_or_all_def_in_env at *
    repeat'
      first
      | constructor
      | assumption
  case prop_3 h1_Γ h1_Δ h1_phi h1_psi h1_1
    h1_2 =>
    unfold Formula.is_meta_var_or_all_def_in_env at *
    repeat'
      first
      | constructor
      | assumption
  case gen h1_Γ h1_Δ h1_phi h1_x h1_1
    h1_ih =>
    unfold Formula.is_meta_var_or_all_def_in_env at *
    repeat'
      first
      | constructor
      | assumption
  case pred_1 h1_Γ h1_Δ h1_phi h1_psi h1_x h1_1
    h1_2 =>
    unfold Formula.is_meta_var_or_all_def_in_env at *
    repeat'
      first
      | constructor
      | assumption
  case pred_2 h1_Γ h1_Δ h1_phi h1_x h1_1
    h1_2 =>
    unfold Formula.is_meta_var_or_all_def_in_env at *
    repeat'
      first
      | constructor
      | assumption
  case eq_1 h1_Γ h1_Δ h1_x h1_y h1_1 => unfold exists_
  case eq_2 h1_Γ h1_Δ h1_x h1_y
    h1_z =>
    unfold Formula.is_meta_var_or_all_def_in_env
    simp only [and_self_iff]
  /-
    case mm0.is_proof.eq_3 : h1_Γ h1_Δ h1_n h1_name h1_xs h1_ys
    { admit },
  -/
  case thm h1_Γ h1_Γ' h1_Δ h1_Δ' h1_phi h1_σ h1_τ h1_1 h1_2 h1_3 h1_4 h1_ih_1 h1_ih_2 =>
    exact lem_2_a E h1_σ h1_τ h1_phi h1_ih_2 h1_1
  case conv h1_Γ h1_Δ h1_phi h1_phi' h1_1 h1_2 h1_3 h1_ih => exact h1_1

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem lem_4 {D : Type} (P : PredInterpretation D) (M : MetaValuation D) (E : Env)
    (d : Definition_) (name : VarName) (args : List VarName) (V : Valuation D) (h1 : E.WF)
    (h2 : d ∈ E) (h3 : Name = d.Name ∧ args.length = d.args.length) :
    Holds D P M E d.q (Function.updateList V (List.zip d.args (List.map V args))) ↔
      Holds D P M E (def_ Name args) V :=
  by
  induction E
  case nil =>
    simp only [List.not_mem_nil] at h2 
    contradiction
  case cons hd tl
    ih =>
    have s1 : env.nodup_ (hd::tl) := env_well_formed_imp_nodup (hd::tl) h1
    unfold env.well_formed at h1 
    cases h1
    cases h1_right
    simp only [List.mem_cons] at h2 
    have s2 : ∃ E1 : env, (hd::tl) = E1 ++ tl
    apply Exists.intro [hd]
    simp only [List.singleton_append, eq_self_iff_true, and_self_iff]
    simp only [holds_not_nil_def]
    split_ifs
    · cases h2
      · rw [h2]
        exact
          holds_env_ext P M tl (hd::tl) hd.q (Function.updateList V (hd.args.zip (List.map V args)))
            s2 h1_right_left s1
      · cases h
        cases h3
        have s3 : hd.name = d.name
        rw [← h_left]
        exact h3_left
        have s4 : hd.args.length = d.args.length
        rw [← h_right]
        exact h3_right
        exfalso
        exact h1_left d h2 s3 s4
    · cases h2
      · simp only [not_and] at h 
        rw [← h2] at h 
        cases h3
        exfalso
        exact h h3_left h3_right
      · specialize ih h1_right_right h2
        rw [← ih]
        exact
          holds_env_ext P M tl (hd::tl) d.q (Function.updateList V (d.args.zip (List.map V args)))
            s2 (def_in_env_imp_is_meta_var_or_all_def_in_env tl d h1_right_right h2) s1

theorem holds_conv {D : Type} (P : PredInterpretation D) (M : MetaValuation D) (E : Env)
    (phi phi' : Formula) (V : Valuation D) (h1 : E.WF) (h2 : IsConv E phi phi') :
    Holds D P M E phi V ↔ Holds D P M E phi' V :=
  by
  induction h2 generalizing V
  case conv_refl h2 V => rfl
  case conv_symm h2_phi h2_phi' h2_1 h2_ih V =>
    symm
    exact h2_ih V
  case conv_trans h2_phi h2_phi' h2_phi'' h2_1 h2_2 h2_ih_1 h2_ih_2
    V =>
    trans holds D P M E h2_phi' V
    exact h2_ih_1 V
    exact h2_ih_2 V
  case conv_not h2_phi h2_phi' h2_1 h2_ih V =>
    simp only [holds_not]
    apply not_congr
    exact h2_ih V
  case conv_imp h2_phi h2_phi' h2_psi h2_psi' h2_1 h2_2 h2_ih_1 h2_ih_2
    V =>
    simp only [holds_imp]
    apply imp_congr
    · exact h2_ih_1 V
    · exact h2_ih_2 V
  case conv_forall h2_x h2_phi h2_phi' h2_1 h2_ih
    V =>
    simp only [holds_forall]
    apply forall_congr'
    intro a
    exact h2_ih (Function.update V h2_x a)
  case conv_unfold d σ h2 V =>
    obtain ⟨σ', a1⟩ := σ.2
    have s1 : Formula.is_meta_var_or_all_def_in_env E d.q :=
      def_in_env_imp_is_meta_var_or_all_def_in_env E d h1 h2
    rw [← holds_subst P M E σ σ' meta_var_ d.q V s1 a1]
    have s2 : d.name = d.name ∧ (List.map σ.val d.args).length = d.args.length
    simp only [eq_self_iff_true, List.length_map, and_self_iff]
    rw [← lem_4 P M E d d.name (List.map σ.val d.args) V h1 h2 s2]
    have s3 : d.q.meta_var_set = ∅ := no_meta_var_imp_meta_var_set_is_empty d.q d.args d.nf
    rw [holds_meta_valuation_ext_no_meta_var P
        (fun (X' : meta_var_name) (V' : Valuation D) => holds D P M E (meta_var_ X') (V' ∘ σ')) M E
        (V ∘ σ.val) d.q s3]
    apply
      holds_valuation_ext P M E
        (Function.updateList V (d.args.zip (List.map V (List.map σ.val d.args)))) (V ∘ σ.val) d.q
        d.args d.nf
    intro v a2
    simp only [List.map_map, Function.comp_apply]
    exact Function.updateList_zip_map_mem V (V ∘ σ.val) d.args v a2

theorem holds_isProof {D : Type} (P : PredInterpretation D) (M : MetaValuation D) (E : Env)
    (Γ : List (VarName × MetaVarName)) (Δ : List Formula) (phi : Formula) (h1 : IsProof E Γ Δ phi)
    (h2 : E.WF)
    (nf : ∀ (v : VarName) (X : MetaVarName), (v, X) ∈ Γ → IsnotFree D P M E v (meta_var_ X))
    (hyp : ∀ (psi : Formula) (V : Valuation D), psi ∈ Δ → Holds D P M E psi V) :
    ∀ V : Valuation D, Holds D P M E phi V :=
  by
  induction h1 generalizing M
  case hyp h1_Γ h1_Δ h1_phi h1_1 h1_2 M nf hyp =>
    intro V
    exact hyp h1_phi V h1_2
  case mp h1_Γ h1_Δ h1_phi h1_psi h1_1 h1_2 h1_ih_1 h1_ih_2 M nf
    hyp =>
    simp only [holds_imp] at h1_ih_2 
    intro V
    exact h1_ih_2 M nf hyp V (h1_ih_1 M nf hyp V)
  case prop_1 h1_Γ h1_Δ h1_phi h1_psi h1_1 h1_2 M nf
    hyp =>
    simp only [holds_imp]
    intro V a1 a2
    exact a1
  case prop_2 h1_Γ h1_Δ h1_phi h1_psi h1_chi h1_1 h1_2 h1_3 M nf
    hyp =>
    simp only [holds_imp]
    intro V a1 a2 a3
    exact a1 a3 (a2 a3)
  case prop_3 h1_Γ h1_Δ h1_phi h1_psi h1_1 h1_2 M nf
    hyp =>
    simp only [holds_imp, holds_not]
    intro V a1 a2
    by_contra contra
    exact a1 contra a2
  case gen h1_Γ h1_Δ h1_phi h1_x h1_1 h1_ih M nf
    hyp =>
    simp only [holds_forall]
    intro V a
    exact h1_ih M nf hyp (Function.update V h1_x a)
  case pred_1 h1_Γ h1_Δ h1_phi h1_psi h1_x h1_1 h1_2 M nf
    hyp =>
    simp only [holds_imp, holds_forall]
    intro V a1 a2 a
    exact a1 a (a2 a)
  case pred_2 h1_Γ h1_Δ h1_phi h1_x h1_1 h1_2 M nf
    hyp =>
    have s1 : is_notFree D P M E h1_x h1_phi :=
      notFree_imp_is_notFree P M E h1_Γ h1_x h1_phi h1_2 (nf h1_x)
    simp only [holds_imp, holds_forall]
    intro V a1 a
    unfold is_notFree at s1 
    rw [← s1 V a]
    exact a1
  case eq_1 h1_Γ h1_Δ h1_x h1_y h1_1 M nf
    hyp =>
    unfold exists_
    simp only [holds_not, holds_forall, holds_eq, Function.update_same, not_forall,
      Classical.not_not]
    intro V
    apply Exists.intro (V h1_y)
    symm
    exact Function.update_noteq h1_1 (V h1_y) V
  case eq_2 h1_Γ h1_Δ h1_x h1_y h1_z M nf
    hyp =>
    simp only [holds_imp, holds_eq]
    intro V a1 a2
    trans V h1_x
    · symm
      exact a1
    · exact a2
  /-
    case mm0.is_proof.eq_3 : h1_Γ h1_Δ h1_n h1_name h1_xs h1_ys M nf hyp
    { admit },
  -/
  case thm h1_Γ h1_Γ' h1_Δ h1_Δ' h1_phi h1_σ h1_τ h1_1 h1_2 h1_3 h1_4 h1_ih_1 h1_ih_2 M nf
    hyp =>
    obtain ⟨σ', a1⟩ := h1_σ.2
    dsimp only at h1_ih_1 
    have s1 : Formula.is_meta_var_or_all_def_in_env E h1_phi := lem_3 E h1_Γ h1_Δ h1_phi h1_4
    intro V
    rw [← holds_subst P M E h1_σ σ' h1_τ h1_phi V s1 a1]
    apply h1_ih_2
    · intro v X a2
      exact lem_1 P M E h1_Γ h1_Γ' h1_σ σ' h1_τ a1 nf h1_2 v X a2
    · intro psi V' a2
      have s2 : Formula.is_meta_var_or_all_def_in_env E psi
      apply lem_2_b E h1_σ h1_τ
      apply lem_3 E h1_Γ' h1_Δ' (Formula.subst h1_σ h1_τ psi)
      exact h1_3 psi a2
      have s3 :
        ∀ V'' : Valuation D,
          holds D P
            (fun (X' : meta_var_name) (V' : Valuation D) => holds D P M E (h1_τ X') (V' ∘ σ')) E psi
            (V'' ∘ h1_σ.val)
      intro V''
      rw [holds_subst P M E h1_σ σ' h1_τ psi V'' s2 a1]
      exact h1_ih_1 psi a2 M nf hyp V''
      specialize s3 (V' ∘ σ')
      rw [Function.comp.assoc] at s3 
      rw [a1.right] at s3 
      simp only [Function.comp.right_id] at s3 
      exact s3
  case conv h1_Γ h1_Δ h1_phi h1_phi' h1_1 h1_2 h1_3 h1_ih M nf
    hyp =>
    intro V
    have s1 : holds D P M E h1_phi V := h1_ih M nf hyp V
    rw [← holds_conv P M E h1_phi h1_phi' V h2 h1_3]
    exact s1

end Mm0

