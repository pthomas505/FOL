import FOL.Finset
import FOL.FunctionUpdateITE
import FOL.NV.Formula
import FOL.NV.Fresh
import FOL.NV.Semantics


set_option autoImplicit false


namespace FOL.NV.Sub.All.Rec

open Formula


def subFresh
  (σ : VarName → VarName)
  (c : Char) :
  Formula → Formula
  | pred_const_ X xs => pred_const_ X (xs.map σ)
  | pred_var_ X xs => pred_var_ X (xs.map σ)
  | eq_ x y => eq_ (σ x) (σ y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (subFresh σ c phi)
  | imp_ phi psi => imp_ (subFresh σ c phi) (subFresh σ c psi)
  | and_ phi psi => and_ (subFresh σ c phi) (subFresh σ c psi)
  | or_ phi psi => or_ (subFresh σ c phi) (subFresh σ c psi)
  | iff_ phi psi => iff_ (subFresh σ c phi) (subFresh σ c psi)
  | forall_ x phi =>
    let x' : VarName :=
      if ∃ (y : VarName), y ∈ phi.freeVarSet \ {x} ∧ σ y = x
      then fresh x c ((subFresh (Function.updateITE σ x x) c phi).freeVarSet)
      else x
    forall_ x' (subFresh (Function.updateITE σ x x') c phi)
  | exists_ x phi =>
    let x' : VarName :=
      if ∃ (y : VarName), y ∈ phi.freeVarSet \ {x} ∧ σ y = x
      then fresh x c ((subFresh (Function.updateITE σ x x) c phi).freeVarSet)
      else x
    exists_ x' (subFresh (Function.updateITE σ x x') c phi)
  | def_ X xs => def_ X (xs.map σ)


theorem lem_1
  (σ : VarName → VarName)
  (c : Char)
  (F : Formula) :
  (subFresh σ c F).freeVarSet = F.freeVarSet.image σ :=
  by
  induction F generalizing σ
  all_goals
    simp only [subFresh]
    simp only [freeVarSet]
  case pred_const_ X xs | pred_var_ X xs | eq_ x y | def_ X xs =>
    apply Finset.ext
    intro a
    simp
  case true_ | false_ =>
    simp
  case not_ phi phi_ih =>
    exact phi_ih σ
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [Finset.image_union]
    congr!
    · exact phi_ih σ
    · exact psi_ih σ
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [phi_ih]

    split_ifs
    case _ c1 =>
      obtain s0 := fresh_not_mem x c (Finset.image (Function.updateITE σ x x) (freeVarSet phi))

      generalize (
      fresh x c (Finset.image (Function.updateITE σ x x) (freeVarSet phi)) ) = x' at *

      obtain s1 := Function.updateITE_not_mem_set (phi.freeVarSet \ {x}) σ x x
      simp at s1
      simp only [← s1]

      obtain s2 := Finset.image_sdiff_singleton phi.freeVarSet x x' (Function.updateITE σ x x')
      simp only [Function.updateITE] at s2
      simp at s2
      simp only [s2]
      clear s2

      have s3 : Finset.image (Function.updateITE σ x x) (freeVarSet phi \ {x}) ⊆ Finset.image (Function.updateITE σ x x) (freeVarSet phi)
      apply Finset.image_subset_image
      simp

      have s4 : x' ∉ Finset.image (Function.updateITE σ x x) (freeVarSet phi \ {x})
      apply Finset.not_mem_mono s3 s0

      obtain s5 := Finset.sdiff_singleton_eq_self s4
      clear s3
      clear s4
      rw [<- s5]

      obtain s6 := Finset.image_congr_update_ite phi.freeVarSet x x x' σ
      simp only [s6]
    case _ c1 =>
      simp at c1

      have s1 : Finset.image σ (freeVarSet phi \ {x}) = Finset.image (Function.updateITE σ x x) (freeVarSet phi \ {x})
      simp only [Finset.image_sdiff_singleton_updateITE]

      simp only [s1]
      clear s1

      have s2 : Finset.image (Function.updateITE σ x x) (freeVarSet phi) \ {x} = Finset.image (Function.updateITE σ x x) (freeVarSet phi \ {x}) \ {x}
      apply Finset.image_sdiff_singleton
      simp only [Function.updateITE]
      simp

      simp only [s2]
      clear s2

      have s3 : x ∉ Finset.image (Function.updateITE σ x x) (freeVarSet phi \ {x})
      simp only [Finset.mem_image]
      simp
      simp only [Function.updateITE]
      simp
      tauto

      simp only [Finset.sdiff_singleton_eq_self s3]


theorem substitution_theorem
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (E : Env)
  (σ : VarName → VarName)
  (c : Char)
  (F : Formula) :
  Holds D I V E (subFresh σ c F) ↔
    Holds D I (V ∘ σ) E F :=
  by
  induction F generalizing σ V
  case pred_const_ X xs | pred_var_ X xs | eq_ x y =>
    simp only [subFresh]
    simp only [Holds]
    simp
  case true_ | false_ =>
    simp only [subFresh]
    simp only [Holds]
  case not_ phi phi_ih =>
    simp only [subFresh]
    simp only [Holds]
    congr! 1
    exact phi_ih V σ
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [subFresh]
    simp only [Holds]
    congr! 1
    · exact phi_ih V σ
    · exact psi_ih V σ
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [subFresh]
    simp only [Holds]

    first | apply forall_congr' | apply exists_congr
    intro d

    simp only [phi_ih]
    apply Holds_coincide_Var
    intro v a1

    simp
    split_ifs
    case _ c1 =>
      set x' := (fresh x c (freeVarSet (subFresh (Function.updateITE σ x x) c phi)))
      by_cases c2 : v = x
      · simp only [c2]
        simp only [Function.updateITE]
        simp
      · by_cases c3 : σ v = x'
        · simp only [Function.updateITE]
          simp only [if_neg c2]
          simp
          intro a2

          obtain s1 := lem_1 (Function.updateITE σ x x) c phi
          simp only [s1] at a2

          obtain s2 := fresh_not_mem x c (Finset.image (Function.updateITE σ x x) (freeVarSet phi))

          simp only [← a2] at s2
          exfalso
          apply s2
          apply Finset.mem_image_update
          · exact c2
          · simp only [← isFreeIn_iff_mem_freeVarSet]
            exact a1
        · simp only [Function.updateITE]
          simp only [if_neg c2]
          simp only [if_neg c3]
          simp
    case _ c1 =>
      by_cases c2 : v = x
      · subst c2
        simp only [Function.updateITE]
        simp
      · have s1 : ¬ σ v = x
        intro contra
        apply c1
        apply Exists.intro v
        constructor
        simp
        simp only [← isFreeIn_iff_mem_freeVarSet]
        tauto
        exact contra
        simp only [Function.updateITE]
        simp only [if_neg c2]
        simp only [if_neg s1]
        simp
  case def_ X xs =>
    induction E
    case nil =>
      simp only [subFresh]
      simp only [Holds]
    case cons E_hd E_tl E_ih =>
      simp only [subFresh] at E_ih

      simp only [subFresh]
      simp only [Holds]
      simp
      split_ifs
      case pos c1 =>
        apply Holds_coincide_Var
        intro v a1
        apply Function.updateListITE_map_mem_ext
        · simp
        · cases c1
          case _ c1_left c1_right =>
            symm
            exact c1_right
        · simp only [isFreeIn_iff_mem_freeVarSet] at a1
          simp only [← List.mem_toFinset]
          apply Finset.mem_of_subset E_hd.h1 a1
      case neg c1 =>
        exact E_ih


theorem substitution_is_valid
  (σ : VarName → VarName)
  (c : Char)
  (phi : Formula)
  (h1 : IsValid phi) :
  IsValid (subFresh σ c phi) :=
  by
  simp only [IsValid] at h1

  simp only [IsValid]
  intros D I V E
  simp only [substitution_theorem]
  apply h1

--------------------------------------------------

/-

def Formula.length : Formula → ℕ
  | pred_const_ _ _ => 0
  | pred_var_ _ _ => 0
  | eq_ _ _ => 0
  | true_ => 0
  | false_ => 0
  | not_ phi => 1 + phi.length
  | imp_ phi psi => 1 + phi.length + psi.length
  | and_ phi psi => 1 + phi.length + psi.length
  | or_ phi psi => 1 + phi.length + psi.length
  | iff_ phi psi => 1 + phi.length + psi.length
  | forall_ _ phi => 1 + phi.length
  | exists_ _ phi => 1 + phi.length
  | def_ _ _ => 0


lemma sub_formula_length_same
  (σ : VarName → VarName)
  (c : Char)
  (F : Formula) :
  (subFresh σ c F).length = F.length :=
  by
  induction F generalizing σ
  case not_ phi phi_ih =>
    simp only [subFresh]
    simp only [Formula.length]
    simp only [phi_ih]
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [subFresh]
    simp only [Formula.length]
    simp only [phi_ih σ]
    simp only [psi_ih σ]
  case forall_ x phi phi_ih | exists_ x phi_ih =>
    simp only [subFresh]
    simp only [Formula.length]
    simp
    apply phi_ih
  all_goals
    simp only [subFresh]
    simp only [Formula.length]
    simp

--------------------------------------------------

lemma SubId
  (c : Char)
  (F : Formula) :
  subFresh id c F = F :=
  by
  induction F
  case pred_const_ X xs | pred_var_ X xs | eq_ x y | def_ X xs =>
    simp only [subFresh]
    simp
  case true_ | false_ =>
    simp only [subFresh]
  case not_ phi phi_ih =>
    simp only [subFresh]
    congr!
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [subFresh]
    congr!
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [subFresh]
    simp
    simp only [Function.updateITE_id]
    exact phi_ih

--------------------------------------------------

def sub_alpha
  (σ : VarName → VarName)
  (α : VarName → VarName)
  (binders : Finset VarName)
  (c : Char) :
  Formula → Formula
  | pred_const_ X xs => pred_const_ X (xs.map α)
  | pred_var_ X xs => pred_var_ X (xs.map α)
  | eq_ x y => eq_ (α x) (α y)
  | true_ => true_
  | false_ => false_
  | not_ phi => sub_alpha σ α binders c phi
  | imp_ phi psi =>
      imp_
      (sub_alpha σ α binders c phi)
      (sub_alpha σ α binders c psi)
  | and_ phi psi =>
      and_
      (sub_alpha σ α binders c phi)
      (sub_alpha σ α binders c psi)
  | or_ phi psi =>
      or_
      (sub_alpha σ α binders c phi)
      (sub_alpha σ α binders c psi)
  | iff_ phi psi =>
      iff_
      (sub_alpha σ α binders c phi)
      (sub_alpha σ α binders c psi)
  | forall_ x phi =>
      let free := phi.freeVarSet \ (binders ∪ {x})
      let replaced_free := free.image σ
      let captured := replaced_free ∩ (binders ∪ {x})
      let x' :=
        if captured = ∅
        then x
        else fresh x c (replaced_free ∪ free)
      forall_ x' (sub_alpha σ (Function.updateITE α x x') (binders ∪ {x'}) c phi)
  | exists_ x phi =>
      let free := phi.freeVarSet \ (binders ∪ {x})
      let replaced_free := free.image σ
      let captured := replaced_free ∩ (binders ∪ {x})
      let x' :=
        if captured = ∅
        then x
        else fresh x c (replaced_free ∪ free)
      exists_ x' (sub_alpha σ (Function.updateITE α x x') (binders ∪ {x'}) c phi)
  | def_ X xs => def_ X (xs.map α)


def sub_alpha'
  (σ : VarName → VarName)
  (α : VarName → VarName)
  (c : Char) :
  Formula → (Formula × Formula)
| pred_const_ X xs => (pred_const_ X (xs.map σ), pred_const_ X (xs.map α))
| pred_var_ X xs => (pred_var_ X (xs.map σ), pred_var_ X (xs.map α))
| eq_ x y => (eq_ (σ x) (σ y), eq_ (α x) (α y))
| true_ => (true_, true_)
| false_ => (false_, false_)
| not_ phi => (not_ (sub_alpha' σ α c phi).fst, not_ (sub_alpha' σ α c phi).snd)
| imp_ phi psi => ((imp_ (sub_alpha' σ α c phi).fst (sub_alpha' σ α c psi).fst), (imp_ (sub_alpha' σ α c phi).snd (sub_alpha' σ α c psi).snd))
| and_ phi psi => ((and_ (sub_alpha' σ α c phi).fst (sub_alpha' σ α c psi).fst), (and_ (sub_alpha' σ α c phi).snd (sub_alpha' σ α c psi).snd))
| or_ phi psi => ((or_ (sub_alpha' σ α c phi).fst (sub_alpha' σ α c psi).fst), (or_ (sub_alpha' σ α c phi).snd (sub_alpha' σ α c psi).snd))
| iff_ phi psi => ((iff_ (sub_alpha' σ α c phi).fst (sub_alpha' σ α c psi).fst), (iff_ (sub_alpha' σ α c phi).snd (sub_alpha' σ α c psi).snd))
| forall_ x phi =>
  let x' : VarName :=
    if ∃ (y : VarName), y ∈ phi.freeVarSet \ {x} ∧ σ y = x
    then fresh x c ((sub_alpha' (Function.updateITE σ x x) α c phi).fst.freeVarSet)
    else x
  let phi' := (sub_alpha' (Function.updateITE σ x x') (Function.updateITE α x x') c phi)
  (forall_ x' phi'.fst, forall_ x' phi'.snd)
| exists_ x phi =>
  let x' : VarName :=
    if ∃ (y : VarName), y ∈ phi.freeVarSet \ {x} ∧ σ y = x
    then fresh x c ((sub_alpha' (Function.updateITE σ x x) α c phi).fst.freeVarSet)
    else x
  let phi' := (sub_alpha' (Function.updateITE σ x x') (Function.updateITE α x x') c phi)
  (exists_ x' phi'.fst, exists_ x' phi'.snd)
| def_ X xs => (def_ X (xs.map σ), def_ X (xs.map α))



def c := '+'

def σ := (Function.updateITE id (VarName.mk "x") (VarName.mk "y"))

def F := (forall_ (VarName.mk "y++") (forall_ (VarName.mk "y") (pred_var_ (PredName.mk "X") [VarName.mk "x", VarName.mk "y++"])))

def F' := (sub_alpha' σ id c F).snd
def F'' := sub_alpha σ id ∅ c F

#eval F

#eval F'

#eval F''

#eval isAlphaEqv F F''

#eval subFresh σ c F''
#eval admitsAux σ ∅ F''

#eval F' = F''

#eval fastReplaceFree σ F'' = subFresh σ c F
#eval fastReplaceFree σ F' = subFresh σ c F

-/
