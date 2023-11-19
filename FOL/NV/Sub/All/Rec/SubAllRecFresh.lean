import FOL.NV.Formula
import FOL.NV.Binders
import FOL.NV.Semantics
import FOL.NV.Fresh

import FOL.NV.Sub.All.Rec.SubAllRecAdmits
import FOL.NV.Alpha

import FOL.FunctionUpdateITE
import FOL.Tactics


namespace FOL

namespace NV

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


lemma lem_1
  (σ : VarName → VarName)
  (c : Char)
  (F : Formula)
  (x : VarName)
  (h1 : ∀ τ : VarName → VarName, (subFresh τ c F).freeVarSet = F.freeVarSet.image τ) :
  let x' :=
    if ∃ (y : VarName), y ∈ F.freeVarSet \ {x} ∧ σ y = x
    then fresh x c (subFresh (Function.updateITE σ x x) c F).freeVarSet
    else x
  x' ∉ (F.freeVarSet \ {x}).image σ :=
  by
  have s1 : (F.freeVarSet \ {x}).image σ ⊆ (subFresh (Function.updateITE σ x x) c F).freeVarSet
  calc
        (F.freeVarSet \ {x}).image σ

    _ = (F.freeVarSet \ {x}).image (Function.updateITE σ x x) :=
      by
      apply Finset.image_congr
      unfold Set.EqOn
      intro y a1
      unfold Function.updateITE
      simp at a1
      cases a1
      case _ a1_left a1_right =>
        simp only [if_neg a1_right]

    _ ⊆ F.freeVarSet.image (Function.updateITE σ x x) :=
      by
      apply Finset.image_subset_image
      exact Finset.sdiff_subset (freeVarSet F) {x}

    _ = (subFresh (Function.updateITE σ x x) c F).freeVarSet :=
      by
      symm
      exact h1 (Function.updateITE σ x x)

  split
  case inl c1 =>
    obtain s2 := fresh_not_mem x c (freeVarSet (subFresh (Function.updateITE σ x x) c F))
    exact Finset.not_mem_mono s1 s2
  case inr c1 =>
    simp at c1
    simp
    exact c1


lemma lem_2
  {α β : Type}
  [DecidableEq α]
  [DecidableEq β]
  (S : Finset α)
  (x : α)
  (x' : β)
  (f : α → β)
  (h1 : f x = x') :
  (Finset.image f S) \ {x'} =
  (Finset.image f (S \ {x})) \ {x'} :=
  by
  subst h1
  apply Finset.ext
  intro a
  simp
  intro a1
  constructor
  · intro a2
    apply Exists.elim a2
    intro b a3
    apply Exists.intro b
    cases a3
    case _ a3_left a3_right =>
      subst a3_right
      tauto
  · intro a2
    apply Exists.elim a2
    intro b a3
    apply Exists.intro b
    cases a3
    case _ a3_left a3_right =>
      subst a3_right
      tauto


lemma lem_3
  {α β : Type}
  [DecidableEq α]
  [DecidableEq β]
  (S : Finset α)
  (x : α)
  (x' : β)
  (f : α → β) :
  ((S \ {x}).image (Function.updateITE f x x')) =
  ((S \ {x}).image f) :=
  by
  apply Finset.image_congr
  unfold Set.EqOn
  intro a a1
  simp at a1
  unfold Function.updateITE
  cases a1
  case _ a1_left a1_right =>
    simp only [if_neg a1_right]


theorem lem_4
  (σ : VarName → VarName)
  (c : Char)
  (F : Formula) :
  (subFresh σ c F).freeVarSet = F.freeVarSet.image σ :=
  by
  induction F generalizing σ
  case pred_const_ X xs | pred_var_ X xs | eq_ x y | def_ X xs =>
    unfold subFresh
    unfold freeVarSet
    apply Finset.ext
    intro a
    simp
  case true_ | false_ =>
    unfold subFresh
    unfold freeVarSet
    simp
  case not_ phi phi_ih =>
    unfold subFresh
    unfold freeVarSet
    exact phi_ih σ
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold subFresh
    unfold freeVarSet
    simp only [Finset.image_union]
    congr!
    · exact phi_ih σ
    · exact psi_ih σ
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    let x' : VarName :=
    if ∃ (y : VarName), y ∈ phi.freeVarSet \ {x} ∧ σ y = x
    then fresh x c ((subFresh (Function.updateITE σ x x) c phi).freeVarSet)
    else x
    calc
        (subFresh σ c (forall_ x phi)).freeVarSet
    _ = (forall_ x' (subFresh (Function.updateITE σ x x') c phi)).freeVarSet := by simp only [subFresh]

    _ = (subFresh (Function.updateITE σ x x') c phi).freeVarSet \ {x'} := by simp only [freeVarSet]

    _ = (phi.freeVarSet.image (Function.updateITE σ x x')) \ {x'} := by simp only [phi_ih (Function.updateITE σ x x')]

    _ = ((phi.freeVarSet \ {x}).image (Function.updateITE σ x x')) \ {x'} :=
      by
      apply lem_2
      unfold Function.updateITE
      simp

    _ = ((phi.freeVarSet \ {x}).image σ) \ {x'} :=
      by
      congr! 1
      apply lem_3

    _ = (phi.freeVarSet \ {x}).image σ :=
      by
      apply Finset.sdiff_singleton_eq_self
      exact lem_1 σ c phi x phi_ih


theorem substitution_fun_theorem'
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
    unfold subFresh
    simp only [Holds]
    simp
  case true_ | false_ =>
    unfold subFresh
    simp only [Holds]
  case not_ phi phi_ih =>
    unfold subFresh
    simp only [Holds]
    congr! 1
    exact phi_ih V σ
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold subFresh
    simp only [Holds]
    congr! 1
    · exact phi_ih V σ
    · exact psi_ih V σ
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    let x' :=
      if ∃ y ∈ phi.freeVarSet \ {x}, σ y = x
      then fresh x c (subFresh (Function.updateITE σ x x) c phi).freeVarSet
      else x

    have s1 : ∀ (a : D) (z : VarName), z ∈ phi.freeVarSet → ((Function.updateITE V x' a) ∘ (Function.updateITE σ x x')) z = (Function.updateITE (V ∘ σ) x a) z
    intro a z h1
    by_cases h2 : z = x
    case pos =>
      subst h2
      unfold Function.updateITE
      simp
    case neg =>
      have s3 : x' ∉ (phi.freeVarSet \ {x}).image σ
      apply lem_1
      intro τ
      exact lem_4 τ c phi

      have s4 : σ z ∈ (phi.freeVarSet \ {x}).image σ
      apply Finset.mem_image_of_mem
      simp
      tauto

      have s5 : ¬ σ z = x'
      intro contra
      apply s3
      simp only [<- contra]
      exact s4

      unfold Function.updateITE
      simp (config := {zeta := false})
      simp (config := {zeta := false}) only [if_neg h2]
      split_ifs
      case pos c1 =>
        tauto
      case neg c1 =>
        rfl

    simp only [subFresh]
    simp only [Holds]
    first | apply forall_congr' | apply exists_congr
    intro a
    simp only [phi_ih]
    apply Holds_coincide_Var
    intro v a1
    apply s1
    simp only [isFreeIn_iff_mem_freeVarSet] at a1
    exact a1

  case def_ X xs =>
    induction E
    case nil =>
      unfold subFresh
      simp only [Holds]
    case cons E_hd E_tl E_ih =>
      unfold subFresh at E_ih

      unfold subFresh
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


theorem sub_valid
  (σ : VarName → VarName)
  (c : Char)
  (phi : Formula)
  (h1 : IsValid phi) :
  IsValid (subFresh σ c phi) :=
  by
  unfold IsValid at h1

  unfold IsValid
  intros D I V E
  simp only [substitution_fun_theorem']
  apply h1

--------------------------------------------------

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
    unfold subFresh
    unfold Formula.length
    simp only [phi_ih]
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold subFresh
    unfold Formula.length
    simp only [phi_ih σ]
    simp only [psi_ih σ]
  case forall_ x phi phi_ih | exists_ x phi_ih =>
    unfold subFresh
    unfold Formula.length
    simp
    apply phi_ih
  all_goals
    unfold subFresh
    unfold Formula.length
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
  (τ : VarName → VarName)
  (binders : Finset VarName)
  (c : Char) :
  Formula → Formula
  | pred_const_ X xs => pred_const_ X (xs.map τ)
  | pred_var_ X xs => pred_var_ X (xs.map τ)
  | eq_ x y => eq_ (τ x) (τ y)
  | true_ => true_
  | false_ => false_
  | not_ phi => sub_alpha σ τ binders c phi
  | imp_ phi psi =>
      imp_
      (sub_alpha σ τ binders c phi)
      (sub_alpha σ τ binders c psi)
  | and_ phi psi =>
      and_
      (sub_alpha σ τ binders c phi)
      (sub_alpha σ τ binders c psi)
  | or_ phi psi =>
      or_
      (sub_alpha σ τ binders c phi)
      (sub_alpha σ τ binders c psi)
  | iff_ phi psi =>
      iff_
      (sub_alpha σ τ binders c phi)
      (sub_alpha σ τ binders c psi)
  | forall_ x phi =>
      let free := phi.freeVarSet \ (binders ∪ {x})
      let free_after_sub := free.image σ
      let captured := free_after_sub ∩ (binders ∪ {x})
      let x' :=
        if captured = ∅
        then x
        else fresh x c (free_after_sub ∪ free)
      forall_ x' (sub_alpha σ (Function.updateITE τ x x') (binders ∪ {x'}) c phi)
  | exists_ x phi =>
      let free := phi.freeVarSet \ (binders ∪ {x})
      let free_after_sub := free.image σ
      let captured := free_after_sub ∩ (binders ∪ {x})
      let x' :=
        if captured = ∅
        then x
        else fresh x c (free_after_sub ∪ free)
      forall_ x' (sub_alpha σ (Function.updateITE τ x x') (binders ∪ {x'}) c phi)
  | def_ X xs => def_ X (xs.map τ)


def sub_alpha'
  (σ : VarName → VarName)
  (τ : VarName → VarName)
  (c : Char) :
  Formula → (Formula × Formula)
| pred_const_ X xs => (pred_const_ X (xs.map σ), pred_const_ X (xs.map τ))
| pred_var_ X xs => (pred_var_ X (xs.map σ), pred_var_ X (xs.map τ))
| eq_ x y => (eq_ (σ x) (σ y), eq_ (τ x) (τ y))
| true_ => (true_, true_)
| false_ => (false_, false_)
| not_ phi => (not_ (sub_alpha' σ τ c phi).fst, not_ (sub_alpha' σ τ c phi).snd)
| imp_ phi psi => ((imp_ (sub_alpha' σ τ c phi).fst (sub_alpha' σ τ c psi).fst), (imp_ (sub_alpha' σ τ c phi).snd (sub_alpha' σ τ c psi).snd))
| and_ phi psi => ((and_ (sub_alpha' σ τ c phi).fst (sub_alpha' σ τ c psi).fst), (and_ (sub_alpha' σ τ c phi).snd (sub_alpha' σ τ c psi).snd))
| or_ phi psi => ((or_ (sub_alpha' σ τ c phi).fst (sub_alpha' σ τ c psi).fst), (or_ (sub_alpha' σ τ c phi).snd (sub_alpha' σ τ c psi).snd))
| iff_ phi psi => ((iff_ (sub_alpha' σ τ c phi).fst (sub_alpha' σ τ c psi).fst), (iff_ (sub_alpha' σ τ c phi).snd (sub_alpha' σ τ c psi).snd))
| forall_ x phi =>
  let x' : VarName :=
    if ∃ (y : VarName), y ∈ phi.freeVarSet \ {x} ∧ σ y = x
    then fresh x c ((sub_alpha' (Function.updateITE σ x x) τ c phi).fst.freeVarSet)
    else x
  let phi' := (sub_alpha' (Function.updateITE σ x x') (Function.updateITE τ x x') c phi)
  (forall_ x' phi'.fst, forall_ x' phi'.snd)
| exists_ x phi =>
  let x' : VarName :=
    if ∃ (y : VarName), y ∈ phi.freeVarSet \ {x} ∧ σ y = x
    then fresh x c ((sub_alpha' (Function.updateITE σ x x) τ c phi).fst.freeVarSet)
    else x
  let phi' := (sub_alpha' (Function.updateITE σ x x') (Function.updateITE τ x x') c phi)
  (exists_ x' phi'.fst, exists_ x' phi'.snd)
| def_ X xs => (def_ X (xs.map σ), def_ X (xs.map τ))



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
#eval admitsFunAux σ ∅ F''

#eval F' = F''

#eval fastReplaceFreeFun σ F'' = subFresh σ c F
#eval fastReplaceFreeFun σ F' = subFresh σ c F
