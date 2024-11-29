import MathlibExtra.Finset
import MathlibExtra.FunctionUpdateITE
import FOL.NV.Formula
import FOL.NV.Fresh
import FOL.NV.Semantics


set_option autoImplicit false


namespace FOL.NV.Sub.Var.All.Rec.Fresh

open Formula


/--
  sub σ c F := The simultaneous replacement of each free occurrence of any variable v in the formula F by σ v. The character c is used to generate fresh binding variables as needed to avoid free variable capture.
-/
def sub
  (σ : VarName_ → VarName_)
  (c : Char) :
  Formula → Formula
  | pred_const_ X xs => pred_const_ X (xs.map σ)
  | pred_var_ X xs => pred_var_ X (xs.map σ)
  | eq_ x y => eq_ (σ x) (σ y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (sub σ c phi)
  | imp_ phi psi => imp_ (sub σ c phi) (sub σ c psi)
  | and_ phi psi => and_ (sub σ c phi) (sub σ c psi)
  | or_ phi psi => or_ (sub σ c phi) (sub σ c psi)
  | iff_ phi psi => iff_ (sub σ c phi) (sub σ c psi)
  | forall_ x phi =>
    let x' : VarName_ :=
      if ∃ (y : VarName_), y ∈ phi.free_var_set \ {x} ∧ σ y = x
      then fresh x c ((sub (Function.updateITE σ x x) c phi).free_var_set)
      else x
    forall_ x' (sub (Function.updateITE σ x x') c phi)
  | exists_ x phi =>
    let x' : VarName_ :=
      if ∃ (y : VarName_), y ∈ phi.free_var_set \ {x} ∧ σ y = x
      then fresh x c ((sub (Function.updateITE σ x x) c phi).free_var_set)
      else x
    exists_ x' (sub (Function.updateITE σ x x') c phi)
  | def_ X xs => def_ X (xs.map σ)


lemma freeVarSet_sub_eq_freeVarSet_image
  (σ : VarName_ → VarName_)
  (c : Char)
  (F : Formula) :
  (sub σ c F).free_var_set = F.free_var_set.image σ :=
  by
  induction F generalizing σ
  all_goals
    simp only [sub]
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

    simp only [<- Finset.image_sdiff_singleton_updateITE phi.free_var_set x x σ]

    split_ifs
    case _ c1 =>
      obtain s1 := fresh_not_mem x c (Finset.image (Function.updateITE σ x x) (freeVarSet phi))

      generalize (
      fresh x c (Finset.image (Function.updateITE σ x x) (freeVarSet phi)) ) = x' at *

      have s2 : Finset.image (Function.updateITE σ x x) (freeVarSet phi \ {x}) ⊆ Finset.image (Function.updateITE σ x x) (freeVarSet phi)
      apply Finset.image_subset_image
      simp

      have s3 : x' ∉ Finset.image (Function.updateITE σ x x) (freeVarSet phi \ {x})
      apply Finset.not_mem_mono s2 s1

      calc
        Finset.image (Function.updateITE σ x x') (freeVarSet phi) \ {x'}
      = Finset.image (Function.updateITE σ x x') (freeVarSet phi \ {x}) \ {x'} :=
          by
          {
            apply Finset.image_sdiff_singleton phi.free_var_set x x' (Function.updateITE σ x x')
            simp only [Function.updateITE]
            simp
          }
      _ = Finset.image (Function.updateITE σ x x) (freeVarSet phi \ {x}) \ {x'} :=
          by simp only [Finset.image_congr_update_ite phi.free_var_set x x' x]
      _ = Finset.image (Function.updateITE σ x x) (freeVarSet phi \ {x}) :=
          by
            simp only [Finset.sdiff_singleton_eq_erase] at *
            exact Finset.erase_eq_of_not_mem s3
    case _ c1 =>
      simp at c1

      have s1 : Finset.image (Function.updateITE σ x x) (freeVarSet phi) \ {x} = Finset.image (Function.updateITE σ x x) (freeVarSet phi \ {x}) \ {x}
      apply Finset.image_sdiff_singleton
      simp only [Function.updateITE]
      simp

      simp only [s1]
      clear s1

      have s2 : x ∉ Finset.image (Function.updateITE σ x x) (freeVarSet phi \ {x})
      simp only [Finset.mem_image]
      simp
      simp only [Function.updateITE]
      simp
      tauto

      simp only [Finset.sdiff_singleton_eq_erase] at *
      exact Finset.erase_eq_of_not_mem s2

theorem substitution_theorem
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env)
  (σ : VarName_ → VarName_)
  (c : Char)
  (F : Formula) :
  holds D I V E (sub σ c F) ↔
    holds D I (V ∘ σ) E F :=
  by
  induction F generalizing σ V
  case pred_const_ X xs | pred_var_ X xs | eq_ x y =>
    simp only [sub]
    simp only [holds]
    simp
  case true_ | false_ =>
    simp only [sub]
    simp only [holds]
  case not_ phi phi_ih =>
    simp only [sub]
    simp only [holds]
    congr! 1
    exact phi_ih V σ
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [sub]
    simp only [holds]
    congr! 1
    · exact phi_ih V σ
    · exact psi_ih V σ
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [sub]
    simp only [holds]

    first | apply forall_congr' | apply exists_congr
    intro d

    simp only [phi_ih]
    apply holds_coincide_var
    intro v a1

    simp
    split_ifs
    case _ c1 =>
      obtain s0 := fresh_not_mem x c (freeVarSet (sub (Function.updateITE σ x x) c phi))

      generalize (fresh x c (freeVarSet (sub (Function.updateITE σ x x) c phi))) = x' at *
      by_cases c2 : v = x
      · simp only [c2]
        simp only [Function.updateITE]
        simp
      · by_cases c3 : σ v = x'
        · subst c3

          simp only [freeVarSet_sub_eq_freeVarSet_image] at s0

          have s1 : σ v ∈ Finset.image (Function.updateITE σ x x) (freeVarSet phi)
          apply Finset.mem_image_update
          · exact c2
          · simp only [← var_is_free_in_iff_mem_free_var_set]
            exact a1

          contradiction
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
        {
          intro contra
          apply c1
          apply Exists.intro v
          constructor
          · simp
            simp only [← var_is_free_in_iff_mem_free_var_set]
            tauto
          · exact contra
        }

        simp only [Function.updateITE]
        simp only [if_neg c2]
        simp only [if_neg s1]
        simp
  case def_ X xs =>
    induction E
    case nil =>
      simp only [sub]
      simp only [holds]
    case cons E_hd E_tl E_ih =>
      simp only [sub] at E_ih

      simp only [sub]
      simp only [holds]
      simp
      split_ifs
      case pos c1 =>
        apply holds_coincide_var
        intro v a1
        apply Function.updateListITE_map_mem_ext
        · simp
        · cases c1
          case _ c1_left c1_right =>
            symm
            exact c1_right
        · simp only [var_is_free_in_iff_mem_free_var_set] at a1
          simp only [← List.mem_toFinset]
          apply Finset.mem_of_subset E_hd.h1 a1
      case neg c1 =>
        exact E_ih


theorem substitution_is_valid
  (σ : VarName_ → VarName_)
  (c : Char)
  (F : Formula)
  (h1 : is_valid F) :
  is_valid (sub σ c F) :=
  by
  simp only [is_valid] at h1

  simp only [is_valid]
  intro D I V E
  simp only [substitution_theorem]
  apply h1


#lint

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
  (σ : VarName_ → VarName_)
  (c : Char)
  (F : Formula) :
  (sub σ c F).length = F.length :=
  by
  induction F generalizing σ
  case not_ phi phi_ih =>
    simp only [sub]
    simp only [Formula.length]
    simp only [phi_ih]
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [sub]
    simp only [Formula.length]
    simp only [phi_ih σ]
    simp only [psi_ih σ]
  case forall_ x phi phi_ih | exists_ x phi_ih =>
    simp only [sub]
    simp only [Formula.length]
    simp
    apply phi_ih
  all_goals
    simp only [sub]
    simp only [Formula.length]
    simp

--------------------------------------------------

lemma SubId
  (c : Char)
  (F : Formula) :
  sub id c F = F :=
  by
  induction F
  case pred_const_ X xs | pred_var_ X xs | eq_ x y | def_ X xs =>
    simp only [sub]
    simp
  case true_ | false_ =>
    simp only [sub]
  case not_ phi phi_ih =>
    simp only [sub]
    congr!
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [sub]
    congr!
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [sub]
    simp
    simp only [Function.updateITE_id]
    exact phi_ih

--------------------------------------------------

def sub_alpha
  (σ : VarName_ → VarName_)
  (α : VarName_ → VarName_)
  (binders : Finset VarName_)
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
      let free := phi.free_var_set \ (binders ∪ {x})
      let replaced_free := free.image σ
      let captured := replaced_free ∩ (binders ∪ {x})
      let x' :=
        if captured = ∅
        then x
        else fresh x c (replaced_free ∪ free)
      forall_ x' (sub_alpha σ (Function.updateITE α x x') (binders ∪ {x'}) c phi)
  | exists_ x phi =>
      let free := phi.free_var_set \ (binders ∪ {x})
      let replaced_free := free.image σ
      let captured := replaced_free ∩ (binders ∪ {x})
      let x' :=
        if captured = ∅
        then x
        else fresh x c (replaced_free ∪ free)
      exists_ x' (sub_alpha σ (Function.updateITE α x x') (binders ∪ {x'}) c phi)
  | def_ X xs => def_ X (xs.map α)


def sub_alpha'
  (σ : VarName_ → VarName_)
  (α : VarName_ → VarName_)
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
  let x' : VarName_ :=
    if ∃ (y : VarName_), y ∈ phi.free_var_set \ {x} ∧ σ y = x
    then fresh x c ((sub_alpha' (Function.updateITE σ x x) α c phi).fst.free_var_set)
    else x
  let phi' := (sub_alpha' (Function.updateITE σ x x') (Function.updateITE α x x') c phi)
  (forall_ x' phi'.fst, forall_ x' phi'.snd)
| exists_ x phi =>
  let x' : VarName_ :=
    if ∃ (y : VarName_), y ∈ phi.free_var_set \ {x} ∧ σ y = x
    then fresh x c ((sub_alpha' (Function.updateITE σ x x) α c phi).fst.free_var_set)
    else x
  let phi' := (sub_alpha' (Function.updateITE σ x x') (Function.updateITE α x x') c phi)
  (exists_ x' phi'.fst, exists_ x' phi'.snd)
| def_ X xs => (def_ X (xs.map σ), def_ X (xs.map α))



def c := '+'

def σ := (Function.updateITE id (VarName_.mk "x") (VarName_.mk "y"))

def F := (forall_ (VarName_.mk "y++") (forall_ (VarName_.mk "y") (pred_var_ (PredName_.mk "X") [VarName_.mk "x", VarName_.mk "y++"])))

def F' := (sub_alpha' σ id c F).snd
def F'' := sub_alpha σ id ∅ c F

#eval F

#eval F'

#eval F''

#eval isAlphaEqv F F''

#eval sub σ c F''
#eval admitsAux σ ∅ F''

#eval F' = F''

#eval fastReplaceFree σ F'' = sub σ c F
#eval fastReplaceFree σ F' = sub σ c F

-/
