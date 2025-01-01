import MathlibExtra.Finset
import MathlibExtra.FunctionUpdateITE
import FOL.NV.Formula
import FOL.NV.Fresh
import FOL.NV.Semantics
import FOL.NV.Sub.Var.All.Rec.Admits


set_option autoImplicit false


namespace FOL.NV.Sub.Var.All.Rec.Fresh

open Formula_


/--
  `sub_var_all_rec σ c F` := The simultaneous replacement of each free occurrence of any variable `v` in the formula `F` by `σ v`. The character `c` is used to generate fresh binding variables as needed to avoid free variable capture.
-/
def sub_var_all_rec
  (σ : VarName_ → VarName_)
  (c : Char) :
  Formula_ → Formula_
  | pred_const_ X xs => pred_const_ X (xs.map σ)
  | pred_var_ X xs => pred_var_ X (xs.map σ)
  | eq_ x y => eq_ (σ x) (σ y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (sub_var_all_rec σ c phi)
  | imp_ phi psi => imp_ (sub_var_all_rec σ c phi) (sub_var_all_rec σ c psi)
  | and_ phi psi => and_ (sub_var_all_rec σ c phi) (sub_var_all_rec σ c psi)
  | or_ phi psi => or_ (sub_var_all_rec σ c phi) (sub_var_all_rec σ c psi)
  | iff_ phi psi => iff_ (sub_var_all_rec σ c phi) (sub_var_all_rec σ c psi)
  | forall_ x phi =>
    let x' : VarName_ :=
      if ∃ (y : VarName_), y ∈ phi.free_var_set \ {x} ∧ σ y = x
      then fresh x c ((sub_var_all_rec (Function.updateITE σ x x) c phi).free_var_set)
      else x
    forall_ x' (sub_var_all_rec (Function.updateITE σ x x') c phi)
  | exists_ x phi =>
    let x' : VarName_ :=
      if ∃ (y : VarName_), y ∈ phi.free_var_set \ {x} ∧ σ y = x
      then fresh x c ((sub_var_all_rec (Function.updateITE σ x x) c phi).free_var_set)
      else x
    exists_ x' (sub_var_all_rec (Function.updateITE σ x x') c phi)
  | def_ X xs => def_ X (xs.map σ)


lemma sub_var_all_rec_free_var_set_eq_free_var_set_image
  (σ : VarName_ → VarName_)
  (c : Char)
  (F : Formula_) :
  (sub_var_all_rec σ c F).free_var_set = F.free_var_set.image σ :=
  by
  induction F generalizing σ
  all_goals
    simp only [sub_var_all_rec]
    simp only [free_var_set]
  case pred_const_ X xs | pred_var_ X xs | eq_ x y | def_ X xs =>
    ext a
    simp
  case true_ | false_ =>
    simp
  case not_ phi phi_ih =>
    apply phi_ih
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [Finset.image_union]
    congr!
    · apply phi_ih
    · apply psi_ih
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [phi_ih]

    simp only [<- Finset.image_sdiff_singleton_updateITE phi.free_var_set x x σ]

    split_ifs
    case _ c1 =>
      obtain s1 := fresh_not_mem x c (Finset.image (Function.updateITE σ x x) (free_var_set phi))

      generalize ( fresh x c (Finset.image (Function.updateITE σ x x) (free_var_set phi)) ) = x' at *

      have s2 : Finset.image (Function.updateITE σ x x) (free_var_set phi \ {x}) ⊆ Finset.image (Function.updateITE σ x x) (free_var_set phi) :=
      by
        apply Finset.image_subset_image
        simp

      have s3 : x' ∉ Finset.image (Function.updateITE σ x x) (free_var_set phi \ {x}) :=
      by
        apply Finset.not_mem_mono s2 s1

      calc
        Finset.image (Function.updateITE σ x x') (free_var_set phi) \ {x'}
      = Finset.image (Function.updateITE σ x x') (free_var_set phi \ {x}) \ {x'} :=
          by
            apply Finset.image_sdiff_singleton phi.free_var_set x x' (Function.updateITE σ x x')
            simp only [Function.updateITE]
            simp
      _ = Finset.image (Function.updateITE σ x x) (free_var_set phi \ {x}) \ {x'} :=
          by simp only [Finset.image_congr_update_ite phi.free_var_set x x' x]
      _ = Finset.image (Function.updateITE σ x x) (free_var_set phi \ {x}) :=
          by
            simp only [Finset.sdiff_singleton_eq_erase] at *
            exact Finset.erase_eq_of_not_mem s3
    case _ c1 =>
      simp at c1

      have s1 : Finset.image (Function.updateITE σ x x) (free_var_set phi) \ {x} = Finset.image (Function.updateITE σ x x) (free_var_set phi \ {x}) \ {x} :=
      by
        apply Finset.image_sdiff_singleton
        simp only [Function.updateITE]
        simp
      simp only [s1]

      have s2 : x ∉ Finset.image (Function.updateITE σ x x) (free_var_set phi \ {x}) :=
      by
        simp only [Finset.mem_image]
        simp
        simp only [Function.updateITE]
        simp
        tauto

      simp only [Finset.sdiff_singleton_eq_erase] at *
      exact Finset.erase_eq_of_not_mem s2


theorem substitution_theorem_sub_var_all_rec
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (σ : VarName_ → VarName_)
  (c : Char)
  (F : Formula_) :
  holds D I V E (sub_var_all_rec σ c F) ↔
    holds D I (V ∘ σ) E F :=
  by
  induction F generalizing σ V
  case pred_const_ X xs | pred_var_ X xs | eq_ x y =>
    simp only [sub_var_all_rec]
    simp only [holds]
    simp
  case true_ | false_ =>
    simp only [sub_var_all_rec]
    simp only [holds]
  case not_ phi phi_ih =>
    simp only [sub_var_all_rec]
    simp only [holds]
    congr! 1
    apply phi_ih
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [sub_var_all_rec]
    simp only [holds]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [sub_var_all_rec]
    simp only [holds]

    first | apply forall_congr' | apply exists_congr
    intro d

    simp only [phi_ih]
    apply holds_coincide_var
    intro v a1

    simp
    split_ifs
    case _ c1 =>
      obtain s0 := fresh_not_mem x c (free_var_set (sub_var_all_rec (Function.updateITE σ x x) c phi))

      generalize (fresh x c (free_var_set (sub_var_all_rec (Function.updateITE σ x x) c phi))) = x' at *
      by_cases c2 : v = x
      · simp only [c2]
        simp only [Function.updateITE]
        simp
      · by_cases c3 : σ v = x'
        · subst c3

          simp only [sub_var_all_rec_free_var_set_eq_free_var_set_image] at s0

          have s1 : σ v ∈ Finset.image (Function.updateITE σ x x) (free_var_set phi) :=
          by
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
      · have s1 : ¬ σ v = x :=
        by
          intro contra
          apply c1
          apply Exists.intro v
          constructor
          · simp
            simp only [← var_is_free_in_iff_mem_free_var_set]
            tauto
          · exact contra

        simp only [Function.updateITE]
        simp only [if_neg c2]
        simp only [if_neg s1]
        simp
  case def_ X xs =>
    induction E
    case nil =>
      simp only [sub_var_all_rec]
      simp only [holds]
    case cons E_hd E_tl E_ih =>
      simp only [sub_var_all_rec] at E_ih

      simp only [sub_var_all_rec]
      simp only [holds]
      simp
      split_ifs
      case pos c1 =>
        apply holds_coincide_var
        intro v a1
        apply Function.updateListITE_map_mem_ext
        · simp
        · obtain ⟨c1_left, c1_right⟩ := c1
          symm
          exact c1_right
        · simp only [var_is_free_in_iff_mem_free_var_set] at a1
          simp only [← List.mem_toFinset]
          apply Finset.mem_of_subset E_hd.h1 a1
      case neg c1 =>
        exact E_ih


theorem substitution_is_valid_sub_var_all_rec
  (σ : VarName_ → VarName_)
  (c : Char)
  (F : Formula_)
  (h1 : is_valid F) :
  is_valid (sub_var_all_rec σ c F) :=
  by
  simp only [is_valid] at h1

  simp only [is_valid]
  intro D I V E
  simp only [substitution_theorem_sub_var_all_rec]
  apply h1

-------------------------------------------------------------------------------

lemma sub_var_all_rec_id
  (c : Char)
  (F : Formula_) :
  sub_var_all_rec id c F = F :=
  by
  induction F
  case pred_const_ X xs | pred_var_ X xs | eq_ x y | def_ X xs =>
    simp only [sub_var_all_rec]
    simp
  case true_ | false_ =>
    simp only [sub_var_all_rec]
  case not_ phi phi_ih =>
    simp only [sub_var_all_rec]
    congr!
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [sub_var_all_rec]
    congr!
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [sub_var_all_rec]
    simp
    simp only [Function.updateITE_id]
    exact phi_ih


example
  (σ : VarName_ → VarName_)
  (c : Char)
  (F : Formula_)
  (h1 : FOL.NV.Sub.Var.All.Rec.admits_var_all_rec σ F) :
  sub_var_all_rec σ c F = FOL.NV.Sub.Var.All.Rec.fast_replace_free_var_all_rec σ F :=
  by
  induction F generalizing σ
  case
      pred_const_ X xs
    | pred_var_ X xs
    | eq_ x y
    | true_
    | false_
    | def_ X xs =>
    simp only [sub_var_all_rec]
    simp only [fast_replace_free_var_all_rec]
  case not_ phi ih =>
    simp only [admits_var_all_rec] at ih

    simp only [admits_var_all_rec] at h1
    simp only [admits_var_all_rec_aux] at h1

    simp only [sub_var_all_rec]
    simp only [fast_replace_free_var_all_rec]
    congr
    apply ih
    exact h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [admits_var_all_rec] at phi_ih
    simp only [admits_var_all_rec] at psi_ih

    simp only [admits_var_all_rec] at h1
    simp only [admits_var_all_rec_aux] at h1

    simp only [sub_var_all_rec]
    simp only [fast_replace_free_var_all_rec]
    congr
    · tauto
    · tauto
  case
      forall_ x phi ih
    | exists_ x phi ih =>
    simp only [admits_var_all_rec] at ih

    simp only [admits_var_all_rec] at h1
    simp only [admits_var_all_rec_aux] at h1
    simp at h1

    simp only [sub_var_all_rec]
    simp only [fast_replace_free_var_all_rec]

    have s1 : ¬ ∃ y ∈ phi.free_var_set \ {x}, σ y = x :=
    by
      simp
      intro v a1 a2 a3
      apply admits_var_all_rec_aux_mem_free_var_set_and_not_mem_binders {x} σ phi h1 v a1
      · simp
        exact a2
      · simp
        exact a3
    simp only [if_neg s1]
    clear s1

    congr
    apply ih
    clear ih
    apply admits_var_all_rec_aux_del_binder
    simp
    exact h1


#lint
