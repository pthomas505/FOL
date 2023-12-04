import FOL.NV.Sub.One.Rec.Admits


set_option autoImplicit false


namespace FOL.NV.Sub.One.Ind

open Formula
open Rec


/--
  IsFreeSub F v t F' := True if and only if F' is the result of replacing in F each free occurrence of v by a free occurrence of t.
-/
inductive IsFreeSub : Formula → VarName → VarName → Formula → Prop

  | pred_const_
    (X : PredName)
    (xs : List VarName)
    (v t : VarName) :
    IsFreeSub (pred_const_ X xs) v t (pred_const_ X (xs.map fun (x : VarName) =>
      if v = x then t else x))

  | pred_var_
    (X : PredName)
    (xs : List VarName)
    (v t : VarName) :
    IsFreeSub (pred_var_ X xs) v t (pred_var_ X (xs.map fun (x : VarName) =>
      if v = x then t else x))

  | eq_
    (x y : VarName)
    (v t : VarName) :
    IsFreeSub (eq_ x y) v t (eq_ (if v = x then t else x) (if v = y then t else y))

  | true_
    (v t : VarName) :
    IsFreeSub true_ v t true_

  | false_
    (v t : VarName) :
    IsFreeSub false_ v t false_

  | not_
    (phi : Formula)
    (v t : VarName)
    (phi' : Formula) :
    IsFreeSub phi v t phi' →
    IsFreeSub phi.not_ v t phi'.not_

  | imp_
    (phi psi : Formula)
    (v t : VarName)
    (phi' psi' : Formula) :
    IsFreeSub phi v t phi' →
    IsFreeSub psi v t psi' →
    IsFreeSub (phi.imp_ psi) v t (phi'.imp_ psi')

  | and_
    (phi psi : Formula)
    (v t : VarName)
    (phi' psi' : Formula) :
    IsFreeSub phi v t phi' →
    IsFreeSub psi v t psi' →
    IsFreeSub (phi.and_ psi) v t (phi'.and_ psi')

  | or_
    (phi psi : Formula)
    (v t : VarName)
    (phi' psi' : Formula) :
    IsFreeSub phi v t phi' →
    IsFreeSub psi v t psi' →
    IsFreeSub (phi.or_ psi) v t (phi'.or_ psi')

  | iff_
    (phi psi : Formula)
    (v t : VarName)
    (phi' psi' : Formula) :
    IsFreeSub phi v t phi' →
    IsFreeSub psi v t psi' →
    IsFreeSub (phi.iff_ psi) v t (phi'.iff_ psi')

  | forall_not_free_in
    (x : VarName)
    (phi : Formula)
    (v t : VarName) :
    ¬ isFreeIn v (forall_ x phi) →
    IsFreeSub (forall_ x phi) v t (forall_ x phi)

  | forall_free_in
    (x : VarName)
    (phi : Formula)
    (v t : VarName)
    (phi' : Formula) :
    isFreeIn v (forall_ x phi) →
    ¬ x = t →
    IsFreeSub phi v t phi' →
    IsFreeSub (forall_ x phi) v t (forall_ x phi')

  | exists_not_free_in
    (x : VarName)
    (phi : Formula)
    (v t : VarName) :
    ¬ isFreeIn v (exists_ x phi) →
    IsFreeSub (exists_ x phi) v t (exists_ x phi)

  | exists_free_in
    (x : VarName)
    (phi : Formula)
    (v t : VarName)
    (phi' : Formula) :
    isFreeIn v (exists_ x phi) →
    ¬ x = t →
    IsFreeSub phi v t phi' →
    IsFreeSub (exists_ x phi) v t (exists_ x phi')

  | def_
    (X : DefName)
    (xs : List VarName)
    (v t : VarName) :
    IsFreeSub (def_ X xs) v t (def_ X (xs.map fun (x : VarName) =>
      if v = x then t else x))


theorem fastAdmitsAux_and_fastReplaceFree_imp_isFreeSub
  (F F' : Formula)
  (v u : VarName)
  (binders : Finset VarName)
  (h1 : fastAdmitsAux v u binders F)
  (h2 : fastReplaceFree v u F = F') :
  IsFreeSub F v u F' :=
  by
  subst h2
  induction F generalizing binders
  all_goals
    simp only [fastAdmitsAux] at h1

    simp only [fastReplaceFree]
  case pred_const_ X xs | pred_var_ X xs =>
    first | apply IsFreeSub.pred_const_ | apply IsFreeSub.pred_var_
  case eq_ x y =>
    apply IsFreeSub.eq_
  case true_ | false_ =>
    first | apply IsFreeSub.true_ | apply IsFreeSub.false_
  case not_ phi phi_ih =>
    apply IsFreeSub.not_
    exact phi_ih binders h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    cases h1
    case intro h1_left h1_right =>
    first | apply IsFreeSub.imp_ | apply IsFreeSub.and_ | apply IsFreeSub.or_ | apply IsFreeSub.iff_
    · exact phi_ih binders h1_left
    · exact psi_ih binders h1_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    cases h1
    case inl h1 =>
      split_ifs
      case pos c1 | neg c1 =>
        first | apply IsFreeSub.forall_not_free_in | apply IsFreeSub.exists_not_free_in
        subst h1
        simp only [isFreeIn]
        simp
    case inr h1 =>
      split_ifs
      case pos c1 =>
        first | apply IsFreeSub.forall_not_free_in | apply IsFreeSub.exists_not_free_in
        simp only [isFreeIn]
        tauto
      case neg c1 =>
        by_cases c2 : isFreeIn v phi
        · first | apply IsFreeSub.forall_free_in | apply IsFreeSub.exists_free_in
          simp only [isFreeIn]
          constructor
          · exact c1
          . exact c2
          . have s1 : ¬ u ∈ binders ∪ {x}
            exact fastAdmitsAux_isFreeIn phi v u (binders ∪ {x}) h1 c2

            simp at s1
            tauto
          · exact phi_ih (binders ∪ {x}) h1
        · have s1 : fastReplaceFree v u phi = phi
          exact not_free_in_fastReplaceFree_self phi v u c2

          simp only [s1]
          first | apply IsFreeSub.forall_not_free_in | apply IsFreeSub.exists_not_free_in
          simp only [isFreeIn]
          tauto
  case def_ X xs =>
    apply IsFreeSub.def_


theorem isFreeSub_imp_fastAdmitsAux
  (F : Formula)
  (v u : VarName)
  (binders : Finset VarName)
  (h1 : ∃ (F' : Formula), IsFreeSub F v u F')
  (h2 : u ∉ binders) :
  fastAdmitsAux v u binders F :=
  by
  apply Exists.elim h1
  intro F' h1_1
  clear h1
  induction h1_1 generalizing binders
  all_goals
    simp only [fastAdmitsAux]
  case
      forall_not_free_in h1_1_x h1_1_phi h1_1_v h1_1_t h1_1_1
    | exists_not_free_in h1_1_x h1_1_phi h1_1_v h1_1_t h1_1_1 =>
    simp only [isFreeIn] at h1_1_1
    simp at h1_1_1

    by_cases c1 : h1_1_v = h1_1_x
    · left
      exact c1
    · right
      apply not_isFreeIn_imp_fastAdmitsAux
      exact h1_1_1 c1
  case
      forall_free_in h1_1_x h1_1_phi h1_1_v h1_1_t _ _ h1_1_2 _ h1_1_ih
    | exists_free_in h1_1_x h1_1_phi h1_1_v h1_1_t _ _ h1_1_2 _ h1_1_ih =>
    right
    apply h1_1_ih
    simp
    tauto
  all_goals
    tauto


theorem isFreeSub_imp_fastReplaceFree
  (F F' : Formula)
  (v u : VarName)
  (h1 : IsFreeSub F v u F') :
  fastReplaceFree v u F = F' :=
  by
  induction h1
  case pred_const_ h1_X h1_xs h1_v h1_t | pred_var_ h1_X h1_xs h1_v h1_t =>
    simp only [fastReplaceFree]
  case eq_ h1_x h1_y h1_v h1_t =>
    simp only [fastReplaceFree]
  case true_ h1_v h1_t | false_ h1_v h1_t =>
    rfl
  case not_ h1_phi h1_v h1_t h1_phi' h1_1 h1_ih =>
    simp only [fastReplaceFree]
    subst h1_ih
    rfl
  case
    imp_ h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' h1_1 h1_2 h1_ih_1 h1_ih_2
  | and_ h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' h1_1 h1_2 h1_ih_1 h1_ih_2
  | or_ h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' h1_1 h1_2 h1_ih_1 h1_ih_2
  | iff_ h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' h1_1 h1_2 h1_ih_1 h1_ih_2 =>
    simp only [fastReplaceFree]
    subst h1_ih_1
    subst h1_ih_2
    rfl
  case
    forall_not_free_in h1_x h1_phi h1_v h1_t h1_1
  | exists_not_free_in h1_x h1_phi h1_v h1_t h1_1 =>
    simp only [isFreeIn] at h1_1
    simp at h1_1

    simp only [fastReplaceFree]
    split_ifs
    case pos c1 =>
      rfl
    case neg c1 =>
      congr!
      apply not_free_in_fastReplaceFree_self
      exact h1_1 c1
  case
    forall_free_in h1_x h1_phi h1_v h1_t h1_phi' h1_1 _ _ h1_ih
  | exists_free_in h1_x h1_phi h1_v h1_t h1_phi' h1_1 _ _ h1_ih =>
    simp only [isFreeIn] at h1_1

    cases h1_1
    case intro h1_1_left h1_1_right =>
      simp only [fastReplaceFree]
      simp only [if_neg h1_1_left]
      subst h1_ih
      rfl
  case def_ h1_X h1_xs h1_v h1_t =>
    simp only [fastReplaceFree]


example
  (F F' : Formula)
  (v u : VarName) :
  IsFreeSub F v u F' ↔
    fastAdmits v u F ∧ fastReplaceFree v u F = F' :=
  by
  simp only [fastAdmits]
  constructor
  · intro a1
    constructor
    · apply isFreeSub_imp_fastAdmitsAux
      · exact Exists.intro F' a1
      · simp
    · exact isFreeSub_imp_fastReplaceFree F F' v u a1
  · intro a1
    cases a1
    case intro a1_left a1_right =>
      exact fastAdmitsAux_and_fastReplaceFree_imp_isFreeSub F F' v u ∅ a1_left a1_right


theorem substitution_theorem_ind
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (E : Env)
  (v t : VarName)
  (F F' : Formula)
  (h1 : IsFreeSub F v t F') :
  Holds D I (Function.updateITE V v (V t)) E F ↔
    Holds D I V E F' :=
  by
  induction h1 generalizing V
  case pred_const_ h1_X h1_xs h1_v h1_t | pred_var_ h1_X h1_xs h1_v h1_t =>
    simp only [Holds]
    congr! 1
    simp
    simp only [List.map_eq_map_iff]
    intro x _
    simp only [Function.updateITE]
    simp only [eq_comm]
    split_ifs
    case _ c1 =>
      simp
      simp only [if_pos c1]
    case _ c1 =>
      simp
      simp only [if_neg c1]
  case eq_ h1_x h1_y h1_v h1_t =>
    simp only [Holds]
    simp only [Function.updateITE]
    simp only [eq_comm]
    congr! 1 <;> { split_ifs <;> rfl }
  case true_ _ _ | false_ _ _ =>
    simp only [Holds]
  case not_ h1_phi h1_v h1_t h1_phi' _ h1_ih =>
    simp only [Holds]
    congr! 1
    apply h1_ih
  case
    imp_ h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' _ _ h1_ih_1 h1_ih_2
  | and_ h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' _ _ h1_ih_1 h1_ih_2
  | or_ h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' _ _ h1_ih_1 h1_ih_2
  | iff_ h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' _ _ h1_ih_1 h1_ih_2 =>
    simp only [Holds]
    congr! 1
    · apply h1_ih_1
    · apply h1_ih_2
  case
    forall_not_free_in h1_x h1_phi h1_v h1_t h1_1
  | exists_not_free_in h1_x h1_phi h1_v h1_t h1_1 =>
    simp only [isFreeIn] at h1_1
    simp at h1_1

    simp only [Holds]
    first | apply forall_congr' | apply exists_congr
    intro d
    apply Holds_coincide_Var
    intro x a1
    simp only [Function.updateITE]
    split_ifs
    case _ c1 =>
      rfl
    case _ c1 c2 =>
      subst c2
      specialize h1_1 c1
      contradiction
    case _ c1 c2 =>
      rfl
  case
    forall_free_in h1_x h1_phi h1_v h1_t h1_phi' h1_1 h1_2 _ h1_ih
  | exists_free_in h1_x h1_phi h1_v h1_t h1_phi' h1_1 h1_2 _ h1_ih =>
    simp only [isFreeIn] at h1_1

    simp only [Holds]
    first | apply forall_congr' | apply exists_congr
    intro d
    specialize h1_ih (Function.updateITE V h1_x d)
    simp only [← h1_ih]
    apply Holds_coincide_Var
    intro x _
    simp only [Function.updateITE]
    simp only [eq_comm]
    split_ifs
    case _ c1 c2 c3 =>
      subst c2
      cases h1_1
      case intro h1_1_left h1_1_right =>
        contradiction
    case _ | _ | _ =>
      rfl
  case def_ h1_X h1_xs h1_v h1_t =>
    induction E
    case nil =>
      simp only [Holds]
    case cons hd tl ih =>
      simp only [Holds]
      split_ifs
      case _ c1 c2 =>
        simp
        apply Holds_coincide_Var
        intro v' a1
        have s1 : List.map (Function.updateITE V h1_v (V h1_t)) h1_xs = List.map (V ∘ fun (x : VarName) => if h1_v = x then h1_t else x) h1_xs
        simp only [List.map_eq_map_iff]
        intro x _
        simp only [Function.updateITE]
        simp only [eq_comm]
        simp
        split_ifs
        case _ c3 =>
          simp only [if_pos c3]
        case _ c3 =>
          simp only [if_neg c3]

        simp only [s1]
        apply Function.updateListITE_mem_eq_len
        · simp only [isFreeIn_iff_mem_freeVarSet] at a1
          simp only [← List.mem_toFinset]
          apply Finset.mem_of_subset hd.h1 a1
        · cases c1
          case intro c1_left c1_right =>
            simp
            simp only [eq_comm]
            exact c1_right
      case _ c1 c2 =>
        simp only [List.length_map] at c2
        contradiction
      case _ c1 c2 =>
        simp at c2
        contradiction
      case _ c1 c2 =>
        exact ih


#lint
