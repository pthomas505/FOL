import MathlibExtra.List
import FOL.NV.Binders


set_option autoImplicit false


namespace FOL.NV.Sub.Var.One.Rec

open Formula


/-
[margaris]
pg. 48

If $P$ is a formula, $v$ is a variable, and $t$ is a term, then $P(t/v)$ is the result of replacing each free occurrence of $v$ in $P$ by an occurrence of $t$.
-/

/--
  Helper function for replaceFree.
-/
def replaceFreeAux (v t : VarName) (binders : Finset VarName) : Formula → Formula
  | pred_const_ X xs =>
      pred_const_
      X
      (xs.map fun (x : VarName) => if v = x ∧ x ∉ binders then t else x)
  | pred_var_ X xs =>
      pred_var_
      X
      (xs.map fun (x : VarName) => if v = x ∧ x ∉ binders then t else x)
  | eq_ x y =>
      eq_
      (if v = x ∧ x ∉ binders then t else x)
      (if v = y ∧ y ∉ binders then t else y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replaceFreeAux v t binders phi)
  | imp_ phi psi =>
      imp_
      (replaceFreeAux v t binders phi)
      (replaceFreeAux v t binders psi)
  | and_ phi psi =>
      and_
      (replaceFreeAux v t binders phi)
      (replaceFreeAux v t binders psi)
  | or_ phi psi =>
      or_
      (replaceFreeAux v t binders phi)
      (replaceFreeAux v t binders psi)
  | iff_ phi psi =>
      iff_
      (replaceFreeAux v t binders phi)
      (replaceFreeAux v t binders psi)
  | forall_ x phi => forall_ x (replaceFreeAux v t (binders ∪ {x}) phi)
  | exists_ x phi => exists_ x (replaceFreeAux v t (binders ∪ {x}) phi)
  | def_ X xs =>
      def_
      X
      (xs.map fun (x : VarName) => if v = x ∧ x ∉ binders then t else x)

/--
  replaceFree v t P :=

  P(t/v)

  v → t in P for each free occurrence of v in P

  The result of replacing each free occurrence of v in P by an occurrence of t.
-/
def replaceFree (v t : VarName) (F : Formula) : Formula :=
  replaceFreeAux v t ∅ F


/--
  fastReplaceFree v t P :=

  P(t/v)

  v → t in P for each free occurrence of v in P

  The result of replacing each free occurrence of v in P by an occurrence of t.

  This is a more efficient version of replaceFree.
-/
def fastReplaceFree (v t : VarName) : Formula → Formula
  | pred_const_ X xs =>
      pred_const_
      X
      (xs.map fun (x : VarName) => if v = x then t else x)
  | pred_var_ X xs =>
      pred_var_
      X
      (xs.map fun (x : VarName) => if v = x then t else x)
  | eq_ x y =>
    eq_
    (if v = x then t else x)
    (if v = y then t else y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (fastReplaceFree v t phi)
  | imp_ phi psi => imp_ (fastReplaceFree v t phi) (fastReplaceFree v t psi)
  | and_ phi psi => and_ (fastReplaceFree v t phi) (fastReplaceFree v t psi)
  | or_ phi psi => or_ (fastReplaceFree v t phi) (fastReplaceFree v t psi)
  | iff_ phi psi => iff_ (fastReplaceFree v t phi) (fastReplaceFree v t psi)
  | forall_ x phi =>
      if v = x
      then forall_ x phi  -- v is not free in (forall_ x phi)
      else forall_ x (fastReplaceFree v t phi)
  | exists_ x phi =>
      if v = x
      then exists_ x phi  -- v is not free in (exists_ x phi)
      else exists_ x (fastReplaceFree v t phi)
  | def_ X xs =>
      def_
      X
      (xs.map fun (x : VarName) => if v = x then t else x)


-- replaceFree = fastReplaceFree

theorem replaceFreeAux_mem_binders
  (F : Formula)
  (v t : VarName)
  (binders : Finset VarName)
  (h1 : v ∈ binders) :
  replaceFreeAux v t binders F = F :=
  by
  induction F generalizing binders
  any_goals
    simp only [replaceFreeAux]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
    simp only [List.map_eq_self_iff]
    simp
    intro x _ a2 a3
    subst a2
    contradiction
  case eq_ x y =>
    simp
    constructor
    case left | right =>
      intro a1 a2
      subst a1
      contradiction
  case not_ phi phi_ih =>
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp
    apply phi_ih
    simp
    left
    exact h1


theorem replaceFreeAux_eq_fastReplaceFree
  (F : Formula)
  (v t : VarName)
  (binders : Finset VarName)
  (h1 : v ∉ binders) :
  replaceFreeAux v t binders F =
    fastReplaceFree v t F :=
  by
  induction F generalizing binders
  any_goals
    simp only [replaceFreeAux]
    simp only [fastReplaceFree]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    congr!
    case _ x =>
      constructor
      case mp =>
        tauto
      case mpr =>
        intro a1
        subst a1
        tauto
  case eq_ x y =>
    congr!
    case _ | _ =>
      constructor
      case mp =>
        tauto
      case mpr =>
        intro a1
        subst a1
        tauto
  case not_ phi phi_ih =>
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    split_ifs
    case pos c1 =>
      congr! 1
      apply replaceFreeAux_mem_binders
      simp
      right
      exact c1
    case neg c1 =>
      congr! 1
      apply phi_ih
      simp
      tauto


theorem replaceFree_eq_fastReplaceFree
  (F : Formula)
  (v t : VarName) :
  replaceFree v t F = fastReplaceFree v t F :=
  by
  simp only [replaceFree]
  apply replaceFreeAux_eq_fastReplaceFree
  simp

--

theorem fastReplaceFree_self
  (F : Formula)
  (v : VarName) :
  fastReplaceFree v v F = F :=
  by
  induction F
  any_goals
    simp only [fastReplaceFree]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
    simp only [List.map_eq_self_iff]
    simp
  case eq_ x y =>
    simp
  case not_ phi phi_ih =>
    congr!
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    congr!
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp
    intro _
    exact phi_ih


theorem not_free_in_fastReplaceFree_self
  (F : Formula)
  (v t : VarName)
  (h1 : ¬ var_is_free_in v F) :
  fastReplaceFree v t F = F :=
  by
  induction F
  any_goals
    simp only [var_is_free_in] at h1

    simp only [fastReplaceFree]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
    simp only [List.map_eq_self_iff]
    simp
    intro x a1 a2
    subst a2
    contradiction
  case eq_ x y =>
    simp
    tauto
  case not_ phi phi_ih =>
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp
    tauto


theorem fastReplaceFree_inverse
  (F : Formula)
  (v t : VarName)
  (h1 : ¬ occursIn t F) :
  fastReplaceFree t v (fastReplaceFree v t F) = F :=
  by
  induction F
  any_goals
    simp only [occursIn] at h1

    simp only [fastReplaceFree]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    congr!
    simp
    simp only [List.map_eq_self_iff]
    simp
    intro x a1
    by_cases c1 : v = x
    · simp only [if_pos c1]
      simp
      exact c1
    · simp only [if_neg c1]
      simp
      intro a2
      subst a2
      contradiction
  case eq_ x y =>
      congr!
      · split_ifs <;> tauto
      · split_ifs <;> tauto
  case not_ phi phi_ih =>
    congr!
    exact phi_ih h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
      congr! <;> tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    push_neg at h1

    cases h1
    case intro h1_left h1_right =>
      split_ifs
      case pos c1 =>
        simp only [fastReplaceFree]
        simp only [if_neg h1_left]
        congr!
        apply not_free_in_fastReplaceFree_self
        contrapose! h1_right
        exact isFreeIn_imp_occursIn t phi h1_right
      case neg c1 =>
        simp only [fastReplaceFree]
        simp only [if_neg h1_left]
        congr!
        exact phi_ih h1_right


theorem not_isFreeIn_fastReplaceFree
  (F : Formula)
  (v t : VarName)
  (h1 : ¬ v = t) :
  ¬ var_is_free_in v (fastReplaceFree v t F) :=
  by
  induction F
  any_goals
    simp only [fastReplaceFree]
    simp only [var_is_free_in]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
    intro x
    split_ifs <;> tauto
  case eq_ x y =>
    split_ifs <;> tauto
  case true_ | false_ =>
    simp
  case not_ phi phi_ih =>
    exact phi_ih
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [fastReplaceFree]
    split_ifs
    case pos c1 =>
      simp only [var_is_free_in]
      simp
      intro a1
      contradiction
    case neg c1 =>
      simp only [var_is_free_in]
      simp
      intro _
      exact phi_ih


#lint
