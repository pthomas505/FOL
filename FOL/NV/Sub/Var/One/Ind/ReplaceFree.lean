import FOL.NV.Sub.Var.One.Rec.ReplaceFree


set_option autoImplicit false


namespace FOL.NV.Sub.Var.One.Ind

open Formula


/--
  IsReplaceFree F v t F' := True if and only if F' is the result of replacing in F each free occurrence of v by an occurrence of t.
-/
inductive IsReplaceFree : Formula → VarName_ → VarName_ → Formula → Prop

  | pred_const_
    (X : PredName_)
    (xs : List VarName_)
    (v t : VarName_) :
    IsReplaceFree (pred_const_ X xs) v t (pred_const_ X (xs.map fun (x : VarName_) =>
      if v = x then t else x))

  | pred_var_
    (X : PredName_)
    (xs : List VarName_)
    (v t : VarName_) :
    IsReplaceFree (pred_var_ X xs) v t (pred_var_ X (xs.map fun (x : VarName_) =>
      if v = x then t else x))

  | eq_
    (x y : VarName_)
    (v t : VarName_) :
    IsReplaceFree (eq_ x y) v t (eq_ (if v = x then t else x) (if v = y then t else y))

  | true_
    (v t : VarName_) :
    IsReplaceFree true_ v t true_

  | false_
    (v t : VarName_) :
    IsReplaceFree false_ v t false_

  | not_
    (phi : Formula)
    (v t : VarName_)
    (phi' : Formula) :
    IsReplaceFree phi v t phi' →
    IsReplaceFree phi.not_ v t phi'.not_

  | imp_
    (phi psi : Formula)
    (v t : VarName_)
    (phi' psi' : Formula) :
    IsReplaceFree phi v t phi' →
    IsReplaceFree psi v t psi' →
    IsReplaceFree (phi.imp_ psi) v t (phi'.imp_ psi')

  | and_
    (phi psi : Formula)
    (v t : VarName_)
    (phi' psi' : Formula) :
    IsReplaceFree phi v t phi' →
    IsReplaceFree psi v t psi' →
    IsReplaceFree (phi.and_ psi) v t (phi'.and_ psi')

  | or_
    (phi psi : Formula)
    (v t : VarName_)
    (phi' psi' : Formula) :
    IsReplaceFree phi v t phi' →
    IsReplaceFree psi v t psi' →
    IsReplaceFree (phi.or_ psi) v t (phi'.or_ psi')

  | iff_
    (phi psi : Formula)
    (v t : VarName_)
    (phi' psi' : Formula) :
    IsReplaceFree phi v t phi' →
    IsReplaceFree psi v t psi' →
    IsReplaceFree (phi.iff_ psi) v t (phi'.iff_ psi')

  | forall_not_free_in
    (x : VarName_)
    (phi : Formula)
    (v t : VarName_) :
    v = x →
    IsReplaceFree (forall_ x phi) v t (forall_ x phi)

  | forall_free_in
    (x : VarName_)
    (phi : Formula)
    (v t : VarName_)
    (phi' : Formula) :
    ¬ v = x →
    IsReplaceFree phi v t phi' →
    IsReplaceFree (forall_ x phi) v t (forall_ x phi')

  | exists_not_free_in
    (x : VarName_)
    (phi : Formula)
    (v t : VarName_) :
    v = x →
    IsReplaceFree (exists_ x phi) v t (exists_ x phi)

  | exists_free_in
    (x : VarName_)
    (phi : Formula)
    (v t : VarName_)
    (phi' : Formula) :
    ¬ v = x →
    IsReplaceFree phi v t phi' →
    IsReplaceFree (exists_ x phi) v t (exists_ x phi')

  | def_
    (X : DefName_)
    (xs : List VarName_)
    (v t : VarName_) :
    IsReplaceFree (def_ X xs) v t (def_ X (xs.map fun (x : VarName_) =>
      if v = x then t else x))


example
  (F F' : Formula)
  (v t : VarName_)
  (h1 : IsReplaceFree F v t F') :
  Rec.fastReplaceFree v t F = F' :=
  by
  induction h1
  all_goals
    simp only [Rec.fastReplaceFree]
  case not_ phi v' t' phi' ih_1 ih_2 =>
    simp
    exact ih_2
  case
    imp_ phi psi v' t' phi' psi' phi_ih_1 psi_ih_1 phi_ih_2 psi_ih_2
  | and_ phi psi v' t' phi' psi' phi_ih_1 psi_ih_1 phi_ih_2 psi_ih_2
  | or_ phi psi v' t' phi' psi' phi_ih_1 psi_ih_1 phi_ih_2 psi_ih_2
  | iff_ phi psi v' t' phi' psi' phi_ih_1 psi_ih_1 phi_ih_2 psi_ih_2 =>
    simp
    tauto
  case
    forall_not_free_in x phi v' t' ih
  | exists_not_free_in x phi v' t' ih =>
    simp
    intro a1
    contradiction
  case
    forall_free_in x phi v' t' phi' ih_1 ih_2 ih_3
  | exists_free_in x phi v' t' phi' ih_1 ih_2 ih_3 =>
    simp only [if_neg ih_1]
    simp
    exact ih_3


example
  (F F' : Formula)
  (v t : VarName_)
  (h1 : Rec.fastReplaceFree v t F = F') :
  IsReplaceFree F v t F' :=
  by
  subst h1
  induction F
  all_goals
    simp only [Rec.fastReplaceFree]
  case
      pred_const_ X xs
    | pred_var_ X xs
    | eq_ x y
    | true_
    | false_
    | def_ X xs =>
    first
    | apply IsReplaceFree.pred_const_
    | apply IsReplaceFree.pred_var_
    | apply IsReplaceFree.eq_
    | apply IsReplaceFree.true_
    | apply IsReplaceFree.false_
    | apply IsReplaceFree.def_
  case not_ phi phi_ih =>
    apply IsReplaceFree.not_
    exact phi_ih
  case
    imp_ phi psi phi_ih psi_ih
  | and_ phi psi phi_ih psi_ih
  | or_ phi psi phi_ih psi_ih
  | iff_ phi psi phi_ih psi_ih =>
    first
    | apply IsReplaceFree.imp_
    | apply IsReplaceFree.and_
    | apply IsReplaceFree.or_
    | apply IsReplaceFree.iff_
    · exact phi_ih
    · exact psi_ih
  case forall_ x phi phi_ih =>
    split_ifs
    case _ c1 =>
      apply IsReplaceFree.forall_not_free_in
      exact c1
    case _ c1 =>
      apply IsReplaceFree.forall_free_in
      · exact c1
      · exact phi_ih
  case exists_ x phi phi_ih =>
    split_ifs
    case _ c1 =>
      apply IsReplaceFree.exists_not_free_in
      exact c1
    case _ c1 =>
      apply IsReplaceFree.exists_free_in
      · exact c1
      · exact phi_ih


#lint
