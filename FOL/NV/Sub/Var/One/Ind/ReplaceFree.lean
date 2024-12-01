import FOL.NV.Sub.Var.One.Rec.ReplaceFree


set_option autoImplicit false


namespace FOL.NV.Sub.Var.One.Ind

open Formula_


/--
  `is_replace_free_var_one_ind F v t F'` := True if and only if `F'` is the result of replacing in `F` each free occurrence of `v` by an occurrence of `t`.
-/
inductive is_replace_free_var_one_ind : Formula_ → VarName_ → VarName_ → Formula_ → Prop

  | pred_const_
    (X : PredName_)
    (xs : List VarName_)
    (v t : VarName_) :
    is_replace_free_var_one_ind (pred_const_ X xs) v t (pred_const_ X (xs.map fun (x : VarName_) =>
      if v = x then t else x))

  | pred_var_
    (X : PredName_)
    (xs : List VarName_)
    (v t : VarName_) :
    is_replace_free_var_one_ind (pred_var_ X xs) v t (pred_var_ X (xs.map fun (x : VarName_) =>
      if v = x then t else x))

  | eq_
    (x y : VarName_)
    (v t : VarName_) :
    is_replace_free_var_one_ind (eq_ x y) v t (eq_ (if v = x then t else x) (if v = y then t else y))

  | true_
    (v t : VarName_) :
    is_replace_free_var_one_ind true_ v t true_

  | false_
    (v t : VarName_) :
    is_replace_free_var_one_ind false_ v t false_

  | not_
    (phi : Formula_)
    (v t : VarName_)
    (phi' : Formula_) :
    is_replace_free_var_one_ind phi v t phi' →
    is_replace_free_var_one_ind phi.not_ v t phi'.not_

  | imp_
    (phi psi : Formula_)
    (v t : VarName_)
    (phi' psi' : Formula_) :
    is_replace_free_var_one_ind phi v t phi' →
    is_replace_free_var_one_ind psi v t psi' →
    is_replace_free_var_one_ind (phi.imp_ psi) v t (phi'.imp_ psi')

  | and_
    (phi psi : Formula_)
    (v t : VarName_)
    (phi' psi' : Formula_) :
    is_replace_free_var_one_ind phi v t phi' →
    is_replace_free_var_one_ind psi v t psi' →
    is_replace_free_var_one_ind (phi.and_ psi) v t (phi'.and_ psi')

  | or_
    (phi psi : Formula_)
    (v t : VarName_)
    (phi' psi' : Formula_) :
    is_replace_free_var_one_ind phi v t phi' →
    is_replace_free_var_one_ind psi v t psi' →
    is_replace_free_var_one_ind (phi.or_ psi) v t (phi'.or_ psi')

  | iff_
    (phi psi : Formula_)
    (v t : VarName_)
    (phi' psi' : Formula_) :
    is_replace_free_var_one_ind phi v t phi' →
    is_replace_free_var_one_ind psi v t psi' →
    is_replace_free_var_one_ind (phi.iff_ psi) v t (phi'.iff_ psi')

  | forall_not_free_in
    (x : VarName_)
    (phi : Formula_)
    (v t : VarName_) :
    v = x →
    is_replace_free_var_one_ind (forall_ x phi) v t (forall_ x phi)

  | forall_free_in
    (x : VarName_)
    (phi : Formula_)
    (v t : VarName_)
    (phi' : Formula_) :
    ¬ v = x →
    is_replace_free_var_one_ind phi v t phi' →
    is_replace_free_var_one_ind (forall_ x phi) v t (forall_ x phi')

  | exists_not_free_in
    (x : VarName_)
    (phi : Formula_)
    (v t : VarName_) :
    v = x →
    is_replace_free_var_one_ind (exists_ x phi) v t (exists_ x phi)

  | exists_free_in
    (x : VarName_)
    (phi : Formula_)
    (v t : VarName_)
    (phi' : Formula_) :
    ¬ v = x →
    is_replace_free_var_one_ind phi v t phi' →
    is_replace_free_var_one_ind (exists_ x phi) v t (exists_ x phi')

  | def_
    (X : DefName_)
    (xs : List VarName_)
    (v t : VarName_) :
    is_replace_free_var_one_ind (def_ X xs) v t (def_ X (xs.map fun (x : VarName_) =>
      if v = x then t else x))


example
  (F F' : Formula_)
  (v t : VarName_)
  (h1 : is_replace_free_var_one_ind F v t F') :
  Rec.fast_replace_free_var_one_rec v t F = F' :=
  by
  induction h1
  all_goals
    simp only [Rec.fast_replace_free_var_one_rec]
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
  (F F' : Formula_)
  (v t : VarName_)
  (h1 : Rec.fast_replace_free_var_one_rec v t F = F') :
  is_replace_free_var_one_ind F v t F' :=
  by
  subst h1
  induction F
  all_goals
    simp only [Rec.fast_replace_free_var_one_rec]
  case
      pred_const_ X xs
    | pred_var_ X xs
    | eq_ x y
    | true_
    | false_
    | def_ X xs =>
    first
    | apply is_replace_free_var_one_ind.pred_const_
    | apply is_replace_free_var_one_ind.pred_var_
    | apply is_replace_free_var_one_ind.eq_
    | apply is_replace_free_var_one_ind.true_
    | apply is_replace_free_var_one_ind.false_
    | apply is_replace_free_var_one_ind.def_
  case not_ phi phi_ih =>
    apply is_replace_free_var_one_ind.not_
    exact phi_ih
  case
    imp_ phi psi phi_ih psi_ih
  | and_ phi psi phi_ih psi_ih
  | or_ phi psi phi_ih psi_ih
  | iff_ phi psi phi_ih psi_ih =>
    first
    | apply is_replace_free_var_one_ind.imp_
    | apply is_replace_free_var_one_ind.and_
    | apply is_replace_free_var_one_ind.or_
    | apply is_replace_free_var_one_ind.iff_
    · exact phi_ih
    · exact psi_ih
  case forall_ x phi phi_ih =>
    split_ifs
    case _ c1 =>
      apply is_replace_free_var_one_ind.forall_not_free_in
      exact c1
    case _ c1 =>
      apply is_replace_free_var_one_ind.forall_free_in
      · exact c1
      · exact phi_ih
  case exists_ x phi phi_ih =>
    split_ifs
    case _ c1 =>
      apply is_replace_free_var_one_ind.exists_not_free_in
      exact c1
    case _ c1 =>
      apply is_replace_free_var_one_ind.exists_free_in
      · exact c1
      · exact phi_ih


#lint
