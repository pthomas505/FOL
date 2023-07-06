import FOL.Sub.All.Rec.SubAllRecAdmits


namespace FOL

open Formula

/--
  The inductive simultaneous uniform substitution of a single predicate variable in a formula.

  IsPredSub A P zs H B := The formula A is said to be transformed into the formula B by a substitution of H* for P z₁ ... zₙ, abbreviated: Sub A (P zⁿ / H*) B, iff B is obtained from A upon replacing in A each occurrence of a derivative of the name form P z₁ ... zₙ by the corresponding derivative of the substituend H*, provided that: (i) P does not occur in a component formula (∀ x A₁) of A if x is a parameter of H*, and (ii) the name variable zₖ, k = 1, ..., n, is not free in a component formula (∀ x H) of H* if P t₁ ... tₙ occurs in A with x occurring in tₖ. If conditions (i) and (ii) are not satisfied, then the indicated substitution for predicate variables is left undefined.
-/
inductive IsPredSub
  (P : PredName)
  (zs : List VarName)
  (H : Formula) :
  Formula → Formula → Prop

  | pred_const_
    (X : PredName)
    (xs : List VarName) :
    IsPredSub P zs H (pred_const_ X xs) (pred_const_ X xs)

/-
  If A is an atomic formula not containing P then Sub A (P zⁿ / H*) A.
-/

  | pred_not_occurs_in
    (X : PredName)
    (xs : List VarName) :
    ¬ (X = P ∧ xs.length = zs.length) →
    IsPredSub P zs H (pred_var_ X xs) (pred_var_ X xs)

  /-
  If A = P t₁ ... tₙ and Sf H* (zⁿ / tⁿ) B, then Sub A (P zⁿ / H*) B.

  Sf H* (zⁿ / tⁿ) B :=
    admits_fun (function.update_list_ite id zs.to_list ts.to_list) H* ∧
    fast_replace_free_fun (function.update_list_ite id zs.to_list ts.to_list) H* = B
  -/

  | pred_occurs_in
    (X : PredName)
    (ts : List VarName) :
    X = P ∧ ts.length = zs.length →
    admitsFun (Function.updateListIte id zs ts) H →
    IsPredSub P zs H (pred_var_ P ts)
    (fastReplaceFreeFun (Function.updateListIte id zs ts) H)

  | eq_
    (x y : VarName) :
    IsPredSub P zs H (eq_ x y) (eq_ x y)

  | true_ : IsPredSub P zs H true_ true_

  | false_ : IsPredSub P zs H false_ false_

/-
  If A = (¬ A₁) and Sub A₁ (P zⁿ / H*) B₁, then Sub A (P zⁿ / H*) (¬ B₁).
-/
  | not_
    (phi : Formula)
    (phi' : Formula) :
    IsPredSub P zs H phi phi' →
    IsPredSub P zs H phi.not_ phi'.not_

/-
  If A = (A₁ → A₂), Sub A₁ (P zⁿ / H*) B₁, and Sub A₂ (P zⁿ / H*) B₂, then Sub A (P zⁿ / H*) (B₁ → B₁).
-/

  | imp_
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsPredSub P zs H phi phi' →
    IsPredSub P zs H psi psi' →
    IsPredSub P zs H (phi.imp_ psi) (phi'.imp_ psi')

  | and_
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsPredSub P zs H phi phi' →
    IsPredSub P zs H psi psi' →
    IsPredSub P zs H (phi.and_ psi) (phi'.and_ psi')

  | or_
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsPredSub P zs H phi phi' →
    IsPredSub P zs H psi psi' →
    IsPredSub P zs H (phi.or_ psi) (phi'.or_ psi')

  | iff_
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsPredSub P zs H phi phi' →
    IsPredSub P zs H psi psi' →
    IsPredSub P zs H (phi.iff_ psi) (phi'.iff_ psi')


/-
  If A = (∀ x A₁) and P does not occur in A then Sub A (P zⁿ / H*) A.

  If A = (∀ x A₁), P occurs in A, x is not free in H*, and Sub A₁ (P zⁿ / H*) B₁, then Sub A (P zⁿ / H*) (∀ x B₁).
-/

  | forall_
    (x : VarName)
    (phi : Formula)
    (phi' : Formula) :
    ¬ isFreeIn x H →
    IsPredSub P zs H phi phi' →
    IsPredSub P zs H (forall_ x phi) (forall_ x phi')

  | exists_
    (x : VarName)
    (phi : Formula)
    (phi' : Formula) :
    ¬ isFreeIn x H →
    IsPredSub P zs H phi phi' →
    IsPredSub P zs H (exists_ x phi) (exists_ x phi')


theorem isPredSub_theorem
  (D : Type)
  (I J : Interpretation D)
  (V : VarAssignment D)
  (A : Formula)
  (P : PredName)
  (zs : List VarName)
  (H : Formula)
  (B : Formula)
  (h1 : IsPredSub P zs H A B)
  (h2 : ∀ (Q : PredName) (ds : List D),
    Q = P ∧ ds.length = zs.length →
      (Holds D I (Function.updateListIte V zs ds) H ↔ J.pred_var_ P ds))
  (h3_const : I.pred_const_ = J.pred_const_)
  (h3_var : ∀ (Q : PredName) (ds : List D),
    ¬ (Q = P ∧ ds.length = zs.length) →
      (I.pred_var_ Q ds ↔ J.pred_var_ Q ds)) :
  Holds D I V B ↔ Holds D J V A :=
  by
  induction h1 generalizing V
  case pred_const_ h1_X h1_ts =>
    unfold Holds
    simp only [h3_const]
  case pred_not_occurs_in h1_X h1_ts h1_1 =>
    simp at h1_1
    apply Holds_coincide_PredVar
    · exact h3_const
    · intro X ds a1
      simp at a1
      cases a1
      case intro a1_left a1_right =>
        subst a1_left
        apply h3_var
        simp
        intro a2
        subst a2
        simp at h1_1
        intro contra
        apply h1_1
        exact Eq.trans a1_right contra
  case pred_occurs_in h1_X h1_ts h1_1 h1_2 =>
    obtain s1 := substitution_fun_theorem D I V (Function.updateListIte id zs h1_ts) H h1_2

    obtain s2 := Function.updateListIte_comp id V zs h1_ts

    simp only [s2] at s1
    simp at s1

    specialize h2 h1_X (List.map V h1_ts)
    simp only [s1] at h2

    simp only [Holds]
    apply h2
    simp
    exact h1_1
  case eq_ h1_x h1_y =>
    unfold Holds
    rfl
  case true_ | false_ =>
    unfold Holds
    rfl
  case not_ h1_phi h1_phi' _ h1_ih =>
    unfold Holds
    congr! 1
    exact h1_ih V h2
  case
    imp_ h1_phi h1_psi h1_phi' h1_psi' _ _ h1_ih_1 h1_ih_2
  | and_ h1_phi h1_psi h1_phi' h1_psi' _ _ h1_ih_1 h1_ih_2
  | or_ h1_phi h1_psi h1_phi' h1_psi' _ _ h1_ih_1 h1_ih_2
  | iff_ h1_phi h1_psi h1_phi' h1_psi' _ _ h1_ih_1 h1_ih_2 =>
    unfold Holds
    congr! 1
    · exact h1_ih_1 V h2
    · exact h1_ih_2 V h2
  case
    forall_ h1_x h1_phi h1_phi' h1_1 _ h1_ih
  | exists_ h1_x h1_phi h1_phi' h1_1 _ h1_ih =>
    unfold Holds
    first | apply forall_congr' | apply exists_congr
    intro d
    apply h1_ih
    intro Q ds a1
    specialize h2 Q ds a1
    have s1 :
      Holds D I (Function.updateListIte (Function.updateIte V h1_x d) zs ds) H ↔
        Holds D I (Function.updateListIte V zs ds) H :=
      by
      apply Holds_coincide_Var
      intro v a1
      apply Function.updateListIte_updateIte
      intro contra
      subst contra
      contradiction
    simp only [h2] at s1
    exact s1


theorem isPredSub_valid
  (phi phi' : Formula)
  (P : PredName)
  (zs : List VarName)
  (H : Formula)
  (h1 : IsPredSub P zs H phi phi')
  (h2 : phi.IsValid) : phi'.IsValid :=
  by
  unfold IsValid at h2

  unfold IsValid
  intro D I V
  let J : Interpretation D :=
    { nonempty := I.nonempty
      pred_const_ := I.pred_const_
      pred_var_ := fun (Q : PredName) (ds : List D) =>
        if (Q = P ∧ ds.length = zs.length)
        then Holds D I (Function.updateListIte V zs ds) H
        else I.pred_var_ Q ds }
  obtain s1 := isPredSub_theorem D I J V phi P zs H phi' h1
  simp only [Interpretation.pred_var_] at s1
  have s2 : Holds D I V phi' ↔ Holds D J V phi :=
    by
    apply s1
    · intro Q ds a1
      cases a1
      case h2.intro a1_left a1_right =>
      simp
      simp only [if_pos a1_right]
    · simp
    · intro Q ds a1
      simp only [if_neg a1]
  simp only [s2]
  apply h2


#lint

end FOL
