import FOL.Alpha
import FOL.Sub.One.Rec.SubOneRecAdmits
import FOL.Sub.All.Rec.SubAllRecReplaceAll
import FOL.PredSub.All.Rec.PredSubAllRec

import FOL.Tactics


namespace FOL

open Formula


/--
  A substitution mapping.
  A bijective function mapping variable names to variable names.
-/
def Instantiation : Type :=
  { σ : VarName → VarName // ∃ σ' : VarName → VarName, σ ∘ σ' = id ∧ σ' ∘ σ = id }

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
    (d : Definition)
    (σ : Instantiation) :
    d ∈ E →
    IsConv E (def_ d.name (d.args.map σ.1)) (replaceAllVar σ.1 d.q)


inductive IsDeduct : Env → List Formula → Formula → Prop
  | struct_1_
    (E : Env)
    (Δ : List Formula)
    (H F : Formula) :
    IsDeduct E Δ F →
    IsDeduct E (H :: Δ) F

  | struct_2_
    (E : Env)
    (Δ : List Formula)
    (H F : Formula) :
    IsDeduct E (H :: H :: Δ) F →
    IsDeduct E (H :: Δ) F

  | struct_3_
    (E : Env)
    (Δ_1 Δ_2 : List Formula)
    (H1 H2 F : Formula) :
    IsDeduct E (Δ_1 ++ [H1] ++ [H2] ++ Δ_2) F →
    IsDeduct E (Δ_1 ++ [H2] ++ [H1] ++ Δ_2) F

  | assume_
    (E : Env)
    (Δ : List Formula)
    (F : Formula) :
    IsDeduct E (F :: Δ) F

  -- ⊢ ⊤
  | prop_true_
    (E : Env)
    (Δ : List Formula) :
    IsDeduct E Δ true_

  -- ⊢ phi → (psi → phi)
  | prop_1_
    (E : Env)
    (Δ : List Formula)
    (phi psi : Formula) :
    IsDeduct E Δ (phi.imp_ (psi.imp_ phi))

  -- ⊢ (phi → (psi → chi)) → ((phi → psi) → (phi → chi))
  | prop_2_
    (E : Env)
    (Δ : List Formula)
    (phi psi chi : Formula) :
    IsDeduct E Δ
      ((phi.imp_ (psi.imp_ chi)).imp_
        ((phi.imp_ psi).imp_ (phi.imp_ chi)))

  -- ⊢ (¬ phi → ¬ psi) → (psi → phi)
  | prop_3_
    (E : Env)
    (Δ : List Formula)
    (phi psi : Formula) :
    IsDeduct E Δ
      (((not_ phi).imp_ (not_ psi)).imp_
        (psi.imp_ phi))

  -- ⊢ (∀ v (phi → psi)) → ((∀ v phi) → (∀ v psi))
  | pred_1_
    (E : Env)
    (Δ : List Formula)
    (v : VarName)
    (phi psi : Formula) :
    IsDeduct E Δ
      ((forall_ v (phi.imp_ psi)).imp_
        ((forall_ v phi).imp_
          (forall_ v psi)))

  /-
    Δ ⊢ (∀ v phi) → phi(t/v)
    provided phi admits t for v
  -/
  | pred_2_
    (E : Env)
    (Δ : List Formula)
    (v t : VarName)
    (phi phi' : Formula) :
    fastAdmits v t phi →
      fastReplaceFree v t phi = phi' →
        IsDeduct E Δ ((forall_ v phi).imp_ phi')

  /-
    Δ ⊢ phi → (∀ v phi)
    provided v is not free in phi
  -/
  | pred_3_
    (E : Env)
    (Δ : List Formula)
    (v : VarName)
    (phi : Formula) :
    ¬ isFreeIn v phi →
    IsDeduct E Δ (phi.imp_ (forall_ v phi))

  /-
    Δ ⊢ ∀ v (v = v)
  -/
  | eq_1_
    (E : Env)
    (Δ : List Formula)
    (v : VarName) :
    IsDeduct E Δ (eq_ v v)

  /-
    Δ ⊢ ((x_0 = y_0) ∧ ... ∧ (x_n = y_n) ∧ ⊤) →
          (pred_ name [x_0 ... x_n] → pred_ name [y_0 ... y_n])
  -/
  | eq_2_pred_const_
    (E : Env)
    (Δ : List Formula)
    (name : PredName)
    (n : ℕ)
    (xs ys : Fin n → VarName) :
    IsDeduct E Δ
    ((And_ (List.ofFn fun i : Fin n => eq_ (xs i) (ys i))).imp_
      ((pred_const_ name (List.ofFn xs)).imp_ (pred_const_ name (List.ofFn ys))))

  /-
    Δ ⊢ ((x_0 = y_0) ∧ ... ∧ (x_n = y_n) ∧ ⊤) →
          (pred_ name [x_0 ... x_n] → pred_ name [y_0 ... y_n])
  -/
  | eq_2_pred_var_
    (E : Env)
    (Δ : List Formula)
    (name : PredName)
    (n : ℕ)
    (xs ys : Fin n → VarName) :
    IsDeduct E Δ
    ((And_ (List.ofFn fun i : Fin n => eq_ (xs i) (ys i))).imp_
      ((pred_var_ name (List.ofFn xs)).imp_ (pred_var_ name (List.ofFn ys))))

  /-
    Δ ⊢ ((x_0 = y_0) ∧ (x_1 = y_1)) →
          ((eq_ x_0 x_1) → (eq_ y_0 y_1))
  -/
  | eq_2_eq_
    (E : Env)
    (Δ : List Formula)
    (x_0 x_1 y_0 y_1 : VarName) :
    IsDeduct E Δ
    ((and_ (eq_ x_0 y_0) (eq_ x_1 y_1)).imp_
      ((eq_ x_0 x_1).imp_ (eq_ y_0 y_1)))

  /-
    Δ ⊢ phi ⇒ Δ ⊢ ∀ v phi
    provided v is not free in any formula in Δ
  -/
  | gen_
    (E : Env)
    (Δ : List Formula)
    (v : VarName)
    (phi : Formula) :
    (∀ H : Formula, H ∈ Δ → ¬ isFreeIn v H) →
    IsDeduct E Δ phi →
    IsDeduct E Δ (forall_ v phi)

  /-
    Δ ⊢ phi → psi ⇒
    Δ ⊢ phi ⇒
    Δ ⊢ psi
  -/
  | mp_
    (E : Env)
    (Δ : List Formula)
    (phi psi : Formula) :
    IsDeduct E Δ (phi.imp_ psi) →
    IsDeduct E Δ phi →
    IsDeduct E Δ psi

  | def_false_
    (E : Env)
    (Δ : List Formula) :
    IsDeduct E Δ (false_.iff_ (not_ true_))

  | def_and_
    (E : Env)
    (Δ : List Formula)
    (phi psi : Formula) :
    IsDeduct E Δ ((phi.and_ psi).iff_ (not_ (phi.imp_ (not_ psi))))

  | def_or_
    (E : Env)
    (Δ : List Formula)
    (phi psi : Formula) :
    IsDeduct E Δ ((phi.or_ psi).iff_ ((not_ phi).imp_ psi))

  | def_iff_
    (E : Env)
    (Δ : List Formula)
    (phi psi : Formula) :
    IsDeduct E Δ (not_ (((phi.iff_ psi).imp_ (not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi))))).imp_ (not_ ((not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi)))).imp_ (phi.iff_ psi)))))

  | define_
    (E : Env)
    (Δ : List Formula)
    (phi : Formula)
    (d : Definition) :
    (∀ d' ∈ E, d.name = d'.name → d.args.length = d'.args.length → False) →
    d.q.all_def_in_env E →
    IsDeduct E Δ phi →
    IsDeduct (d :: E) Δ phi

  | conv_
    (E : Env)
    (Δ : List Formula)
    (phi phi' : Formula) :
    IsDeduct E Δ phi →
    IsConv E phi phi' →
    IsDeduct E Δ phi'

  | pred_sub_
    (E : Env)
    (Δ : List Formula)
    (phi : Formula)
    (τ : PredName → ℕ → List VarName × Formula) :
    IsDeduct E Δ phi →
    admitsPredFun τ phi →
    (∀ H : Formula, H ∈ Δ → admitsPredFun τ H) →
    IsDeduct E (Δ.map (replacePredFun τ)) (replacePredFun τ phi)

  | thm
    (Δ Δ' : List Formula)
    (phi : Formula)
    (σ : Instantiation) :
    (∀ H : Formula, H ∈ Δ → IsDeduct E Δ' (replaceAllVar σ.1 H)) →
    IsDeduct E Δ phi →
    IsDeduct E Δ' (replaceAllVar σ.1 phi)
