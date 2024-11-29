import FOL.NV.Binders


set_option autoImplicit false


open Formula_


/--
  The type of definitions.
-/
structure Definition : Type where
  /--
    The name.
  -/
  (name : DefName_)

  /--
    The arguments.
  -/
  (args : List VarName_)

  /--
    The formula.
  -/
  (q : Formula_)

  (nodup : args.Nodup)
  (h1 : q.free_var_set ⊆ args.toFinset)
  (h2 : q.pred_var_set = ∅)
deriving DecidableEq


/--
  The type of environments.
-/
def Env : Type := List Definition

instance : Membership Definition Env :=
  inferInstanceAs (Membership Definition (List Definition))

instance : HAppend Env Env Env :=
  inferInstanceAs (HAppend (List Definition) (List Definition) (List Definition))


/--
  `Formula_.all_def_in_env E F` := True if and only if every definition that occurs in the formula `F` is in the environment `E`.
-/
def Formula_.all_def_in_env (E : Env) : Formula_ → Prop
| pred_const_ _ _ => True
| pred_var_ _ _ => True
| eq_ _ _ => True
| true_ => True
| false_ => True
| not_ phi => phi.all_def_in_env E
| imp_ phi psi =>
    phi.all_def_in_env E ∧
    psi.all_def_in_env E
| and_ phi psi =>
    phi.all_def_in_env E ∧
    psi.all_def_in_env E
| or_ phi psi =>
    phi.all_def_in_env E ∧
    psi.all_def_in_env E
| iff_ phi psi =>
    phi.all_def_in_env E ∧
    psi.all_def_in_env E
| forall_ _ phi => phi.all_def_in_env E
| exists_ _ phi => phi.all_def_in_env E
| def_ X xs =>
  ∃ (d : Definition), d ∈ E ∧ X = d.name ∧ xs.length = d.args.length

instance (E : Env) (F : Formula_) : Decidable (F.all_def_in_env E) :=
  by
  induction F
  all_goals
    simp only [all_def_in_env]
    infer_instance


/--
  `Env.nodup_ E` := True if and only if every definition that occurs in the environment `E` has a unique combination of name and argument length.
-/
def Env.nodup_ : Env → Prop :=
  List.Pairwise (fun (d1 d2 : Definition) => d1.name = d2.name → d1.args.length = d2.args.length → False)

instance (E : Env) : Decidable (E.nodup_) :=
  by
  induction E
  all_goals
    simp only [Env.nodup_]
    infer_instance


/--
  `Env.well_formed E` := True if and only if
  1. Every definition that occurs in the environment `E` has a unique combination of name and argument length.
  2. Every definition that occurs in the formula of a definition `d` in the environment `d :: E' ⊆ E` occurs in the environment `E'`. This means there are no circular definitions.
-/
def Env.well_formed : Env → Prop
  | List.nil => True
  | d :: E =>
    (∀ (d' : Definition), d' ∈ E →
      d.name = d'.name → d.args.length = d'.args.length → False) ∧
        Formula_.all_def_in_env E d.q ∧ Env.well_formed E

instance (E : Env) : Decidable (E.well_formed) :=
  by
  induction E
  all_goals
    simp only [Env.well_formed]
    infer_instance


#lint
