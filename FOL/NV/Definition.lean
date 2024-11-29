import FOL.NV.Binders


set_option autoImplicit false


open Formula_


/--
  The type of definitions.
-/
structure Definition_ : Type where
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
def Env_ : Type := List Definition_

instance : Membership Definition_ Env_ :=
  inferInstanceAs (Membership Definition_ (List Definition_))

instance : HAppend Env_ Env_ Env_ :=
  inferInstanceAs (HAppend (List Definition_) (List Definition_) (List Definition_))


/--
  `Formula_.all_def_in_env E F` := True if and only if every definition that occurs in the formula `F` is in the environment `E`.
-/
def Formula_.all_def_in_env (E : Env_) : Formula_ → Prop
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
  ∃ (d : Definition_), d ∈ E ∧ X = d.name ∧ xs.length = d.args.length

instance (E : Env_) (F : Formula_) : Decidable (F.all_def_in_env E) :=
  by
  induction F
  all_goals
    simp only [all_def_in_env]
    infer_instance


/--
  `Env_.nodup_ E` := True if and only if every definition that occurs in the environment `E` has a unique combination of name and argument length.
-/
def Env_.nodup_ : Env_ → Prop :=
  List.Pairwise (fun (d1 d2 : Definition_) => d1.name = d2.name → d1.args.length = d2.args.length → False)

instance (E : Env_) : Decidable (E.nodup_) :=
  by
  induction E
  all_goals
    simp only [Env_.nodup_]
    infer_instance


/--
  `Env_.well_formed E` := True if and only if
  1. Every definition that occurs in the environment `E` has a unique combination of name and argument length.
  2. Every definition that occurs in the formula of a definition `d` in the environment `d :: E' ⊆ E` occurs in the environment `E'`. This means there are no circular definitions.
-/
def Env_.well_formed : Env_ → Prop
  | [] => True
  | d :: E =>
    (∀ (d' : Definition_), d' ∈ E →
      d.name = d'.name → d.args.length = d'.args.length → False) ∧
        Formula_.all_def_in_env E d.q ∧ Env_.well_formed E

instance (E : Env_) : Decidable (E.well_formed) :=
  by
  induction E
  all_goals
    simp only [Env_.well_formed]
    infer_instance


#lint
