import FOL.Parsing.Language.RegExp.RegExp


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577
-- https://www.cambridge.org/core/journals/journal-of-functional-programming/article/regularexpression-derivatives-reexamined/E5734B86DEB96C61C69E5CF3C4FB0AFA


namespace RegExp


def is_nullable
  {α : Type} :
  RegExp α → Prop
  | char _ => False
  | epsilon => True
  | zero => False
  | union R S => R.is_nullable ∨ S.is_nullable
  | concat R S => R.is_nullable ∧ S.is_nullable
  | kleene_closure _ => True


instance
  (α : Type)
  [DecidableEq α]
  (RE : RegExp α) :
  Decidable RE.is_nullable :=
  by
    induction RE
    all_goals
      simp only [RegExp.is_nullable]
      infer_instance


lemma regexp_is_nullable_iff_eps_mem_lang_of
  {α : Type}
  (RE : RegExp α) :
  RE.is_nullable ↔ [] ∈ RE.LanguageOf :=
  by
    induction RE
    all_goals
      simp only [RegExp.is_nullable]
      simp only [RegExp.LanguageOf]
    case char c =>
      simp
    case epsilon =>
      simp
    case zero =>
      simp
    case union R S R_ih S_ih =>
      rw [R_ih]
      rw [S_ih]
      simp
    case concat R S R_ih S_ih =>
      rw [R_ih]
      rw [S_ih]
      simp only [Language.eps_mem_concat_iff]
    case kleene_closure R _ =>
      simp
      simp only [Language.eps_mem_kleene_closure]


lemma regexp_is_nullable_iff_regexp_lang_of_is_nullable
  {α : Type}
  (RE : RegExp α) :
  RE.is_nullable ↔ RE.LanguageOf.is_nullable :=
  by
    simp only [Language.is_nullable]
    exact regexp_is_nullable_iff_eps_mem_lang_of RE


def nullify
  {α : Type} :
  RegExp α → RegExp α
  | char _ => zero
  | epsilon => epsilon
  | zero => zero
  | union R S => union R.nullify S.nullify
  | concat R S => concat R.nullify S.nullify
  | kleene_closure _ => epsilon


lemma regexp_nullify_lang_eq_regexp_lang_nullify
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α) :
  RE.nullify.LanguageOf = (RE.LanguageOf).nullify :=
  by
    induction RE
    case char c =>
      simp only [RegExp.LanguageOf]
      simp only [Language.nullify]
      simp
    case epsilon =>
      simp only [RegExp.LanguageOf]
      simp only [Language.nullify_eps]
    case zero =>
      simp only [RegExp.LanguageOf]
      simp only [Language.nullify_empty]
    case union R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      simp only [Language.nullify_union]
      rw [R_ih]
      rw [S_ih]
    case concat R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      simp only [Language.nullify_concat]
      rw [R_ih]
      rw [S_ih]
    case kleene_closure R _ =>
      simp only [RegExp.LanguageOf]
      simp only [Language.nullify_kleene_closure]


example
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α) :
  if RE.is_nullable
  then RE.nullify.LanguageOf = {[]}
  else RE.nullify.LanguageOf = ∅ :=
  by
    rw [regexp_nullify_lang_eq_regexp_lang_nullify]
    split_ifs
    case pos c1 =>
      simp only [Language.nullify]
      rw [regexp_is_nullable_iff_eps_mem_lang_of] at c1
      simp only [c1]
      simp
    case neg c1 =>
      simp only [Language.nullify]
      rw [regexp_is_nullable_iff_eps_mem_lang_of] at c1
      simp only [c1]
      simp
