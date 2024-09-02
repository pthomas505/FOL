import FOL.Parsing.Language.Regular
import FOL.Parsing.Language.DFA


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577
-- https://www.cambridge.org/core/journals/journal-of-functional-programming/article/regularexpression-derivatives-reexamined/E5734B86DEB96C61C69E5CF3C4FB0AFA


namespace RegExp


inductive RegExp (α : Type) : Type
  | char : α → RegExp α
  | epsilon : RegExp α
  | zero : RegExp α
  | union : RegExp α → RegExp α → RegExp α
  | concat : RegExp α → RegExp α → RegExp α
  | kleene_closure : RegExp α → RegExp α
  deriving Inhabited, DecidableEq

compile_inductive% RegExp


def RegExp.LanguageOf
  {α : Type} :
  RegExp α → Language.Language α
  | char c => {[c]}
  | epsilon => {[]}
  | zero => ∅
  | union R S => R.LanguageOf ∪ S.LanguageOf
  | concat R S => Language.concat R.LanguageOf S.LanguageOf
  | kleene_closure R => Language.kleene_closure α R.LanguageOf


example
  {α : Type}
  (RE : RegExp α) :
  Language.IsRegLang RE.LanguageOf :=
  by
    induction RE
    case char c =>
      simp only [RegExp.LanguageOf]
      exact Language.IsRegLang.char c
    case epsilon =>
      simp only [RegExp.LanguageOf]
      exact Language.IsRegLang.epsilon
    case zero =>
      simp only [RegExp.LanguageOf]
      exact Language.IsRegLang.zero
    case union R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      exact Language.IsRegLang.union R.LanguageOf S.LanguageOf R_ih S_ih
    case concat R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      exact Language.IsRegLang.concat R.LanguageOf S.LanguageOf R_ih S_ih
    case kleene_closure R R_ih =>
      simp only [RegExp.LanguageOf]
      exact Language.IsRegLang.kleene_closure R.LanguageOf R_ih


def RegExp.is_nullable
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
      simp only [Language.concat]
      simp
    case kleene_closure R _ =>
      simp
      simp only [Language.eps_mem_kleene_closure]


def RegExp.nullify
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
      simp only [Language.Language.nullify]
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


lemma regexp_is_nullable_ite
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
      simp only [Language.Language.nullify]
      rw [regexp_is_nullable_iff_eps_mem_lang_of] at c1
      simp only [c1]
      simp
    case neg c1 =>
      simp only [Language.Language.nullify]
      rw [regexp_is_nullable_iff_eps_mem_lang_of] at c1
      simp only [c1]
      simp


def RegExp.derivative
  {α : Type}
  [DecidableEq α]
  (a : α) :
  RegExp α → RegExp α
  | char b => if a = b then epsilon else zero
  | epsilon => zero
  | zero => zero
  | union R S => union (R.derivative a) (S.derivative a)
  | concat R S => union (concat (R.derivative a) S) (concat R.nullify (S.derivative a))
  | kleene_closure R => concat (R.derivative a) (kleene_closure R)


lemma regexp_lang_derivative_eq_regexp_derivative_lang
  {α : Type}
  [DecidableEq α]
  (a : α)
  (RE : RegExp α) :
  (RE.derivative a).LanguageOf = Language.derivative RE.LanguageOf [a] :=
  by
    induction RE
    case char c =>
      simp only [RegExp.derivative]
      split_ifs
      case pos c1 =>
        rw [c1]
        simp only [RegExp.LanguageOf]
        simp only [Language.derivative_of_char_wrt_same_char]
      case neg c1 =>
        simp only [RegExp.LanguageOf]
        simp only [Language.derivative_of_char_wrt_diff_char a c c1]
    case epsilon =>
      simp only [RegExp.LanguageOf]
      simp only [Language.derivative_of_eps_wrt_char]
    case zero =>
      simp only [RegExp.LanguageOf]
      simp only [Language.derivative_of_empty_wrt_char]
    case union R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      rw [R_ih]
      rw [S_ih]
      simp only [Language.derivative_of_union_wrt_char]
    case concat R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      rw [R_ih]
      rw [S_ih]
      simp only [Language.derivative_of_concat_wrt_char]
      simp only [regexp_nullify_lang_eq_regexp_lang_nullify]
    case kleene_closure R R_ih =>
      simp only [RegExp.LanguageOf]
      rw [R_ih]
      simp only [Language.derivative_of_kleene_closure_wrt_char]


def equal
  (α : Type)
  (R S : RegExp α) :
  Prop :=
  R.LanguageOf = S.LanguageOf


def RegExp.matches
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α) :
  Str α → Prop
  | [] => RE.is_nullable
  | hd :: tl => (RE.derivative hd).matches tl


instance
  (α : Type)
  [DecidableEq α]
  (RE : RegExp α)
  (s : Str α) :
  Decidable (RE.matches s) :=
  by
    induction s generalizing RE
    case nil =>
      simp only [RegExp.matches]
      infer_instance
    case cons hd tl ih =>
      simp only [RegExp.matches]
      infer_instance


#eval RegExp.matches (RegExp.char 'c') ['c']
#eval RegExp.matches (RegExp.char 'c') ['d']
#eval RegExp.matches (RegExp.kleene_closure (RegExp.char 'c')) ['c', 'c']


example
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (s : Str α) :
  RE.matches s ↔ s ∈ RE.LanguageOf :=
  by
    induction s generalizing RE
    case nil =>
      simp only [RegExp.matches]
      exact regexp_is_nullable_iff_eps_mem_lang_of RE
    case cons hd tl ih =>
      simp only [RegExp.matches]
      rw [ih]
      rw [regexp_lang_derivative_eq_regexp_derivative_lang]
      simp only [Language.derivative]
      simp
