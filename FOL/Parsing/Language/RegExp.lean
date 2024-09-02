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
  {α : Type}
  (RE : RegExp α) :
  Prop :=
  [] ∈ RE.LanguageOf


def RegExp.nullify
  {α : Type} :
  RegExp α → RegExp α
  | char _ => zero
  | epsilon => epsilon
  | zero => zero
  | union R S => union R.nullify S.nullify
  | concat R S => concat R.nullify S.nullify
  | kleene_closure _ => epsilon


noncomputable
instance
  (α : Type)
  [DecidableEq α]
  (L : Language.Language α) :
  Fintype L.nullify :=
  by
    simp only [Language.Language.nullify]
    split_ifs
    case pos c1 =>
      exact Fintype.subtypeEq []
    case neg c1 =>
      exact Set.fintypeEmpty


instance
  (α : Type)
  [DecidableEq α]
  (RE : RegExp α) :
  Fintype (RE.nullify.LanguageOf) :=
  by
    induction RE
    case char _ =>
      exact Set.fintypeEmpty
    case epsilon =>
      exact Fintype.subtypeEq []
    case zero =>
      exact Set.fintypeEmpty
    case union R S R_ih S_ih =>
      exact Set.fintypeUnion R.nullify.LanguageOf S.nullify.LanguageOf
    case concat R S R_ih S_ih =>
      exact Set.fintypeImage2 (fun a b => a ++ b) R.nullify.LanguageOf S.nullify.LanguageOf
    case kleene_closure _ _ =>
      exact Fintype.subtypeEq []


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
  open Classical in
  if RE.is_nullable
  then RE.nullify.LanguageOf = {[]}
  else RE.nullify.LanguageOf = ∅ :=
  by
    rw [regexp_nullify_lang_eq_regexp_lang_nullify]
    simp only [RegExp.is_nullable]
    simp only [Language.Language.nullify]
    split_ifs
    · rfl
    · rfl


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
  | [] => RE.nullify.LanguageOf.toFinset = {[]}
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
      exact decEq (Set.toFinset RE.nullify.LanguageOf) {[]}
    case cons hd tl ih =>
      simp only [RegExp.matches]
      exact ih (RegExp.derivative hd RE)


#eval RegExp.matches (RegExp.char 'c') ['c']


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
      sorry
      --simp only [regexp_nullify_lang_eq_regexp_lang_nullify]
      --simp only [← Language.is_nullable_iff_nullify_eq_eps_singleton]
      --simp only [Language.Language.is_nullable]
    case cons hd tl ih =>
      simp only [RegExp.matches]
      rw [ih]
      rw [regexp_lang_derivative_eq_regexp_derivative_lang]
      simp only [Language.derivative]
      simp
