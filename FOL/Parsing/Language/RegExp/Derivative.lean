import FOL.Parsing.Language.RegExp.Nullable


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577
-- https://www.cambridge.org/core/journals/journal-of-functional-programming/article/regularexpression-derivatives-reexamined/E5734B86DEB96C61C69E5CF3C4FB0AFA


namespace RegExp


def RegExp.derivative
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (a : α) :
  RegExp α :=
  match RE with
  | char b => if a = b then epsilon else zero
  | epsilon => zero
  | zero => zero
  | union R S => union (R.derivative a) (S.derivative a)
  | concat R S => union (concat (R.derivative a) S) (concat R.nullify (S.derivative a))
  | kleene_closure R => concat (R.derivative a) (kleene_closure R)


def RegExp.derivative_wrt_str
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α) :
  Str α → RegExp α
  | [] => RE
  | hd :: tl => RegExp.derivative_wrt_str (RegExp.derivative RE hd) tl


lemma regexp_lang_derivative_eq_regexp_derivative_lang
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (a : α) :
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


lemma regexp_lang_derivative_wrt_str_eq_regexp_derivative_lang
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (s : Str α) :
  (RE.derivative_wrt_str s).LanguageOf = Language.derivative RE.LanguageOf s :=
  by
    induction s generalizing RE
    case nil =>
      simp only [RegExp.derivative_wrt_str]
      simp only [Language.derivative_wrt_eps]
    case cons hd tl ih =>
      simp only [RegExp.derivative_wrt_str]
      rw [Language.derivative_wrt_cons]
      simp only [← regexp_lang_derivative_eq_regexp_derivative_lang]
      exact ih (RE.derivative hd)


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
#eval RegExp.matches (RegExp.concat (RegExp.kleene_closure (RegExp.char 'c')) (RegExp.char 'd')) ['c', 'c', 'd']


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
