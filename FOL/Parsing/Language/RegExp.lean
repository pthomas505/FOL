import FOL.Parsing.Language.Regular


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577
-- https://www.cambridge.org/core/journals/journal-of-functional-programming/article/regularexpression-derivatives-reexamined/E5734B86DEB96C61C69E5CF3C4FB0AFA


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
  (α : Type) :
  RegExp α → Language.Language α
  | char c => {[c]}
  | epsilon => {[]}
  | zero => ∅
  | union E1 E2 => E1.LanguageOf ∪ E2.LanguageOf
  | concat E1 E2 => Language.concat E1.LanguageOf E2.LanguageOf
  | kleene_closure E => Language.kleene_closure α E.LanguageOf


example
  {α : Type}
  (E : RegExp α) :
  Language.IsRegLang α E.LanguageOf :=
  by
    induction E
    case char c =>
      simp only [RegExp.LanguageOf]
      exact Language.IsRegLang.char c
    case epsilon =>
      simp only [RegExp.LanguageOf]
      exact Language.IsRegLang.epsilon
    case zero =>
      simp only [RegExp.LanguageOf]
      exact Language.IsRegLang.zero
    case union E1 E2 E1_ih E2_ih =>
      simp only [RegExp.LanguageOf]
      exact Language.IsRegLang.union E1.LanguageOf E2.LanguageOf E1_ih E2_ih
    case concat E1 E2 E1_ih E2_ih =>
      simp only [RegExp.LanguageOf]
      exact Language.IsRegLang.concat E1.LanguageOf E2.LanguageOf E1_ih E2_ih
    case kleene_closure E E_ih =>
      simp only [RegExp.LanguageOf]
      exact Language.IsRegLang.kleene_closure E.LanguageOf E_ih
