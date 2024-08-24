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
  (α : Type) :
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
  Language.IsRegLang α RE.LanguageOf :=
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


def RegExp.nullify
  {α : Type} :
  RegExp α → RegExp α
  | char _ => zero
  | epsilon => epsilon
  | zero => zero
  | union R S => union R.nullify S.nullify
  | concat R S => concat R.nullify S.nullify
  | kleene_closure _ => epsilon


example
  {α : Type}
  (RE : RegExp α) :
  open Classical in
  if [] ∈ RE.LanguageOf
  then RE.nullify = RegExp.epsilon
  else RE.nullify = RegExp.zero :=
  by
    induction RE
    case char c =>
      simp only [RegExp.nullify]
      simp only [RegExp.LanguageOf]
      simp
    case epsilon =>
      simp only [RegExp.nullify]
      simp only [RegExp.LanguageOf]
      simp
    case zero =>
      simp only [RegExp.nullify]
      simp only [RegExp.LanguageOf]
      simp
    case union R S R_ih S_ih =>
      sorry
    all_goals
      sorry


example
  {α : Type}
  [DecidableEq α]
  (R : RegExp α) :
  R.nullify.LanguageOf = Language.Language.nullify R.LanguageOf :=
  by
    induction R
    case char c =>
      simp only [RegExp.LanguageOf]
      simp only [Language.Language.nullify]
      simp
    case epsilon =>
      simp only [RegExp.LanguageOf]
      simp only [Language.Language.nullify]
      simp
    case zero =>
      simp only [RegExp.LanguageOf]
      simp only [Language.Language.nullify]
      simp
    case union R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      rw [R_ih]
      rw [S_ih]
      simp only [Language.Language.nullify]
      ext cs
      simp
      tauto
    case concat R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      rw [R_ih]
      rw [S_ih]
      simp only [Language.Language.nullify]
      ext cs
      simp
      split_ifs
      case pos c1 c2 =>
        simp only [Language.concat]
        simp
        simp only [c1]
        simp only [c2]
        simp
      case neg c1 c2 =>
        simp only [Language.concat]
        simp
        simp only [c1]
        simp only [c2]
        simp
      case pos c1 c2 =>
        simp only [Language.concat]
        simp
        simp only [c1]
        simp only [c2]
        simp
      case neg c1 c2 =>
        simp only [Language.concat]
        simp
        simp only [c1]
        simp only [c2]
        simp
    case kleene_closure R _ =>
      simp only [RegExp.LanguageOf]
      simp only [Language.Language.nullify]
      split_ifs
      case pos _ =>
        rfl
      case neg c1 =>
        exfalso
        apply c1
        exact Language.eps_mem_kleene_closure (RegExp.LanguageOf α R)


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


example
  {α : Type}
  [DecidableEq α]
  (a : α)
  (R : RegExp α) :
  (R.derivative a).LanguageOf = Language.derivative R.LanguageOf [a] :=
  by
    induction R
    case char c =>
      simp only [RegExp.derivative]
      simp only [Language.derivative]
      split_ifs
      case pos c1 =>
        rw [c1]
        simp only [RegExp.LanguageOf]
        simp
      case neg c1 =>
        simp only [RegExp.LanguageOf]
        simp
        simp only [c1]
        simp
    case epsilon =>
      simp only [RegExp.LanguageOf]
      simp only [Language.derivative]
      simp
    case zero =>
      simp only [RegExp.LanguageOf]
      simp only [Language.derivative]
      simp
    case union R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      rw [R_ih]
      rw [S_ih]
      simp only [Language.derivative]
      ext cs
      simp
    case concat R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      rw [R_ih]
      rw [S_ih]
      sorry
    case kleene_closure R R_ih =>
      sorry


def equal
  (α : Type)
  (R S : RegExp α) :
  Prop :=
  R.LanguageOf = S.LanguageOf


def RegExp.matches
  {α : Type}
  [DecidableEq α]
  (R : RegExp α)
  (s : Str α) :
  Prop :=
  s ∈ R.LanguageOf
