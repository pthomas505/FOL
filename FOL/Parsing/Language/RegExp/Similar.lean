import FOL.Parsing.Language.RegExp.Derivative


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577
-- https://www.cambridge.org/core/journals/journal-of-functional-programming/article/regularexpression-derivatives-reexamined/E5734B86DEB96C61C69E5CF3C4FB0AFA


namespace RegExp


inductive Similar {α : Type} : RegExp α → RegExp α → Prop
| union_1
  (R : RegExp α) :
  Similar (RegExp.union R R) R

| union_2
  (R S : RegExp α) :
  Similar (RegExp.union R S) (RegExp.union S R)

| union_3
  (R S T : RegExp α) :
  Similar (RegExp.union (RegExp.union R S) T) (RegExp.union R (RegExp.union S T))

| union_4
  (R : RegExp α) :
  Similar (RegExp.union RegExp.zero R) R

| concat_1
  (R S T : RegExp α) :
  Similar (RegExp.concat (RegExp.concat R S) T) (RegExp.concat R (RegExp.concat S T))

| concat_2
  (R : RegExp α) :
  Similar (RegExp.concat RegExp.zero R) RegExp.zero

| concat_3
  (R : RegExp α) :
  Similar (RegExp.concat R RegExp.zero) RegExp.zero

| concat_4
  (R : RegExp α) :
  Similar (RegExp.concat RegExp.epsilon R) R

| concat_5
  (R : RegExp α) :
  Similar (RegExp.concat R RegExp.epsilon) R

| kleene_closure_1
  (R : RegExp α) :
  Similar (RegExp.kleene_closure (RegExp.kleene_closure R)) (RegExp.kleene_closure R)

| kleene_closure_2 :
  Similar (RegExp.kleene_closure RegExp.epsilon) RegExp.epsilon

| kleene_closure_3 :
  Similar (RegExp.kleene_closure RegExp.zero) RegExp.epsilon


example
  {α : Type}
  (RE_1 RE_2 : RegExp α)
  (h1 : Similar RE_1 RE_2) :
  RE_1.LanguageOf = RE_2.LanguageOf :=
  by
    induction h1
    case union_1 R =>
      simp only [RegExp.LanguageOf]
      simp
    case union_2 R S =>
      simp only [RegExp.LanguageOf]
      exact Set.union_comm R.LanguageOf S.LanguageOf
    case union_3 R S T =>
      simp only [RegExp.LanguageOf]
      exact Set.union_assoc R.LanguageOf S.LanguageOf T.LanguageOf
    case union_4 R =>
      simp only [RegExp.LanguageOf]
      exact Set.empty_union R.LanguageOf
    case concat_1 R S T =>
      simp only [RegExp.LanguageOf]
      symm
      exact Language.concat_assoc R.LanguageOf S.LanguageOf T.LanguageOf
    case concat_2 R =>
      simp only [RegExp.LanguageOf]
      exact Language.concat_empty_left R.LanguageOf
    case concat_3 R =>
      simp only [RegExp.LanguageOf]
      exact Language.concat_empty_right R.LanguageOf
    case concat_4 R =>
      simp only [RegExp.LanguageOf]
      exact Language.concat_eps_left R.LanguageOf
    case concat_5 R =>
      simp only [RegExp.LanguageOf]
      exact Language.concat_eps_right R.LanguageOf
    case kleene_closure_1 R =>
      simp only [RegExp.LanguageOf]
      symm
      exact Language.kleene_closure_idempotent R.LanguageOf
    case kleene_closure_2 =>
      simp only [RegExp.LanguageOf]
      exact Language.kleene_closure_eps
    case kleene_closure_3 =>
      simp only [RegExp.LanguageOf]
      exact Language.kleene_closure_empty


def simp_concat
  {α : Type}
  (RE_1 RE_2 : RegExp α) :
  RegExp α :=
  match RE_1 with
  | RegExp.epsilon => RE_2
  | RegExp.zero => RegExp.zero
  | R =>
    match RE_2 with
    | RegExp.epsilon => R
    | RegExp.zero => RegExp.zero
    | S => RegExp.concat R S


lemma simp_concat_lang_eq_concat_lang
  {α : Type}
  (RE_1 RE_2 : RegExp α) :
  (simp_concat RE_1 RE_2).LanguageOf = (RegExp.concat RE_1 RE_2).LanguageOf :=
  by
    simp only [simp_concat]

    induction RE_1 generalizing RE_2
    case epsilon =>
      simp only [RegExp.LanguageOf]
      simp only [Language.concat_eps_left]
    case zero =>
      simp only [RegExp.LanguageOf]
      simp only [Language.concat_empty_left]
    all_goals
      cases RE_2
      case epsilon =>
        simp only [RegExp.LanguageOf]
        simp only [Language.concat_eps_right]
      case zero =>
        simp only [RegExp.LanguageOf]
        simp only [Language.concat_empty_right]
      all_goals
        rfl


def simp_union
  {α : Type}
  (RE_1 RE_2 : RegExp α) :
  RegExp α :=
  match RE_1 with
  | RegExp.zero => RE_2
  | R =>
    match RE_2 with
    | RegExp.zero => R
    | S => RegExp.union R S


lemma simp_union_lang_eq_union_lang
  {α : Type}
  (RE_1 RE_2 : RegExp α) :
  (simp_union RE_1 RE_2).LanguageOf = (RegExp.union RE_1 RE_2).LanguageOf :=
  by
    simp only [simp_union]

    induction RE_1 generalizing RE_2
    case zero =>
      simp only [RegExp.LanguageOf]
      simp
    all_goals
      cases RE_2
      case zero =>
        simp only [RegExp.LanguageOf]
        simp
      all_goals
        rfl


def simp_kleene_closure
  {α : Type}
  (RE : RegExp α) :
  RegExp α :=
  match RE with
  | RegExp.epsilon => RegExp.epsilon
  | RegExp.zero => RegExp.epsilon
  | RegExp.kleene_closure R => simp_kleene_closure R
  | R => RegExp.kleene_closure R


lemma simp_kleene_closure_lang_eq_kleene_closure_lang
  {α : Type}
  (RE : RegExp α) :
  (simp_kleene_closure RE).LanguageOf = (RegExp.kleene_closure RE).LanguageOf :=
  by
    induction RE
    case epsilon =>
      simp only [RegExp.LanguageOf]
      simp only [Language.kleene_closure_eps]
    case zero =>
      simp only [RegExp.LanguageOf]
      simp only [Language.kleene_closure_empty]
    case kleene_closure R R_ih =>
      simp only [RegExp.LanguageOf] at R_ih

      simp only [simp_kleene_closure]
      simp only [RegExp.LanguageOf]
      rw [← Language.kleene_closure_idempotent]
      exact R_ih
    all_goals
      rfl


def simp_derivative
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (a : α) :
  RegExp α :=
  match RE with
  | char b => if a = b then epsilon else zero
  | epsilon => zero
  | zero => zero
  | union R S => simp_union (R.simp_derivative a) (S.simp_derivative a)
  | concat R S => simp_union (simp_concat (R.simp_derivative a) S) (simp_concat R.nullify (S.simp_derivative a))
  | kleene_closure R => simp_concat (R.simp_derivative a) (simp_kleene_closure R)


lemma simp_derivative_lang_eq_derivative_lang
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (a : α) :
  (RegExp.simp_derivative RE a).LanguageOf = (RegExp.derivative RE a).LanguageOf :=
  by
    induction RE
    case union R S R_ih S_ih =>
      simp only [RegExp.simp_derivative]
      simp only [RegExp.derivative]
      simp only [simp_union_lang_eq_union_lang]
      simp only [RegExp.LanguageOf]
      rw [R_ih]
      rw [S_ih]
    case concat R S R_ih S_ih =>
      simp only [RegExp.simp_derivative]
      simp only [RegExp.derivative]
      simp only [simp_union_lang_eq_union_lang]
      simp only [RegExp.LanguageOf]
      simp only [simp_concat_lang_eq_concat_lang]
      simp only [RegExp.LanguageOf]
      rw [R_ih]
      rw [S_ih]
    case kleene_closure R R_ih =>
      simp only [RegExp.simp_derivative]
      simp only [RegExp.derivative]
      simp only [simp_concat_lang_eq_concat_lang]
      simp only [RegExp.LanguageOf]
      simp only [simp_kleene_closure_lang_eq_kleene_closure_lang]
      simp only [RegExp.LanguageOf]
      rw [R_ih]
    all_goals
      rfl
