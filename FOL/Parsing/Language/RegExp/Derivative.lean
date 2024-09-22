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


def RegExp.simp_derivative
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


example
  {α : Type}
  [DecidableEq α]
  (R S : RegExp α)
  (a : α)
  (h1 : R.LanguageOf = S.LanguageOf) :
  (R.derivative a).LanguageOf = (S.derivative a).LanguageOf :=
  by
    simp only [regexp_lang_derivative_eq_regexp_derivative_lang]
    simp only [h1]


def finset_regexp_language_of
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α)) :
  Language.Language α :=
  ⋃ (R ∈ Γ), R.LanguageOf


def RegExp.derivative_of_finset_wrt_char
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (a : α) :
  Finset (RegExp α) :=
  Finset.biUnion Γ (fun (R : RegExp α) => {RegExp.derivative R a})


lemma regexp_lang_derivative_of_finset_wrt_char_eq_regexp_derivative_of_finset_wrt_char_lang
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (a : α) :
  finset_regexp_language_of (RegExp.derivative_of_finset_wrt_char Γ a) = Language.derivative (finset_regexp_language_of Γ) [a] :=
  by
    simp only [RegExp.derivative_of_finset_wrt_char]
    simp only [finset_regexp_language_of]
    simp
    simp only [regexp_lang_derivative_eq_regexp_derivative_lang]
    rw [Language.derivative_distrib_union_of_finset_wrt_str]


def RegExp.derivative_of_finset_wrt_str
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (s : Str α) :
  Finset (RegExp α) :=
  Finset.biUnion Γ (fun (R : RegExp α) => {RegExp.derivative_wrt_str R s})


lemma regexp_lang_derivative_of_finset_wrt_str_eq_regexp_derivative_of_finset_wrt_str_lang
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (s : Str α) :
  finset_regexp_language_of (RegExp.derivative_of_finset_wrt_str Γ s) = Language.derivative (finset_regexp_language_of Γ) s :=
  by
    simp only [RegExp.derivative_of_finset_wrt_str]
    simp only [finset_regexp_language_of]
    simp
    simp only [regexp_lang_derivative_wrt_str_eq_regexp_derivative_lang]
    rw [Language.derivative_distrib_union_of_finset_wrt_str]


def concat_finset_regexp_regexp
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (β : RegExp α) :
  Finset (RegExp α) :=
  if ¬ β = RegExp.zero
  -- Finset { α β | α ∈ Γ }
  then Γ.image (fun α => RegExp.concat α β)
  else ∅


def RegExp.partial_derivative_wrt_char
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (a : α) :
  Finset (RegExp α) :=
  match RE with
  | char b => if a = b then {epsilon} else ∅
  | epsilon => ∅
  | zero => ∅
  | union α β => (α.partial_derivative_wrt_char a) ∪ (β.partial_derivative_wrt_char a)
  | concat α β =>
      if α.is_nullable
      then (concat_finset_regexp_regexp (α.partial_derivative_wrt_char a) β) ∪ (β.partial_derivative_wrt_char a)
      else (concat_finset_regexp_regexp (α.partial_derivative_wrt_char a) β)
  | kleene_closure α => concat_finset_regexp_regexp (α.partial_derivative_wrt_char a) (RegExp.kleene_closure α)


def RegExp.partial_derivative_of_finset_wrt_char
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (a : α) :
  Finset (RegExp α) :=
  Finset.biUnion Γ (fun (R : RegExp α) => partial_derivative_wrt_char R a)


def RegExp.partial_derivative_of_finset_wrt_str_aux
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α)) :
  Str α → Finset (RegExp α)
  | [] => Γ
  | hd :: tl => RegExp.partial_derivative_of_finset_wrt_str_aux (RegExp.partial_derivative_of_finset_wrt_char Γ hd) tl


def RegExp.partial_derivative_wrt_str
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (s : Str α) :
  Finset (RegExp α) :=
  RegExp.partial_derivative_of_finset_wrt_str_aux {RE} s


def RegExp.partial_derivative_of_finset_wrt_str
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (s : Str α) :
  Finset (RegExp α) :=
  RegExp.partial_derivative_of_finset_wrt_str_aux Γ s


lemma partial_derivative_wrt_str_aux_last
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (s : Str α)
  (a : α) :
  RegExp.partial_derivative_of_finset_wrt_str_aux Γ (s ++ [a]) =
    RegExp.partial_derivative_of_finset_wrt_char (RegExp.partial_derivative_of_finset_wrt_str_aux Γ s) a :=
  by
    induction s generalizing Γ
    case nil =>
      simp
      simp only [RegExp.partial_derivative_of_finset_wrt_str_aux]
    case cons hd tl ih =>
      simp
      simp only [RegExp.partial_derivative_of_finset_wrt_str_aux]
      exact ih (RegExp.partial_derivative_of_finset_wrt_char Γ hd)


lemma partial_derivative_wrt_str_last
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (s : Str α)
  (a : α) :
  RegExp.partial_derivative_wrt_str RE (s ++ [a]) =
    RegExp.partial_derivative_of_finset_wrt_char (RegExp.partial_derivative_wrt_str RE s) a :=
  by
    simp only [RegExp.partial_derivative_wrt_str]
    exact partial_derivative_wrt_str_aux_last {RE} s a


theorem partial_derivative_lang_eq_derivative_lang
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (a : α) :
  finset_regexp_language_of (RE.partial_derivative_wrt_char a) = Language.derivative RE.LanguageOf [a] :=
  by
    simp only [finset_regexp_language_of]
    induction RE
    case char b =>
      simp only [Language.derivative]
      ext cs
      simp
      simp only [RegExp.partial_derivative_wrt_char]
      split_ifs
      case pos c1 =>
        simp
        simp only [RegExp.LanguageOf]
        simp
        intro _
        exact c1
      case neg c1 =>
        simp
        simp only [RegExp.LanguageOf]
        simp
        intro a1
        contradiction
    case epsilon =>
      simp only [RegExp.LanguageOf]
      simp only [Language.derivative_of_eps_wrt_char]
      simp only [RegExp.partial_derivative_wrt_char]
      simp
    case zero =>
      simp only [RegExp.LanguageOf]
      simp only [Language.derivative_of_empty_wrt_char]
      simp only [RegExp.partial_derivative_wrt_char]
      simp
    case union R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      simp only [Language.derivative_of_union_wrt_char]
      simp only [RegExp.partial_derivative_wrt_char]
      simp only [Finset.set_biUnion_union]
      rw [R_ih]
      rw [S_ih]
    case concat R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      simp only [Language.derivative_of_concat_wrt_char]
      simp only [RegExp.partial_derivative_wrt_char]

      split_ifs
      case pos c1 =>
        simp only [regexp_is_nullable_iff_regexp_lang_of_is_nullable] at c1
        simp only [Language.is_nullable_iff_nullify_eq_eps_singleton] at c1
        rw [c1]
        simp only [Language.concat_eps_left]

        simp only [Finset.set_biUnion_union]
        congr
        · simp only [concat_finset_regexp_regexp]
          split_ifs
          case pos c2 =>
            rw [c2]
            simp only [RegExp.LanguageOf]
            simp only [Language.concat_empty_right]
            simp
          case neg c2 =>
            rw [← R_ih]
            rw [← Language.concat_distrib_finset_i_union_right]
            simp
            simp only [RegExp.LanguageOf]
      case neg c1 =>
        simp only [regexp_is_nullable_iff_regexp_lang_of_is_nullable] at c1
        simp only [Language.not_is_nullable_iff_nullify_eq_empty] at c1
        rw [c1]
        simp only [Language.concat_empty_left]
        simp

        simp only [concat_finset_regexp_regexp]
        split_ifs
        case pos c2 =>
          rw [c2]
          simp only [RegExp.LanguageOf]
          simp only [Language.concat_empty_right]
          simp
        case neg c2 =>
          rw [← R_ih]
          rw [← Language.concat_distrib_finset_i_union_right]
          simp
          simp only [RegExp.LanguageOf]

    case kleene_closure R R_ih =>
      simp only [RegExp.LanguageOf]
      simp only [Language.derivative_of_kleene_closure_wrt_char]
      simp only [RegExp.partial_derivative_wrt_char]
      simp only [concat_finset_regexp_regexp]
      simp
      simp only [RegExp.LanguageOf]
      rw [Language.concat_distrib_finset_i_union_right]
      rw [R_ih]


theorem partial_derivative_wrt_char_lang_eq_derivative_lang_wrt_char
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (a : α) :
  finset_regexp_language_of (RegExp.partial_derivative_of_finset_wrt_char Γ a) = Language.derivative (finset_regexp_language_of Γ) [a] :=
  by
    simp only [finset_regexp_language_of]
    simp only [← Language.derivative_distrib_union_of_finset_wrt_str]
    simp only [RegExp.partial_derivative_of_finset_wrt_char]
    simp
    sorry


theorem partial_derivative_wrt_str_lang_eq_derivative_lang_wrt_str
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (s : Str α) :
  finset_regexp_language_of (RegExp.partial_derivative_of_finset_wrt_str Γ s) = Language.derivative (finset_regexp_language_of Γ) s :=
  by
    induction s generalizing Γ
    case nil =>
      simp only [RegExp.partial_derivative_of_finset_wrt_str]
      simp only [RegExp.partial_derivative_of_finset_wrt_str_aux]
      simp only [Language.derivative_wrt_eps]
    case cons hd tl ih =>
      simp only [RegExp.partial_derivative_of_finset_wrt_str] at *
      simp only [RegExp.partial_derivative_of_finset_wrt_str_aux]
      rw [Language.derivative_wrt_cons]
      sorry
