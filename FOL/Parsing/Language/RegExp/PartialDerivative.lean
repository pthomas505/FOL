import FOL.Parsing.Language.RegExp.Derivative


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577
-- https://www.cambridge.org/core/journals/journal-of-functional-programming/article/regularexpression-derivatives-reexamined/E5734B86DEB96C61C69E5CF3C4FB0AFA


namespace RegExp


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
  Language α :=
  ⋃ (R ∈ Γ), R.LanguageOf


def derivative_of_finset_wrt_char
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


def derivative_of_finset_wrt_str
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


def partial_derivative_wrt_char
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


def partial_derivative_of_finset_wrt_char
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (a : α) :
  Finset (RegExp α) :=
  Finset.biUnion Γ (fun (R : RegExp α) => partial_derivative_wrt_char R a)


def partial_derivative_of_finset_wrt_str_aux
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α)) :
  Str α → Finset (RegExp α)
  | [] => Γ
  | hd :: tl => RegExp.partial_derivative_of_finset_wrt_str_aux (RegExp.partial_derivative_of_finset_wrt_char Γ hd) tl


def partial_derivative_wrt_str
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (s : Str α) :
  Finset (RegExp α) :=
  RegExp.partial_derivative_of_finset_wrt_str_aux {RE} s


def partial_derivative_of_finset_wrt_str
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
