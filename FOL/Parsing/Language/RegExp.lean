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
      simp only [Language.eps_mem_concat_iff]
    case kleene_closure R _ =>
      simp
      simp only [Language.eps_mem_kleene_closure]


lemma regexp_is_nullable_iff_regexp_lang_of_is_nullable
  {α : Type}
  (RE : RegExp α) :
  RE.is_nullable ↔ RE.LanguageOf.is_nullable :=
  by
    simp only [Language.Language.is_nullable]
    exact regexp_is_nullable_iff_eps_mem_lang_of RE


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


def regexp_equiv
  {α : Type}
  (R S : RegExp α) :
  Prop :=
  R.LanguageOf = S.LanguageOf


def RegExp.equiv_class
  {α : Type}
  (R : RegExp α) :=
  {S : RegExp α | regexp_equiv R S}


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


lemma finset_regexp_language_of_union
  {α : Type}
  [DecidableEq α]
  (S T : Finset (RegExp α)) :
  finset_regexp_language_of (S ∪ T) = finset_regexp_language_of S ∪ finset_regexp_language_of T :=
  by
    simp only [finset_regexp_language_of]
    exact Finset.set_biUnion_union S T fun x => x.LanguageOf


def concat_finset_regexp_regexp
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (β : RegExp α) :
  Finset (RegExp α) :=
  if ¬ β = RegExp.zero ∧ ¬ β = RegExp.epsilon
  -- Finset { α β | α ∈ Γ }
  then Γ.image (fun α => RegExp.concat α β)
  else
    if β = RegExp.zero
    then ∅
    else Γ


def concat_finset_regexp_regexp_alt
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (β : RegExp α) :
  Finset (RegExp α) :=
  if ¬ β = RegExp.zero
  -- Finset { α β | α ∈ Γ }
  then Γ.image (fun α => RegExp.concat α β)
  else ∅


example
  {α : Type}
  [DecidableEq α]
  (Γ : Finset (RegExp α))
  (β : RegExp α) :
  finset_regexp_language_of (concat_finset_regexp_regexp Γ β) = finset_regexp_language_of (concat_finset_regexp_regexp_alt Γ β) :=
  by
    simp only [concat_finset_regexp_regexp]
    simp only [concat_finset_regexp_regexp_alt]
    ext re
    simp
    split_ifs
    case pos c1 c2 =>
      tauto
    case neg c1 c2 =>
      rfl
    case pos c1 c2 =>
      rfl
    case neg c1 c2 =>
      simp at c1
      specialize c1 c2
      rw [c1]
      simp only [finset_regexp_language_of]
      simp
      simp only [RegExp.LanguageOf]
      simp only [Language.concat_eps_right]


def RegExp.partial_derivative
  {α : Type}
  [DecidableEq α]
  (a : α) :
  RegExp α → Finset (RegExp α)
  | char b => if a = b then {epsilon} else ∅
  | epsilon => ∅
  | zero => ∅
  | union α β => (α.partial_derivative a) ∪ (β.partial_derivative a)
  | concat α β =>
      if α.is_nullable
      then (concat_finset_regexp_regexp (α.partial_derivative a) β) ∪ (β.partial_derivative a)
      else (concat_finset_regexp_regexp (α.partial_derivative a) β)
  | kleene_closure α => concat_finset_regexp_regexp (α.partial_derivative a) (RegExp.kleene_closure α)


def RegExp.partial_derivative_alt
  {α : Type}
  [DecidableEq α]
  (a : α) :
  RegExp α → Finset (RegExp α)
  | char b => if a = b then {epsilon} else ∅
  | epsilon => ∅
  | zero => ∅
  | union α β => (α.partial_derivative_alt a) ∪ (β.partial_derivative_alt a)
  | concat α β =>
      if α.is_nullable
      then (concat_finset_regexp_regexp_alt (α.partial_derivative_alt a) β) ∪ (β.partial_derivative_alt a)
      else (concat_finset_regexp_regexp_alt (α.partial_derivative_alt a) β)
  | kleene_closure α => concat_finset_regexp_regexp_alt (α.partial_derivative_alt a) (RegExp.kleene_closure α)


theorem RegExp.extracted_1
  {α : Type}
  [inst : DecidableEq α]
  (S : RegExp α)
  (Γ : Finset (RegExp α))
  (re : Str α)
  (h1 : re ∈ finset_regexp_language_of (concat_finset_regexp_regexp Γ S)) :
  re ∈ Language.concat (finset_regexp_language_of Γ) S.LanguageOf :=
  by
    simp only [concat_finset_regexp_regexp] at h1
    split_ifs at h1
    case _ c2 =>
      simp only [finset_regexp_language_of] at h1
      simp at h1
      simp only [RegExp.LanguageOf] at h1
      simp only [Language.concat] at h1
      simp at h1
      simp only [finset_regexp_language_of]
      simp only [Language.concat]
      simp
      aesop
    case _ c2 c3 =>
      simp only [finset_regexp_language_of] at h1
      simp at h1
    case _ c2 c3 =>
      simp at c2
      specialize c2 c3
      rw [c2]
      simp only [RegExp.LanguageOf]
      simp only [Language.concat_eps_right]
      exact h1


example
  {α : Type}
  [DecidableEq α]
  (a : α)
  (RE : RegExp α) :
  finset_regexp_language_of (RE.partial_derivative a) = Language.derivative RE.LanguageOf [a] :=
  by
    induction RE
    case char b =>
      simp only [finset_regexp_language_of]
      simp only [Language.derivative]
      simp only [RegExp.LanguageOf]
      ext re
      simp
      simp only [RegExp.partial_derivative]
      split_ifs
      case pos c1 =>
        rw [c1]
        simp
        simp only [RegExp.LanguageOf]
        simp
      case neg c1 =>
        simp
        simp only [c1]
        simp
    case union R S R_ih S_ih =>
      simp only [Language.derivative]
      simp only [RegExp.LanguageOf]
      ext re
      simp only [RegExp.partial_derivative]
      simp only [finset_regexp_language_of_union]
      simp
      congr! 1
      · simp only [R_ih]
        simp only [Language.derivative]
        simp
      · simp only [S_ih]
        simp only [Language.derivative]
        simp
    case concat R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      simp only [Language.derivative_of_concat_wrt_char]
      rw [← R_ih]
      rw [← S_ih]
      ext re
      simp
      constructor
      · intro a1
        simp only [RegExp.partial_derivative] at a1
        split_ifs at a1
        case pos c1 =>
          simp only [regexp_is_nullable_iff_regexp_lang_of_is_nullable] at c1
          simp only [Language.is_nullable_iff_nullify_eq_eps_singleton] at c1
          simp only [c1]
          simp only [Language.concat_eps_left]

          simp only [finset_regexp_language_of_union] at a1
          simp at a1
          cases a1
          case _ a1_left =>
            left
            apply RegExp.extracted_1
            exact a1_left
          case _ a1_right =>
            right
            exact a1_right
        case neg c1 =>
          simp only [regexp_is_nullable_iff_regexp_lang_of_is_nullable] at c1
          simp only [Language.not_is_nullable_iff_nullify_eq_empty] at c1
          simp only [c1]
          simp only [Language.concat_empty_left]
          simp
          apply RegExp.extracted_1
          exact a1
      · intro a1
        cases a1
        case _ a1_left =>
          simp only [RegExp.partial_derivative]
          split_ifs
          case pos c1 =>
            simp only [finset_regexp_language_of_union]
            simp
            simp only [finset_regexp_language_of] at a1_left
            simp only [Language.concat] at a1_left
            simp at a1_left
            simp only [finset_regexp_language_of]
            simp
            simp only [concat_finset_regexp_regexp]
            split_ifs
            case pos c1 c2 =>
              simp
              simp only [RegExp.LanguageOf]
              simp only [Language.concat]
              simp
              aesop
            case neg c1 c2 c3 =>
              simp at c2
              specialize c2 c3
              simp only [c2]
              simp only [RegExp.partial_derivative]
              simp
              obtain ⟨s, ⟨i, a2, a3⟩, t, a4, a5 ⟩ := a1_left
              simp only [c2] at a4
              simp only [RegExp.LanguageOf] at a4
              simp at a4
              rw [a4] at a5
              simp at a5
              rw [a5] at a3
              apply Exists.intro i
              exact ⟨a2, a3⟩
            case pos c1 c2 c3 =>
              simp at c2
              simp
              obtain ⟨s, ⟨i, a2, a3⟩, t, a4, a5 ⟩ := a1_left
              rw [c3] at a4
              simp only [RegExp.LanguageOf] at a4
              simp at a4
          case neg c1 =>
            simp only [RegExp.regexp_is_nullable_iff_regexp_lang_of_is_nullable] at c1
            simp only [Language.not_is_nullable_iff_nullify_eq_empty] at c1
            simp only [Language.concat] at a1_left
            simp at a1_left
            simp only [concat_finset_regexp_regexp]
            split_ifs
            case _ c2 =>
              simp only [finset_regexp_language_of]
              simp
              simp only [RegExp.LanguageOf]
              simp only [Language.concat]
              simp
              simp only [finset_regexp_language_of] at a1_left
              simp at a1_left
              aesop
            case _ c2 c3 =>
              simp at c2
              simp only [finset_regexp_language_of] at a1_left
              simp at a1_left
              obtain ⟨s, ⟨i, a2, a3⟩, t, a4, a5 ⟩ := a1_left
              rw [c3] at a4
              simp only [RegExp.LanguageOf] at a4
              simp at a4
            case _ c2 c3 =>
              simp at c2
              specialize c2 c3
              rw [c2] at a1_left
              simp only [RegExp.LanguageOf] at a1_left
              simp at a1_left
              exact a1_left
        case _ a1_right =>
          simp only [RegExp.partial_derivative]
          simp only [Language.mem_concat_nullify_left_iff] at a1_right
          cases a1_right
          case _ a1_right_left a1_right_right =>
            simp only [← RegExp.regexp_is_nullable_iff_eps_mem_lang_of] at a1_right_left
            simp only [a1_right_left]
            simp
            simp only [finset_regexp_language_of_union]
            simp
            right
            exact a1_right_right
    all_goals
      sorry


example
  {α : Type}
  [DecidableEq α]
  (a : α)
  (RE : RegExp α) :
  finset_regexp_language_of (RE.partial_derivative_alt a) = Language.derivative RE.LanguageOf [a] :=
  by
    simp only [finset_regexp_language_of]
    induction RE
    case char b =>
      simp only [Language.derivative]
      ext cs
      simp
      simp only [RegExp.partial_derivative_alt]
      split_ifs
      case pos c1 =>
        simp
        simp only [RegExp.LanguageOf]
        simp
        intro a1
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
      simp only [RegExp.partial_derivative_alt]
      simp
    case zero =>
      simp only [RegExp.LanguageOf]
      simp only [Language.derivative_of_empty_wrt_char]
      simp only [RegExp.partial_derivative_alt]
      simp
    case union R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      simp only [Language.derivative_of_union_wrt_char]
      simp only [RegExp.partial_derivative_alt]
      simp only [Finset.set_biUnion_union]
      rw [R_ih]
      rw [S_ih]
    case concat R S R_ih S_ih =>
      simp only [RegExp.LanguageOf]
      simp only [Language.derivative_of_concat_wrt_char]
      simp only [RegExp.partial_derivative_alt]

      split_ifs
      case pos c1 =>
        simp only [regexp_is_nullable_iff_regexp_lang_of_is_nullable] at c1
        simp only [Language.is_nullable_iff_nullify_eq_eps_singleton] at c1
        rw [c1]
        simp only [Language.concat_eps_left]

        simp only [Finset.set_biUnion_union]
        congr
        · simp only [concat_finset_regexp_regexp_alt]
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

        simp only [concat_finset_regexp_regexp_alt]
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
    all_goals
      sorry
