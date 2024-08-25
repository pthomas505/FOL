import FOL.Parsing.Language.Equiv


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577


namespace Language


inductive IsRegLang (α : Type) : Language α → Prop
| char
  (a : α) :
  IsRegLang α {[a]}

| epsilon :
  IsRegLang α {[]}

| zero :
  IsRegLang α ∅

| union
  (R1 R2 : Language α) :
  IsRegLang α R1 →
  IsRegLang α R2 →
  IsRegLang α (R1 ∪ R2)

| concat
  (R1 R2 : Language α) :
  IsRegLang α R1 →
  IsRegLang α R2 →
  IsRegLang α (concat R1 R2)

| kleene_closure
  (R : Language α) :
  IsRegLang α R →
  IsRegLang α (kleene_closure α R)


theorem derivative_of_reg_lang_wrt_char_is_reg_lang
  {α : Type}
  [DecidableEq α]
  (R : Language α)
  (a : α)
  (h1 : IsRegLang α R) :
  IsRegLang α (derivative R [a]) :=
  by
    induction h1
    case char b =>
      by_cases c1 : a = b
      case pos =>
        rw [c1]
        simp only [derivative_of_char_wrt_same_char]
        exact IsRegLang.epsilon
      case neg =>
        simp only [derivative_of_char_wrt_diff_char a b c1]
        exact IsRegLang.zero
    case epsilon =>
      simp only [derivative_of_eps_wrt_char]
      exact IsRegLang.zero
    case zero =>
      simp only [derivative_of_empty_wrt_char]
      exact IsRegLang.zero
    case union R1 R2 ih_1 ih_2 ih_3 ih_4 =>
      simp only [derivative_of_union_wrt_char]
      exact IsRegLang.union (derivative R1 [a]) (derivative R2 [a]) ih_3 ih_4
    case concat R1 R2 ih_1 ih_2 ih_3 ih_4 =>
      simp only [derivative_of_concat_wrt_char]
      apply IsRegLang.union
      · exact IsRegLang.concat (derivative R1 [a]) R2 ih_3 ih_2
      · apply IsRegLang.concat
        · simp only [Language.nullify]
          split_ifs
          case pos c1 =>
            exact IsRegLang.epsilon
          case neg c1 =>
            exact IsRegLang.zero
        · exact ih_4
    case kleene_closure R' ih_1 ih_2 =>
      simp only [derivative_of_kleene_closure_wrt_char]
      apply IsRegLang.concat
      · exact ih_2
      · exact IsRegLang.kleene_closure R' ih_1


theorem derivative_of_reg_lang_wrt_str_is_reg_lang
  {α : Type}
  [DecidableEq α]
  (R : Language α)
  (s : Str α)
  (h1: IsRegLang α R) :
  IsRegLang α (derivative R s) :=
  by
    induction s generalizing R
    case nil =>
      simp only [derivative]
      simp
      exact h1
    case cons hd tl ih =>
      rw [derivative_wrt_cons]
      apply ih
      apply derivative_of_reg_lang_wrt_char_is_reg_lang
      exact h1


example
  {α : Type}
  [DecidableEq α]
  (s : Str α) :
  derivative ∅ s = ∅ := rfl

example
  {α : Type}
  [DecidableEq α] :
  derivative {([] : Str α)} [] = {[]} := rfl

example
  {α : Type}
  [DecidableEq α]
  (s : Str α)
  (h1 : ¬ s = []) :
  derivative {([] : Str α)} s = ∅ :=
  by
    simp only [derivative]
    simp
    simp only [h1]
    simp

example
  {α : Type}
  [DecidableEq α]
  (a : α) :
  derivative {[a]} [] = {[a]} := rfl

example
  {α : Type}
  [DecidableEq α]
  (a : α) :
  derivative {[a]} [a] = {[]} :=
  by
    exact derivative_of_char_wrt_same_char a

example
  {α : Type}
  [DecidableEq α]
  (s : Str α)
  (a : α)
  (h1 : ¬ s = [])
  (h2 : ¬ s = [a]) :
  derivative {[a]} s = ∅ :=
  by
    cases s
    case nil =>
      simp at h1
    case cons hd tl =>
      simp at h2
      simp only [derivative]
      simp
      ext cs
      simp
      tauto


example
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (s : Str α) :
  derivative (L1 ∪ L2) s = derivative L1 s ∪ derivative L2 s := rfl


theorem thm_18
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (h1: IsRegLang α L) :
  Finite { derivative L s | s : Str α } :=
  by
    induction h1
    case char c =>
      have s1 : {x | ∃ (s : Str α), derivative {[c]} s = x} ⊆ {{}, {[]}, {[c]}} :=
      by
        simp only [Set.subset_def]
        simp
        intro s
        cases s
        case nil =>
          right; right;
          exact derivative_wrt_eps {[c]}
        case cons hd tl =>
          cases tl
          case nil =>
            by_cases c1 : hd = c
            case pos =>
              rw [c1]
              right; left;
              exact derivative_of_char_wrt_same_char c
            case neg =>
              left
              exact derivative_of_char_wrt_diff_char hd c c1
          case cons tl_hd tl_tl =>
            simp only [derivative]
            simp
      apply Set.Finite.subset _ s1
      exact Set.toFinite {∅, {[]}, {[c]}}
    case epsilon =>
      have s1 : {x | ∃ (s : Str α), derivative {[]} s = x} ⊆ {∅, {[]}} :=
      by
        simp only [Set.subset_def]
        simp
        intro s
        cases s
        case nil =>
          right;
          exact derivative_wrt_eps {[]}
        case cons hd tl =>
          left;
          rw [derivative_wrt_cons]
          simp only [derivative_of_eps_wrt_char]
          exact derivative_of_empty_wrt_str tl
      apply Set.Finite.subset _ s1
      exact Set.toFinite {∅, {[]}}
    case zero =>
      have s1 : {x | ∃ (s : Str α), derivative ∅ s = x} ⊆ {∅} :=
      by
        simp only [Set.subset_def]
        simp
        intro s
        exact derivative_of_empty_wrt_str s
      apply Set.Finite.subset _ s1
      exact Set.finite_singleton ∅
    case union L1 L2 L1_ih1 L2_ih1 L1_ih2 L2_ih2 =>
      simp only [derivative_of_union_wrt_str]

      have s1 : {x | ∃ s, derivative L1 s = x} = ⋃ (s : Str α), {derivative L1 s} :=
      by
        ext cs
        simp
      rw [s1] at L1_ih2

      have s2 : {x | ∃ s, derivative L2 s = x} = ⋃ (s : Str α), {derivative L2 s} :=
      by
        ext cs
        simp
      rw [s2] at L2_ih2

      have s3 : {x | ∃ s, derivative L1 s ∪ derivative L2 s = x} = ⋃ (s : Str α), {derivative L1 s ∪ derivative L2 s} :=
      by
        ext cs
        simp
      rw [s3]

      clear s1; clear s2; clear s3;
      sorry
    all_goals
      sorry
