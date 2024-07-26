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

| closure
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
    case closure R' ih_1 ih_2 =>
      simp only [derivative_of_kleene_closure_wrt_char]
      apply IsRegLang.concat
      · exact ih_2
      · exact IsRegLang.closure R' ih_1


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
      have s1 : hd :: tl = [hd] ++ tl := rfl
      rw [s1]
      clear s1

      rw [derivative_wrt_append]
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


example
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a1 a2 : α) :
  derivative (kleene_closure α L) [a1, a2] =
    concat (derivative L [a1, a2]) (kleene_closure α L) ∪
      concat (derivative L [a1]).nullify (concat (derivative L [a2]) (kleene_closure α L)) :=
  by
    have s1 : [a1, a2] = [a1] ++ [a2] := rfl
    rw [s1]
    clear s1

    simp only [derivative_wrt_append]
    rw [derivative_of_kleene_closure_wrt_char]
    rw [derivative_of_concat_wrt_char]
    rw [derivative_of_kleene_closure_wrt_char]


example
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a1 a2 a3 : α) :
  derivative (kleene_closure α L) [a1, a2, a3] =
    concat (derivative L [a1, a2, a3]) (kleene_closure α L) ∪
      concat (derivative L [a1, a2]).nullify (concat (derivative L [a3]) (kleene_closure α L)) ∪
        (concat (derivative L [a1]).nullify (concat (derivative L [a2, a3]) (kleene_closure α L) ∪
            concat (derivative L [a2]).nullify (concat (derivative L [a3]) (kleene_closure α L)))) :=
  by
    have s1 : [a1, a2, a3] = [a1] ++ [a2] ++ [a3] := rfl
    rw [s1]
    clear s1

    rw [derivative_wrt_append]
    simp

    -----
    have s2 : [a1, a2] = [a1] ++ [a2] := rfl
    rw [s2]
    clear s2

    simp only [derivative_wrt_append]
    rw [derivative_of_kleene_closure_wrt_char]
    rw [derivative_of_concat_wrt_char]
    rw [derivative_of_kleene_closure_wrt_char]
    -----

    rw [derivative_of_union_wrt_char]
    simp only [derivative_of_concat_wrt_char]
    rw [derivative_of_kleene_closure_wrt_char]

    simp only [nullify_idempotent]
    simp only [derivative_of_nullify_wrt_char]
    simp only [concat_empty_left]
    simp
    simp only [← derivative_wrt_append]
    simp


example
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a1 a2 a3 a4 : α) :
  derivative (kleene_closure α L) [a1, a2, a3, a4] =
    concat (derivative L [a1, a2, a3, a4]) (kleene_closure α L) ∪
      concat (concat (derivative L [a1, a2, a3]).nullify (derivative L [a4])) (kleene_closure α L) ∪
        (concat (concat (derivative L [a1, a2]).nullify (derivative L [a3, a4])) (kleene_closure α L) ∪
          concat (concat (concat (derivative L [a1, a2]).nullify (derivative L [a3]).nullify) (derivative L [a4])) (kleene_closure α L)) ∪
            (concat (concat (derivative L [a1]).nullify (derivative L [a2, a3, a4])) (kleene_closure α L) ∪
              concat (concat (concat (derivative L [a1]).nullify (derivative L [a2, a3]).nullify) (derivative L [a4])) (kleene_closure α L) ∪
                (concat (concat (concat (derivative L [a1]).nullify (derivative L [a2]).nullify) (derivative L [a3, a4])) (kleene_closure α L) ∪
                  concat (concat (concat (concat (derivative L [a1]).nullify (derivative L [a2]).nullify) (derivative L [a3]).nullify) (derivative L [a4])) (kleene_closure α L))) :=
  by
    have s1 : [a1, a2, a3, a4] = [a1] ++ [a2] ++ [a3] ++ [a4]:= rfl
    rw [s1]
    clear s1

    simp only [derivative_wrt_append]
    simp only [derivative_of_kleene_closure_wrt_char, derivative_of_concat_wrt_char, derivative_of_union_wrt_char]
    simp only [nullify_idempotent]
    simp only [derivative_of_nullify_wrt_char]
    simp only [derivative_of_empty_wrt_char]
    simp only [concat_empty_left]
    simp
    simp only [nullify_empty]
    simp only [concat_empty_left]
    simp
    simp only [← derivative_wrt_append]
    simp
    simp only [concat_distrib_union_left]
    simp only [concat_assoc]


example
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (s : Str α)
  (h1 : ¬ s = []) :
  ∃ (T : List (List α)), T ⊆ s.tails ∧ [] ∉ T ∧
    derivative (kleene_closure α L) s =
    ⋃ t ∈ T, concat (derivative L t) (kleene_closure α L) :=
  by
    let a :: s := s
    rw [← List.singleton_append, derivative_wrt_append, derivative_of_kleene_closure_wrt_char, derivative_of_concat_wrt_str]
    simp only [← derivative_wrt_append, List.singleton_append]

    apply Exists.intro ((a :: s) :: s.tails.filter (open Classical in fun v => v ≠ [] ∧ [] ∈ derivative L (a :: s.take (s.length - v.length))))
    constructor
    · simp [List.subset_def, List.mem_filter]; aesop
    · constructor
      · simp [List.mem_filter]
      · simp; congr 1; ext x; simp [List.mem_filter, List.IsSuffix]
        have s1 {u v} (H : u ++ v = s) : List.take (s.length - v.length) s = u := H ▸ by simp
        obtain s10 := take_append_len_left s
        have s2 : ∀ (X Y : Language α) (s : Str α), s ∈ concat X.nullify Y ↔ [] ∈ X ∧ s ∈ Y := by
          simp [concat, Language.nullify]
          aesop
        constructor
        · intro a1
          obtain ⟨M, ⟨u, v, a2, a3, a4⟩, a5⟩ := a1
          apply Exists.intro v
          constructor
          · constructor
            · apply Exists.intro u
              exact a2
            · constructor
              · exact a3
              · obtain H3 := s1 a2
                rw [H3]
                obtain s3 := s2 (derivative L (a :: u)) (derivative (kleene_closure α L) v) x
                rw [← a4] at s3
                obtain ⟨s3_left, s3_right⟩ := s3
                specialize s3_left a5
                tauto
          · simp only [concat]
            simp
            rw [a4] at a5
            clear a4
            simp only [concat] at a5
            simp at a5
            obtain ⟨s1, hs1, t1, ht1, eq⟩ := a5
            specialize s2 (derivative L (a :: u)) (derivative (kleene_closure α L) v) (s1 ++ t1)
            have s3 : s1 ++ t1 ∈ concat (derivative L (a :: u)).nullify (derivative (kleene_closure α L) v)  := append_mem_concat (derivative L (a :: u)).nullify (derivative (kleene_closure α L) v) s1 t1 hs1 ht1
            obtain ⟨H2_left, H2_right⟩ := s2
            specialize H2_left s3
            clear s3
            obtain ⟨H2_left_left, H2_left_right⟩ := H2_left
            clear H2_right
            simp only [Language.nullify] at hs1
            simp at hs1
            simp only [derivative] at hs1
            simp at hs1
            simp only [derivative] at ht1
            simp at ht1
            simp only [derivative] at H2_left_left
            simp at H2_left_left
            obtain ⟨hs1_left, hs1_right⟩ := hs1
            subst hs1_right
            simp at *
            rw [← eq]
            simp only [derivative]
            simp
            simp only [derivative] at H2_left_right
            simp at H2_left_right
            sorry
        · intro a1
          obtain ⟨i, ⟨⟨u, hu⟩, a6, a7 ⟩, z, a4, ⟨v, ⟨ a8, a9⟩ ⟩⟩ := a1
          apply Exists.intro (concat (derivative L (a :: u)).nullify (derivative (kleene_closure α L) i))
          constructor
          · apply Exists.intro u
            apply Exists.intro i
            constructor
            · exact hu
            · constructor
              · exact a6
              · rfl
          · rw [← a9]
            clear a9
            obtain s5 := s2 (derivative L (a :: u)) (derivative (kleene_closure α L) i) (z ++ v)
            rw [s5]
            clear s5
            clear s2
            constructor
            · specialize @s1 u i hu
              rw [s1] at a7
              exact a7
            · specialize @s1 u i hu
              simp only [s1] at a7
              simp only [derivative]
              simp
              simp only [derivative] at a4
              simp at a4
              rw [String.str_append_assoc]
              apply append_kleene_closure_closed
              · exact mem_language_mem_kleene_closure L (i ++ z) a4
              · exact a8


theorem thm_18
  {α : Type}
  [DecidableEq α]
  (R : Language α)
  (h1: IsRegLang α R) :
  Finite { derivative R s | s : Str α } :=
  by
    sorry
