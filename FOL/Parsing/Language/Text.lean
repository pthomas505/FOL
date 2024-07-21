import FOL.Parsing.Language.Equiv


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577


-------------------------------------------------------------------------------

namespace Languages



-------------------------------------------------------------------------------









-------------------------------------------------------------------------------


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


theorem thm_17_aux
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
        simp only [thm_12_3]
        exact IsRegLang.epsilon
      case neg =>
        simp only [thm_12_4 a b c1]
        exact IsRegLang.zero
    case epsilon =>
      simp only [thm_12_2]
      exact IsRegLang.zero
    case zero =>
      simp only [thm_12_1]
      exact IsRegLang.zero
    case union R1 R2 ih_1 ih_2 ih_3 ih_4 =>
      simp only [thm_12_5]
      exact IsRegLang.union (derivative R1 [a]) (derivative R2 [a]) ih_3 ih_4
    case concat R1 R2 ih_1 ih_2 ih_3 ih_4 =>
      simp only [thm_12_7]
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
      simp only [thm_12_8]
      apply IsRegLang.concat
      · exact ih_2
      · exact IsRegLang.closure R' ih_1


theorem thm_17
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

      rw [thm_11_b]
      apply ih
      apply thm_17_aux
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
    exact thm_12_3 a

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

    simp only [thm_11_b]
    rw [thm_12_8]
    rw [thm_12_7]
    rw [thm_12_8]


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

    rw [thm_11_b]
    simp

    -----
    have s2 : [a1, a2] = [a1] ++ [a2] := rfl
    rw [s2]
    clear s2

    simp only [thm_11_b]
    rw [thm_12_8]
    rw [thm_12_7]
    rw [thm_12_8]
    -----

    rw [thm_12_5]
    simp only [thm_12_7]
    rw [thm_12_8]

    simp only [nullify_idempotent]
    simp only [derivative_of_nullify]
    simp only [concat_empty_left]
    simp
    simp only [← thm_11_b]
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

    simp only [thm_11_b]
    simp only [thm_12_8, thm_12_7, thm_12_5]
    simp only [nullify_idempotent]
    simp only [derivative_of_nullify]
    simp only [thm_12_1]
    simp only [concat_empty_left]
    simp
    simp only [nullify_empty]
    simp only [concat_empty_left]
    simp
    simp only [← thm_11_b]
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
    induction s generalizing L
    case nil =>
      simp at h1
    case cons hd tl ih =>
      have s1 : hd :: tl = [hd] ++ tl := rfl
      rw [s1]
      clear s1

      simp only [thm_11_b]
      simp
      simp only [thm_12_8]
      by_cases c1 : tl = []
      case pos =>
        subst c1
        simp
        apply Exists.intro [[hd]]
        simp
        rw [thm_11_a]
      case neg =>
        specialize ih L c1
        obtain ⟨T, ⟨a1, a2, a3⟩⟩ := ih
        sorry


theorem thm_18
  {α : Type}
  [DecidableEq α]
  (R : Language α)
  (h1: IsRegLang α R) :
  Finite { derivative R s | s : Str α } :=
  by
    sorry
