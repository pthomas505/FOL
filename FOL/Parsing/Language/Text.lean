import FOL.Parsing.Language.Derivative


set_option autoImplicit false


-- https://arxiv.org/pdf/1907.13577


-------------------------------------------------------------------------------

namespace Languages



-------------------------------------------------------------------------------







/-
Definition 16 (Distinguishing extension). Let L ⊆ Σ∗ be a language, and
s, t ∈ Σ∗ strings. A distinguishing extension is a string u ∈ Σ∗ such that
either su ∈ L or tu ∈ L, but not both.
-/
def is_dist_ext
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (u : Str α) :
  Prop :=
  (s ++ u ∈ L ∧ t ++ u ∉ L) ∨ (s ++ u ∉ L ∧ t ++ u ∈ L)


/-
Definition 17. Define the relation ≡L, “L-equivalent”, or “equivalent with
respect to L”, on strings by the rule
s ≡L t ⇔ {u : su ∈ L} = {u : tu ∈ L} , (1.66)
i.e. s ≡L t if there is no distinguishing extension for s and t.
-/
def L_equiv
  {α : Type}
  (L : Language α)
  (s t : Str α) :
  Prop :=
  {u | s ++ u ∈ L} = {u | t ++ u ∈ L}


lemma L_equiv_iff_deriv_eq
  {α : Type}
  (L : Language α)
  (s t : Str α) :
  L_equiv L s t ↔ derivative L s = derivative L t :=
  by
    rfl


theorem thm_15_refl
  {α : Type}
  (L : Language α)
  (s : Str α) :
  L_equiv L s s :=
  by
    rfl


theorem thm_15_symm
  {α : Type}
  (L : Language α)
  (s t : Str α) :
  L_equiv L s t → L_equiv L t s :=
  by
    simp only [L_equiv]
    intro a1
    symm
    exact a1


theorem thm_15_trans
  {α : Type}
  (L : Language α)
  (r s t : Str α)
  (h1 : L_equiv L r s)
  (h2 : L_equiv L s t) :
  L_equiv L r t :=
  by
    simp only [L_equiv] at *
    trans {u | s ++ u ∈ L}
    · exact h1
    · exact h2


instance (α : Type) (L : Language α) : IsEquiv (Str α) (L_equiv L) :=
  {
    symm := thm_15_symm L
    refl := thm_15_refl L
    trans := thm_15_trans L
  }

theorem L_equivalence
  {α : Type}
  (L : Language α) :
  Equivalence (L_equiv L) :=
  ⟨ thm_15_refl L, thm_15_symm L _ _, thm_15_trans L _ _ _ ⟩


def Str.equiv_class
  {α : Type}
  (L : Language α)
  (s : Str α) :
  Set (Str α) :=
  {t | L_equiv L s t}


example
  {α : Type}
  (L : Language α)
  (s : Str α) :
  Str.equiv_class L s = { t | derivative L s = derivative L t } :=
  by
    rfl


example
  {α : Type}
  (L : Language α)
  (a : α) :
  Str.equiv_class L [a] ∩ {s : Str α | s.length = 1} =
    { b | derivative L [a] = derivative L b ∧ b.length = 1 } :=
  by
    rfl


theorem thm_16_2
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (s t : Str α)
  (h1 : L_equiv L1 s t)
  (h2 : L_equiv L2 s t) :
  L_equiv (L1 ∪ L2) s t :=
  by
    simp only [L_equiv_iff_deriv_eq] at *
    rw [thm_12_5_str L1 L2 s]
    rw [thm_12_5_str L1 L2 t]
    rw [h1]
    rw [h2]


theorem thm_16_3
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α)
  (s t : Str α)
  (h1 : L_equiv L1 s t)
  (h2 : L_equiv L2 s t) :
  L_equiv (L1 ∩ L2) s t :=
  by
    simp only [L_equiv_iff_deriv_eq] at *
    rw [thm_12_6_str L1 L2 s]
    rw [thm_12_6_str L1 L2 t]
    rw [h1]
    rw [h2]


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
