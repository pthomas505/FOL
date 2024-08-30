import FOL.Parsing.Language.Equiv

import Mathlib.Data.Finset.NAry

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


lemma blah
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (M : List (Str α))
  (f : Str α -> Language α):
  ⋃ s ∈ M, concat (f s) L = concat (⋃ s ∈ M, (f s)) L :=
  by
    simp only [concat]
    simp
    ext cs
    simp
    constructor
    · intro a1
      obtain ⟨i, hi, s, hs, t, ht, eq⟩ := a1
      rw [← eq]
      exact ⟨s, ⟨i, hi, hs⟩, t, ht, rfl⟩
    · intro a1
      obtain ⟨s, ⟨i, hi, hs⟩, t, ht, eq⟩ := a1
      rw [← eq]
      exact ⟨i, hi, s, hs, t, ht, rfl⟩


theorem thm_18
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (h1: IsRegLang α L) :
  ∃ T : Finset (Language α), ∀ s, derivative L s ∈ T :=
  by
    open Classical in
    induction h1
    case char c =>
      apply Exists.intro {{}, {[]}, {[c]}}
      intro s
      cases s
      case nil =>
        rw [derivative_wrt_eps]
        apply Finset.mem_insert_of_mem
        apply Finset.mem_insert_of_mem
        simp only [Finset.mem_singleton]
      case cons hd tl =>
        cases tl
        case nil =>
          by_cases c1 : hd = c
          case pos =>
            rw [c1]
            simp only [derivative_of_char_wrt_same_char c]
            apply Finset.mem_insert_of_mem
            exact Finset.mem_insert_self {[]} {{[c]}}
          case neg =>
            simp only [derivative_of_char_wrt_diff_char hd c c1]
            exact Finset.mem_insert_self ∅ {{[]}, {[c]}}
        case cons tl_hd tl_tl =>
          simp only [derivative]
          simp
    case epsilon =>
      apply Exists.intro {∅, {[]}}
      intro s
      cases s
      case nil =>
        simp only [derivative_wrt_eps]
        apply Finset.mem_insert_of_mem
        simp only [Finset.mem_singleton]
      case cons hd tl =>
        rw [derivative_wrt_cons]
        simp only [derivative_of_eps_wrt_char]
        simp only [derivative_of_empty_wrt_str]
        exact Finset.mem_insert_self ∅ {{[]}}
    case zero =>
      apply Exists.intro {∅}
      intro s
      simp only [derivative_of_empty_wrt_str]
      simp only [Finset.mem_singleton]
    case union L1 L2 L1_ih1 L2_ih1 L1_ih2 L2_ih2 =>
      simp only [derivative_of_union_wrt_str]

      obtain ⟨T1, a1⟩ := L1_ih2
      obtain ⟨T2, a2⟩ := L2_ih2
      apply Exists.intro (T1.biUnion (fun a => T2.biUnion (fun b => {a ∪ b})))
      simp
      intro s
      apply Exists.intro (derivative L1 s)
      constructor
      · apply a1
      · apply Exists.intro (derivative L2 s)
        constructor
        · apply a2
        . rfl
    case concat L1 L2 L1_ih1 L2_ih1 L1_ih2 L2_ih2 =>
      simp only [derivative_of_concat_wrt_str]

      obtain ⟨T1, a1⟩ := L1_ih2
      obtain ⟨T2, a2⟩ := L2_ih2

      let A : Finset (Language α) := {L2}
      let B : Finset (Language α) := T1.biUnion (fun a => A.biUnion (fun b => {concat a b}))
      let C : Finset (Language α) := (T1.biUnion (fun a => T2.biUnion (fun b => {concat a.nullify b} )) : Finset (Language α))

      have s3 : ∀ s, {M | ∃ u v, u ++ v = s ∧ List.length v > 0 ∧ M = concat (derivative L1 u).nullify (derivative L2 v)} ⊆ C :=
      by
        intro s
        simp only [C]
        simp only [Set.subset_def]
        intro X a3
        simp at a3
        simp
        obtain ⟨u, v, a4, a5, a6⟩ := a3
        apply Exists.intro (derivative L1 u)
        constructor
        · apply a1
        · apply Exists.intro (derivative L2 v)
          constructor
          · apply a2
          · exact a6

      have s4 : ∀ s, Finite {M | ∃ u v, u ++ v = s ∧ List.length v > 0 ∧ M = concat (derivative L1 u).nullify (derivative L2 v)} :=
      by
        intro s
        apply Set.Finite.subset
        · exact Finite.of_fintype { x // x ∈ C }
        · exact s3 s

      let D := C.powerset.image fun x => x.toSet.sUnion

      let T := (B.biUnion (fun a => D.biUnion (fun b => {a ∪ b})))

      apply Exists.intro T
      intro s
      simp only [T]
      simp only [B]
      simp only [D]
      simp only [A]
      simp

      apply Exists.intro (concat (derivative L1 s) L2)
      constructor
      · apply Exists.intro (derivative L1 s)
        constructor
        · apply a1
        · rfl
      · apply Exists.intro ({M | ∃ u v, u ++ v = s ∧ v.length > 0 ∧ M = concat (derivative L1 u).nullify (derivative L2 v)}).toFinite.toFinset
        constructor
        · exact Set.Finite.toFinset_subset.mpr (s3 s)
        · simp
    case kleene_closure L1 L1_ih1 L1_ih2 =>
      obtain ⟨T, a1⟩ := L1_ih2

      have s1 : ∀ (s : Str α), {M | ∃ s_1 ∈ foo' L1 s, derivative L1 s_1 = M} ⊆ T :=
      by
        intro s
        apply Set.setOf_subset.mpr
        simp
        intro a a2
        apply a1

      have s2 : ∀ (s : Str α), Finite {M | ∃ s_1 ∈ foo' L1 s, derivative L1 s_1 = M} :=
      by
        intro s
        simp
        apply Set.Finite.subset _ (s1 s)
        simp

      have s4 : ∀ (s : Str α), (⋃ s_1 ∈ foo' L1 s, derivative L1 s_1) = ⋃₀ {M | ∃ s_1 ∈ foo' L1 s, derivative L1 s_1 = M} :=
      by
        intro s
        ext cs
        simp

      have s5 : ∃ (S : Finset (Language α)), ∀ (s : Str α), (⋃ s_1 ∈ foo' L1 s, derivative L1 s_1) ∈ S :=
      by
        simp only [s4]
        apply Exists.intro (T.powerset.image (fun x => x.toSet.sUnion))
        intro s
        simp
        apply Exists.intro ({M | ∃ s_1 ∈ foo' L1 s, derivative L1 s_1 = M}.toFinite.toFinset)
        simp
        apply s1

      obtain ⟨S, a2⟩ := s5

      let A : Finset (Language α) := {kleene_closure α L1} ∪ S.biUnion (fun a => {concat a (kleene_closure α L1)})

      apply Exists.intro A
      intro s
      by_cases c1 : s = []
      case pos =>
        simp only [A]
        simp only [c1]
        simp only [derivative_wrt_eps]
        simp
      case neg =>
        obtain s1 := derivative_of_kleene_closure_wrt_str L1 s c1
        rw [s1]
        clear s1
        rw [blah]
        simp only [A]
        simp
        right
        apply Exists.intro (⋃ s_1 ∈ foo' L1 s, derivative L1 s_1)
        tauto
