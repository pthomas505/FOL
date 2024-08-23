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
  [inst : DecidableEq α]
  (L : Language α)
  (hd : α)
  (tl : List α)
  (cs : Str α) :
  (∃ i,
      ((∃ t, t ++ i = tl) ∧ ¬i = [] ∧ [] ∈ derivative L (hd :: List.take (tl.length - i.length) tl)) ∧
        cs ∈ concat (derivative L i) (kleene_closure α L)) →
    ∃ t,
      (∃ u v, u ++ v = tl ∧ ¬v = [] ∧ t = concat (derivative L (hd :: u)).nullify (derivative (kleene_closure α L) v)) ∧
        cs ∈ t :=
  by
    intro a1
    obtain ⟨i, ⟨⟨u, a2⟩, a3, a4⟩, a5⟩ := a1
    rw [← a2] at a4
    simp at a4
    simp only [derivative] at a4
    simp at a4

    simp only [derivative] at a5
    simp only [concat] at a5
    simp at a5
    obtain ⟨s, a6, t, a7, a8⟩ := a5
    rw [← a8]

    apply Exists.intro (derivative (kleene_closure α L) i)
    constructor
    · apply Exists.intro u
      obtain s1 := str_mem_lang_iff_nullify_derivative_eq_eps L (hd :: u)
      simp only [a4] at s1
      simp at s1
      rw [s1]
      simp only [concat_eps_left]
      apply Exists.intro i
      constructor
      · exact a2
      · constructor
        · exact a3
        · rfl
    · simp only [derivative]
      simp
      rw [String.str_append_assoc]
      apply append_kleene_closure_closed
      · exact mem_language_mem_kleene_closure L (i ++ s) a6
      · exact a7


noncomputable def foo'
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (s : Str α) :
  List (List α) :=
  match s with
  | [] => []
  | hd :: tl =>
    open Classical in
    let l1 :=
      tl.tails.filter fun s => ¬ s = [] ∧ [] ∈ derivative L (hd :: tl.take (tl.length - s.length))
    have IH (v : List α) (h : v.IsSuffix tl) :=
      have : v.length ≤ tl.length := h.length_le
      foo' L v
    let l2 := l1.attach.bind fun ⟨v, h⟩ => by
      simp [l1, List.mem_filter] at h
      exact IH v h.1
    (hd :: tl) :: l2
termination_by s.length


lemma foo_proof
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (s : Str α)
  (h1 : ¬ s = []) :
  derivative (kleene_closure α L) s =
    ⋃ t ∈ foo' L s, concat (derivative L t) (kleene_closure α L) :=
  by
    cases e : s
    case nil =>
      contradiction
    case cons hd tl =>
      have IH : ∀ (v : List α), v.IsSuffix tl → ¬ v = [] → derivative (kleene_closure α L) v = ⋃ t ∈ foo' L v, concat (derivative L t) (kleene_closure α L) :=
      by
        intro v h
        have : v.length < s.length :=
        by
          rw [e]
          simp
          apply Nat.lt_succ_of_le
          exact List.IsSuffix.length_le h
        exact foo_proof L v

      rw [derivative_wrt_cons]
      simp only [derivative_of_kleene_closure_wrt_char]
      simp only [derivative_of_concat_wrt_str]
      simp only [← derivative_wrt_append]
      simp only [List.singleton_append]

      simp only [foo']

      simp
      congr! 1
      ext cs
      simp

      simp only [List.mem_filter]
      simp

      constructor
      · intro a1
        obtain ⟨M, ⟨u, v, a2, a3, a4⟩, a5⟩ := a1

        have s1 : v.IsSuffix tl :=
        by
          simp only [List.IsSuffix]
          apply Exists.intro u
          exact a2

        specialize IH v s1 a3

        rw [a4] at a5
        clear a4
        simp only [mem_concat_nullify_left_iff] at a5
        obtain ⟨a6, a7⟩ := a5

        apply Exists.intro v
        constructor
        · constructor
          · exact s1
          · constructor
            · exact a3
            · rw [← a2]
              simp
              exact a6
        · rw [IH] at a7
          simp at a7
          exact a7
      · intro a1
        obtain ⟨i, ⟨a2, a3, a4⟩, j, a5, a6⟩ := a1

        simp only [derivative] at a4
        simp at a4

        specialize IH i a2 a3
        have s1 : ∃ i_1 ∈ foo' L i, cs ∈ concat (derivative L i_1) (kleene_closure α L) :=
        by
          apply Exists.intro j
          tauto

        simp only [List.IsSuffix] at a2
        obtain ⟨t, ht⟩ := a2

        rw [← ht] at a4
        simp at a4

        apply Exists.intro (derivative (kleene_closure α L) i)

        constructor
        · apply Exists.intro t
          apply Exists.intro i
          constructor
          · exact ht
          · constructor
            · exact a3
            · simp only [Language.nullify]
              split_ifs
              case pos c1 =>
                simp only [concat_eps_left]
              case neg c1 =>
                simp only [derivative] at c1
                simp at c1
                contradiction
        · rw [IH]
          simp
          exact s1
termination_by s.length


theorem thm_18
  {α : Type}
  [DecidableEq α]
  (R : Language α)
  (h1: IsRegLang α R) :
  Finite { derivative R s | s : Str α } :=
  by
    sorry
