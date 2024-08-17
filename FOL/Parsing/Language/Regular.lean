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
    have IH (v) (h : List.IsSuffix v tl) :=
      have := h.length_le
      foo' L v
    let l2 := l1.attach.bind fun ⟨v, h⟩ => by
      simp [l1, List.mem_filter] at h
      exact IH v h.1
    (hd :: tl) :: l2
termination_by s.length


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
    cases s
    case nil =>
      simp at h1
    case cons hd tl =>
      rw [← List.singleton_append]
      simp only [derivative_wrt_append]
      simp only [derivative_of_kleene_closure_wrt_char]
      simp only [derivative_of_concat_wrt_str]
      simp only [← derivative_wrt_append]
      simp only [List.singleton_append]
      simp
      apply Exists.intro ((hd :: tl) :: tl.tails.filter (open Classical in fun s => ¬ s = [] ∧ [] ∈ derivative L (hd :: tl.take (tl.length - s.length))))
      constructor
      · simp [List.subset_def, List.mem_filter]; aesop
      · constructor
        · simp [List.mem_filter]
        · simp
          congr 1
          ext cs
          simp only [List.mem_filter]
          simp
          simp only [List.IsSuffix]
          constructor
          · intro a1
            obtain ⟨M, ⟨u, v, a2, a3, a4⟩ , a5⟩ := a1
            rw [← a2]
            clear a2
            rw [a4] at a5
            clear a4
            simp only [derivative] at a5
            simp at a5
            simp only [Language.nullify] at a5
            simp at a5
            simp only [concat] at a5
            simp at a5
            obtain ⟨s, ⟨a6, a7⟩, t, a8, a9⟩ := a5
            rw [← a9]
            clear a9
            simp only [a7]
            clear a7
            simp

            simp only [derivative]
            simp
            simp only [concat]
            simp
            rw [kleene_closure_eq_eps_union_concat_language_kleene_closure] at a8
            simp at a8
            cases a8
            case _ c1 =>
              tauto
            case _ c1 =>
              simp only [concat] at c1
              simp at c1
              obtain ⟨a, a9, c, a10, a11⟩ := c1
              simp only [List.append_eq_append_iff] at a11
              cases a11
              case _ c2 =>
                obtain ⟨a', a12, a13⟩ := c2
                rw [a12]
                simp
                sorry
              case _ c2 =>
                obtain ⟨c', a14, a15⟩ := c2
                apply Exists.intro v
                simp
                constructor
                · tauto
                · apply Exists.intro c'
                  rw [← a14]
                  constructor
                  · exact a9
                  · apply Exists.intro c
                    tauto
          · intro a1
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


noncomputable def foo
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (s : Str α)
  (h1 : ¬ s = []) :
  { T : List (List α) // T ⊆ s.tails ∧ [] ∉ T ∧
    derivative (kleene_closure α L) s =
    ⋃ t ∈ T, concat (derivative L t) (kleene_closure α L) } :=
  by
    let hd :: tl := s
    rw [← List.singleton_append]
    simp only [derivative_wrt_append]
    simp only [derivative_of_kleene_closure_wrt_char]
    simp only [derivative_of_concat_wrt_str]
    simp only [← derivative_wrt_append]
    simp only [List.singleton_append]
    simp only [List.tails, gt_iff_lt, List.length_pos, ne_eq]
    open Classical in
      let l1 :=
        tl.tails.filter fun s => ¬ s = [] ∧ [] ∈ derivative L (hd :: tl.take (tl.length - s.length))
    have IH (v) (h : List.IsSuffix v tl) :=
      have := h.length_le
      foo L v
    let l2 := l1.attach.bind fun ⟨v, h⟩ => by
      simp [l1, List.mem_filter] at h
      exact (IH v h.1 h.2.1).1
    refine ⟨(hd :: tl) :: l2, ?_, ?_, ?_⟩
    · simp [l2, l1, List.subset_def, List.mem_filter]
      intro _ _ ⟨a1, _⟩ a2
      have := (IH _ _ _).2.1 a2
      simp at this
      exact .inr (this.trans a1)
    · simp [List.mem_filter, l2, l1]
      intro _ _ a2
      exact (IH _ _ _).2.2.1 a2
    · simp
      congr 1
      ext cs
      simp only [Set.mem_sUnion, Set.mem_setOf_eq, List.mem_bind, List.mem_attach, true_and,
        Subtype.exists, List.mem_filter, List.mem_tails, List.IsSuffix, decide_eq_true_eq,
        Set.iUnion_exists, eq_mp_eq_cast, Set.biUnion_and', Set.biUnion_and, Set.mem_iUnion,
        exists_prop, exists_and_right, l2, l1]
      have H1 {u v} (H : u ++ v = tl) : List.take (tl.length - v.length) tl = u := H ▸ by simp
      have H2 {X Y : Language α} {s : Str α} : s ∈ concat X.nullify Y ↔ [] ∈ X ∧ s ∈ Y := by
        simp [concat, Language.nullify]
        aesop
      constructor
      · rintro ⟨M, ⟨u, v, rfl, a1, rfl⟩, a5⟩
        have ⟨a6, a7⟩ := H2.1 a5
        simp [(IH _ ⟨_, rfl⟩ a1).2.2.2] at a7
        obtain ⟨w, c1, c2⟩ := a7
        refine ⟨_, _, ⟨a1, _, rfl, ?_, c1⟩, c2⟩
        simp [a6]
      · rintro ⟨v, w, ⟨a1, a2, rfl, a3, a4⟩, a5⟩
        simp at a3
        refine ⟨_, ⟨_, _, rfl, a1, rfl⟩, ?_⟩
        rw [H2]
        refine ⟨a3, ?_⟩
        simp [(IH _ ⟨_, rfl⟩ a1).2.2.2]
        refine ⟨_, a4, a5⟩
termination_by s.length


theorem thm_18
  {α : Type}
  [DecidableEq α]
  (R : Language α)
  (h1: IsRegLang α R) :
  Finite { derivative R s | s : Str α } :=
  by
    sorry
