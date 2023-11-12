import FOL.Tactics


theorem List.map_eq_self_iff
  {α : Type}
  {f : α → α}
  (l : List α) :
  List.map f l = l ↔
    ∀ x : α, x ∈ l → f x = x :=
  by
  induction l
  case nil =>
    simp
  case cons l_hd l_tl l_ih =>
    simp
    intro _
    exact l_ih


lemma List.map_mem_id
  {α : Type}
  (xs: List α)
  (f : α → α)
  (h1: ∀ (x : α), x ∈ xs → f x = x) :
  List.map f xs = xs :=
  by
  induction xs
  case nil =>
    simp
  case cons hd tl ih =>
    simp at h1
    cases h1
    case _ h1_left h1_right =>
      simp
      constructor
      · exact h1_left
      · exact ih h1_right


example
  {α β : Type}
  [DecidableEq α]
  [DecidableEq β]
  (f g : α → β)
  (a b : α)
  (h1 : Function.Injective f)
  (h2_left : g a = f b)
  (h2_right : g b = f a)
  (h3 : ∀ x : α, (¬ x = a ∧ ¬ x = b) → f x = g x) :
  Function.Injective g :=
  by
  unfold Function.Injective at h1

  unfold Function.Injective
  intro x1 x2 a1
  by_cases x1_a : x1 = a
  · by_cases x2_a : x2 = a
    · simp only [x1_a]
      simp only [x2_a]
    · by_cases x1_b : x1 = b
      · by_cases x2_b : x2 = b
        · simp only [x1_b]
          simp only [x2_b]
        · specialize h3 x2
          simp at h3
          specialize h3 x2_a x2_b
          simp only [<- a1] at h3
          simp only [x1_a] at h3
          simp only [h2_left] at h3
          specialize h1 h3
          contradiction
      · by_cases x2_b : x2 = b
        · subst x1_a
          subst x2_b
          apply h1
          simp only [<- h2_left]
          simp only [<- h2_right]
          simp only [a1]
        · specialize h3 x2 --
          simp at h3
          specialize h3 x2_a x2_b
          simp only [<- a1] at h3
          simp only [x1_a] at h3
          simp only [h2_left] at h3
          specialize h1 h3
          contradiction
  · by_cases x2_a : x2 = a
    · by_cases x1_b : x1 = b
      · subst x1_b
        subst x2_a
        apply h1
        simp only [<- h2_left]
        simp only [<- h2_right]
        simp only [a1]
      · by_cases x2_b : x2 = b
        · specialize h3 x1
          simp at h3
          specialize h3 x1_a x1_b
          simp only [a1] at h3
          simp only [x2_a] at h3
          simp only [h2_left] at h3
          simp only [← x2_b] at h3
          exact h1 h3
        · specialize h3 x1
          simp at h3
          specialize h3 x1_a x1_b
          simp only [a1] at h3
          simp only [x2_a] at h3
          simp only [h2_left] at h3
          specialize h1 h3
          contradiction
    · by_cases x1_b : x1 = b
      · by_cases x2_b : x2 = b
        · simp only [x1_b]
          simp only [x2_b]
        · specialize h3 x2
          simp at h3
          specialize h3 x2_a x2_b
          simp only [<- a1] at h3
          simp only [x1_b] at h3
          simp only [h2_right] at h3
          specialize h1 h3
          contradiction
      · by_cases x2_b : x2 = b
        · specialize h3 x1
          simp at h3
          specialize h3 x1_a x1_b
          simp only [a1] at h3
          simp only [x2_b] at h3
          simp only [h2_right] at h3
          specialize h1 h3
          contradiction
        · have s1 : ¬ x1 = a ∧ ¬ x1 = b
          constructor
          · exact x1_a
          · exact x1_b

          have s2 : ¬ x2 = a ∧ ¬ x2 = b
          constructor
          · exact x2_a
          · exact x2_b

          apply h1
          simp only [h3 x1 s1]
          simp only [h3 x2 s2]
          exact a1


/-
  have s1 : x1 = a := sorry
  have s2 : ¬ x2 = a := sorry
  have s3 : ¬ x2 = b := sorry
  specialize h3 x2
  simp at h3
  specialize h3 s2 s3
  simp only [<- a1] at h3
  simp only [s1] at h3
  simp only [h2_left] at h3
  specialize h1 h3
  contradiction
-/

/-
  have s1 : x1 = b := sorry
  have s2 : ¬ x2 = a := sorry
  have s3 : ¬ x2 = b := sorry
  specialize h3 x2
  simp at h3
  specialize h3 s2 s3
  simp only [<- a1] at h3
  simp only [s1] at h3
  simp only [h2_right] at h3
  specialize h1 h3
  contradiction
-/

/-
  have s1 : x1 = x2 := sorry
  exact s1
-/

/-
  have s1 : x1 = a := sorry
  have s2 : x2 = a := sorry
  simp only [s1]
  simp only [s2]
-/

/-
  have s1 : x1 = b := sorry
  have s2 : x2 = b := sorry
  simp only [s1]
  simp only [s2]
-/

/-
  have s1 : x1 = a := sorry
  have s2 : x2 = b := sorry
  subst s1
  subst s2
  apply h1
  simp only [<- h2_left]
  simp only [<- h2_right]
  simp only [a1]
-/

/-
  have s1 : x1 = b := sorry
  have s2 : x2 = a := sorry
  subst s1
  subst s2
  apply h1
  simp only [<- h2_left]
  simp only [<- h2_right]
  simp only [a1]
-/

/-
  have s1 : ¬ x1 = a ∧ ¬ x1 = b := sorry
  have s2 : ¬ x2 = a ∧ ¬ x2 = b := sorry
  apply h1
  simp only [h3 x1 s1]
  simp only [h3 x2 s2]
  exact a1
-/


theorem nodup_eq_len_imp_eqv
  {α : Type}
  [DecidableEq α]
  (xs ys : List α)
  (h1 : xs.length = ys.length)
  (h2 : xs.Nodup)
  (h3 : ys.Nodup) :
  ∃ f : α ≃ α, xs.map f = ys :=
  by
  induction xs generalizing ys
  case nil =>
    have s1 : ys = []
    {
      apply List.eq_nil_of_length_eq_zero
      simp only [← h1]
      simp
    }
    simp only [s1]
    apply Exists.intro Equiv.inhabited'.default
    simp
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp at h1
    case cons ys_hd ys_tl =>
      simp at h1
      simp at h2
      simp at h3

      cases h2
      case intro h2_left h2_right =>
        cases h3
        case intro h3_left h3_right =>
          simp
          specialize xs_ih ys_tl h1 h2_right h3_right

          apply Exists.elim xs_ih
          intro f a1
          clear xs_ih

          sorry


theorem list_zipWith_of_map
  {α β γ : Type}
  (l : List α)
  (f : α → β)
  (g : α → β → γ) :
  List.zipWith g l (List.map f l) =
    List.map (fun x : α => g x (f x)) l :=
  by
  induction l
  case nil =>
    simp
  case cons hd tl ih =>
    simp
    exact ih


--#lint
