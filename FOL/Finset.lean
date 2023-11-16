import FOL.Tactics

set_option autoImplicit false


lemma Finset.union_subset_left_right
  {α : Type}
  [DecidableEq α]
  (A B C D : Finset α)
  (h1 : A ⊆ C)
  (h2 : B ⊆ D) :
  A ∪ B ⊆ C ∪ D :=
  by
    apply Finset.union_subset_iff.mpr
    constructor
    · trans C
      · exact h1
      · exact Finset.subset_union_left C D
    · trans D
      · exact h2
      · exact Finset.subset_union_right C D


lemma Finset.union_subset_union_left_right
  {α : Type}
  [DecidableEq α]
  (A B C D E : Finset α)
  (h1 : A ⊆ C ∪ E)
  (h2 : B ⊆ D ∪ E) :
  A ∪ B ⊆ C ∪ D ∪ E :=
  by
  apply Finset.union_subset_iff.mpr
  constructor
  · trans C ∪ E
    · exact h1
    · apply Finset.union_subset_union_left
      exact Finset.subset_union_left C D
  · trans D ∪ E
    · exact h2
    · apply Finset.union_subset_union_left
      exact Finset.subset_union_right C D


lemma Finset.union_subset_diff
  {α : Type}
  [DecidableEq α]
  (A B C D E : Finset α)
  (h1 : A ⊆ C \ E)
  (h2 : B ⊆ D \ E) :
  A ∪ B ⊆ (C ∪ D) \ E :=
  by
  apply Finset.union_subset_iff.mpr
  constructor
  · trans C \ E
    · exact h1
    · apply Finset.sdiff_subset_sdiff
      · exact Finset.subset_union_left C D
      · rfl
  · trans D \ E
    · exact h2
    · apply Finset.sdiff_subset_sdiff
      · exact Finset.subset_union_right C D
      · rfl


lemma Finset.union_subset_left_right_diff
  {α : Type}
  [DecidableEq α]
  (A B C D E F : Finset α)
  (h1 : A ⊆ E ∪ C \ F)
  (h2 : B ⊆ E ∪ D \ F) :
  A ∪ B ⊆ E ∪ (C ∪ D) \ F :=
  by
  apply Finset.union_subset_iff.mpr
  constructor
  · trans E ∪ C \ F
    · exact h1
    · apply Finset.union_subset_union_right
      apply Finset.sdiff_subset_sdiff
      · exact Finset.subset_union_left C D
      · rfl
  · trans E ∪ D \ F
    · exact h2
    · apply Finset.union_subset_union_right
      apply Finset.sdiff_subset_sdiff
      · exact Finset.subset_union_right C D
      · rfl


lemma Finset.diff_union_subset
  {α : Type}
  [DecidableEq α]
  (A B C D E : Finset α)
  (h1 : A \ E ⊆ C)
  (h2 : B \ E ⊆ D) :
  (A ∪ B) \ E ⊆ C ∪ D :=
  by
  have s1 : (A ∪ B) \ E = (A \ E) ∪ (B \ E)
  exact Finset.union_sdiff_distrib A B E
  trans (A \ E) ∪ (B \ E)
  · simp only [s1]
    rfl
  · exact Finset.union_subset_left_right (A \ E) (B \ E) C D h1 h2


#lint
