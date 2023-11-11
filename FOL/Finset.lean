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


#lint
