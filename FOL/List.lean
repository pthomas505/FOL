import Mathlib.Data.List.Basic
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


#lint
