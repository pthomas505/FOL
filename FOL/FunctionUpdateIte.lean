import Std.Tactic.Lint.Frontend
import Mathlib.Tactic

import FOL.Tactics


/--
  Specialized version of Function.update for non-dependent functions.
  Function.updateIte f a' b := Replaces the value of f at a' by b.
-/
def Function.updateIte
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (a' : α)
  (b : β)
  (a : α) :
  β :=
  if a = a' then b else f a

#eval Function.updateIte (fun n : ℕ => n) 5 10 1
#eval Function.updateIte (fun n : ℕ => n) 5 10 5


/--
  Function.updateIte at multiple points.
  Function.updateListIte f xs ys := Replaces the value of f at each point in xs by the value in ys at the same index.
  If there are duplicate values in xs then the value at the smallest index is used.
  If the lengths of xs and ys do not match then the longer is effectively truncated to the length of the smaller.
-/
def Function.updateListIte
  {α β : Type}
  [DecidableEq α]
  (f : α → β) :
  List α → List β → α → β
  | x::xs, y::ys => Function.updateIte (Function.updateListIte f xs ys) x y
  | _, _ => f

#eval Function.updateListIte (fun n : ℕ => n) [5, 10, 5] [10, 20, 30] 5
#eval Function.updateListIte (fun n : ℕ => n) [5, 10] [10] 5
#eval Function.updateListIte (fun n : ℕ => n) [10] [5, 10] 10
#eval Function.updateListIte (fun n : ℕ => n) [] [5, 10] 10
#eval Function.updateListIte (fun n : ℕ => n) [5, 10] [] 5


/-
def Function.updateListIte'
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (xs : List α)
  (ys : List β) :
  α → β :=
  List.foldr (fun (p : α × β) (_ : α → β) => Function.updateIte f p.fst p.snd) f (List.zip xs ys)

#eval Function.updateListIte' (fun n : ℕ => n) [0, 3, 0] [10, 2, 2] 0
-/


lemma Function.left_id_left_inverse
  {α β : Type}
  (f : α → β)
  (g : β → α)
  (h1 : g ∘ f = id) :
  Function.LeftInverse g f :=
  by
  unfold Function.LeftInverse
  intro x
  exact congrFun h1 x


lemma Function.right_id_right_inverse
  {α β : Type}
  (f : α → β)
  (g : β → α)
  (h1 : f ∘ g = id) :
  Function.RightInverse g f :=
  by
  unfold Function.RightInverse
  exact Function.left_id_left_inverse g f h1


-- Function.updateIte


theorem Function.updateIte_comp_left
  {α β γ : Type}
  [DecidableEq α]
  (f : β → γ)
  (g : α → β)
  (a : α)
  (b : β) :
  f ∘ (Function.updateIte g a b) =
    Function.updateIte (f ∘ g) a (f b) :=
  by
  funext x
  unfold Function.updateIte
  simp
  split_ifs
  · rfl
  · rfl


theorem Function.updateIte_comp_right
  {α β γ : Type}
  [DecidableEq α]
  [DecidableEq β]
  (f : α → β)
  (finv : β → α)
  (g : β → γ)
  (a : β)
  (b : γ)
  (h1 : finv ∘ f = id)
  (h2 : f ∘ finv = id) :
  (Function.updateIte g a b) ∘ f =
    Function.updateIte (g ∘ f) (finv a) b :=
  by
  funext x
  unfold Function.updateIte
  simp
  congr!
  constructor
  · intro a1
    simp only [← a1]
    obtain s1 := Function.left_id_left_inverse f finv h1
    unfold Function.LeftInverse at s1
    simp only [s1 x]
  · intro a1
    simp only [a1]
    obtain s1 := Function.right_id_right_inverse f finv h2
    unfold Function.RightInverse at s1
    unfold Function.LeftInverse at s1
    exact s1 a


theorem Function.updateIte_comp_right_injective
  {α β γ : Type}
  [DecidableEq α]
  [DecidableEq β]
  (f : α → β)
  (g : β → γ)
  (a : α)
  (b : γ)
  (h1 : Function.Injective f) :
  (Function.updateIte g (f a) b) ∘ f =
    Function.updateIte (g ∘ f) a b :=
  by
  unfold Function.Injective at h1

  funext x
  unfold Function.updateIte
  simp
  congr!
  constructor
  · apply h1
  · intro a1
    subst a1
    rfl


theorem Function.updateIte_comm
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (a b : α)
  (u v : β)
  (h1 : ¬ a = b) :
  Function.updateIte (Function.updateIte f a v) b u =
    Function.updateIte (Function.updateIte f b u) a v :=
  by
  funext x
  unfold Function.updateIte
  split_ifs
  case _ c1 c2 =>
    subst c1 c2
    contradiction
  case _ | _ | _ =>
    rfl


theorem Function.updateIte_idem
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (a : α)
  (x y : β) :
  Function.updateIte (Function.updateIte f a x) a y =
    Function.updateIte f a y :=
  by
  funext v
  unfold Function.updateIte
  split_ifs
  · rfl
  · rfl


theorem Function.updateIte_id
  {α : Type}
  [DecidableEq α]
  (x : α) :
  Function.updateIte (id : α → α) x x = id :=
  by
  funext v
  unfold Function.updateIte
  split_ifs
  case _ c1 =>
    subst c1
    simp
  case _ =>
    rfl


theorem Function.updateIte_comm_id
  {α : Type}
  [DecidableEq α]
  (x a b : α)
  (h1 : ¬ x = a) :
  Function.updateIte (Function.updateIte id a b) x x =
    Function.updateIte id a b :=
  by
  funext y
  unfold Function.updateIte
  simp
  intro a1
  subst a1
  simp only [if_neg h1]


theorem Function.updateIte_coincide
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (x : α)
  (h1 : ∀ y : α, ¬ y = x → f y = g y) :
  Function.updateIte f x (g x) = g :=
  by
  funext y
  unfold Function.updateIte
  split_ifs
  case _ c1 =>
    subst c1
    rfl
  case _ c1 =>
    exact h1 y c1


theorem Function.updateIte_not_mem_list
  {α β : Type}
  [DecidableEq α]
  (l : List α)
  (f : α → β)
  (a : α)
  (b : β)
  (h1 : a ∉ l) :
  l.map (Function.updateIte f a b) = l.map f :=
  by
  induction l
  case nil =>
    simp
  case cons l_hd l_tl l_ih =>
    simp at h1
    push_neg at h1

    cases h1
    case intro h1_left h1_right =>
      simp
      unfold Function.updateIte
      split_ifs <;> tauto


theorem Function.updateIte_not_mem_set
  {α β : Type}
  [DecidableEq α]
  [DecidableEq β]
  (S : Finset α)
  (f : α → β)
  (a : α)
  (b : β)
  (h1 : a ∉ S) :
  Finset.image (Function.updateIte f a b) S =
    Finset.image f S :=
  by
  induction S using Finset.induction_on
  case empty =>
    simp
  case insert S_a S_S _ S_ih =>
    simp at h1
    push_neg at h1

    cases h1
    case intro h1_left h1_right =>
    simp
    congr! 1
    · unfold Function.updateIte
      split_ifs
      case _ c1 =>
        subst c1
        contradiction
      case _ c1 =>
        rfl
    · exact S_ih h1_right


theorem Function.updateIte_symm
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (x y : α)
  (d d' : β)
  (h1 : ¬ x = y) :
  Function.updateIte (Function.updateIte f x d) y d' =
    Function.updateIte (Function.updateIte f y d') x d :=
  by
  funext a
  unfold Function.updateIte
  by_cases c1 : a = x
  · by_cases c2 : a = y
    · subst c1
      subst c2
      contradiction
    · subst c1
      simp
      intro a1
      contradiction
  · by_cases c2 : a = y
    · subst c2
      simp
      simp only [if_neg c1]
    · simp only [if_neg c1]


-- Function.updateListIte

theorem Function.updateListIte_comp
  {α β γ : Type}
  [DecidableEq α]
  (f : α → β)
  (g : β → γ)
  (xs : List α)
  (ys : List β) :
  g ∘ Function.updateListIte f xs ys =
    Function.updateListIte (g ∘ f) xs (ys.map g) :=
  by
  induction xs generalizing ys
  case nil =>
    unfold Function.updateListIte
    rfl
  case cons _ xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp
      unfold Function.updateListIte
      rfl
    case cons ys_hd ys_tl =>
      simp
      unfold Function.updateListIte
      simp only [← xs_ih]
      apply Function.updateIte_comp_left


theorem Function.updateListIte_mem'
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (xs ys : List α)
  (x : α)
  (h1 : f x = g x) :
  Function.updateListIte f xs (List.map f ys) x =
    Function.updateListIte g xs (List.map f ys) x :=
  by
  induction xs generalizing ys
  case nil =>
    unfold Function.updateListIte
    exact h1
  case cons _ xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp
      unfold Function.updateListIte
      exact h1
    case cons ys_hd ys_tl =>
      simp
      unfold Function.updateListIte
      unfold Function.updateIte
      split_ifs
      · rfl
      · exact xs_ih ys_tl


theorem Function.updateListIte_mem_eq_len
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (v : α)
  (xs : List α)
  (ys : List β)
  (h1 : v ∈ xs)
  (h2 : xs.length = ys.length) :
  Function.updateListIte f xs ys v =
    Function.updateListIte g xs ys v :=
  by
  induction xs generalizing ys
  case nil =>
    contradiction
  case cons xs_hd xs_tl xs_ih =>
    simp at h1

    cases ys
    case nil =>
      contradiction
    case cons ys_hd ys_tl =>
      unfold Function.updateListIte
      unfold Function.updateIte
      cases h1
      case inl h1 =>
        simp only [if_pos h1]
      case inr h1 =>
        split_ifs
        case inl =>
          rfl
        case inr c1 =>
          simp at h2
          exact xs_ih ys_tl h1 h2


theorem Function.updateListIte_mem
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (v : α)
  (xs : List α)
  (ys : List β)
  (h1 : v ∈ xs)
  (h2 : f v = g v) :
  Function.updateListIte f xs ys v =
    Function.updateListIte g xs ys v :=
  by
  induction xs generalizing ys
  case nil =>
    contradiction
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp at h1

      unfold Function.updateListIte
      exact h2
    case cons ys_hd ys_tl =>
      simp at h1

      unfold Function.updateListIte
      unfold Function.updateIte
      split_ifs
      case inl =>
        rfl
      case inr c1 =>
        cases h1
        case inl c2 =>
          contradiction
        case inr c2 =>
          exact xs_ih ys_tl c2


theorem Function.updateListIte_not_mem
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (v : α)
  (xs : List α)
  (ys : List β)
  (h1 : v ∉ xs) :
  Function.updateListIte f xs ys v = f v :=
  by
  induction xs generalizing ys
  case nil =>
    unfold Function.updateListIte
    rfl
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      unfold Function.updateListIte
      rfl
    case cons ys_hd ys_tl =>
      unfold Function.updateListIte
      unfold Function.updateIte
      split_ifs
      case inl c1 =>
        subst c1
        simp at h1
      case inr c1 =>
        simp at h1
        push_neg at h1
        cases h1
        case intro h1_left h1_right =>
          apply xs_ih ys_tl h1_right


theorem Function.updateListIte_updateIte
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (l1 : List α)
  (l2 : List β)
  (x y : α)
  (z : β)
  (h1 : ¬ x = y) :
  Function.updateListIte (Function.updateIte f y z) l1 l2 x =
    Function.updateListIte f l1 l2 x :=
  by
  induction l1 generalizing l2
  case nil =>
    unfold Function.updateListIte
    unfold Function.updateIte
    simp only [if_neg h1]
  case cons l1_hd l1_tl l1_ih =>
    cases l2
    case nil =>
      unfold Function.updateListIte
      unfold Function.updateIte
      simp only [if_neg h1]
    case cons l2_hd l2_tl =>
      unfold Function.updateListIte
      unfold Function.updateIte
      split_ifs
      case inl c1 =>
        rfl
      case inr c1 =>
        apply l1_ih


theorem Function.updateListIte_fun_coincide_mem_eq_len
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (xs ys : List α)
  (x : α)
  (h1 : ∀ (v : α), v ∈ ys → f v = g v)
  (h2 : x ∈ xs)
  (h3 : xs.length = ys.length):
  Function.updateListIte f xs (List.map f ys) x =
    Function.updateListIte g xs (List.map g ys) x :=
  by
  have s1 : List.map f ys = List.map g ys
  simp only [List.map_eq_map_iff]
  exact h1

  simp only [s1]
  apply Function.updateListIte_mem_eq_len
  · exact h2
  · simp
    exact h3


#lint
