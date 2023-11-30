import Std.Tactic.Lint.Frontend
import Mathlib.Tactic

import FOL.Tactics


/--
  Specialized version of Function.update for non-dependent functions.
  Function.updateITE f a b := Replaces the value of f at a by b.
-/
def Function.updateITE
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (a : α)
  (b : β)
  (c : α) :
  β :=
  if c = a then b else f c

#eval Function.updateITE (fun n : ℕ => n) 5 10 1
#eval Function.updateITE (fun n : ℕ => n) 5 10 5


/--
  Symmetric equality version of Function.updateITE.
-/
def Function.updateITE'
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (a : α)
  (b : β)
  (c : α) :
  β :=
  if a = c then b else f c


/--
  Function.updateITE at multiple points.
  Function.updateListITE f xs ys := Replaces the value of f at each point in xs by the value in ys at the same index.
  If there are duplicate values in xs then the value at the smallest index is used.
  If the lengths of xs and ys do not match then the longer is effectively truncated to the length of the smaller.
-/
def Function.updateListITE
  {α β : Type}
  [DecidableEq α]
  (f : α → β) :
  List α → List β → α → β
  | x::xs, y::ys => Function.updateITE (Function.updateListITE f xs ys) x y
  | _, _ => f

#eval Function.updateListITE (fun n : ℕ => n) [5, 10, 5] [10, 20, 30] 5
#eval Function.updateListITE (fun n : ℕ => n) [5, 10] [10] 5
#eval Function.updateListITE (fun n : ℕ => n) [10] [5, 10] 10
#eval Function.updateListITE (fun n : ℕ => n) [] [5, 10] 10
#eval Function.updateListITE (fun n : ℕ => n) [5, 10] [] 5


/-
def Function.updateListITE'
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (xs : List α)
  (ys : List β) :
  α → β :=
  List.foldr (fun (p : α × β) (_ : α → β) => Function.updateITE f p.fst p.snd) f (List.zip xs ys)

#eval Function.updateListITE' (fun n : ℕ => n) [0, 3, 0] [10, 2, 2] 0
-/


lemma Function.left_id_left_inverse
  {α β : Type}
  (f : α → β)
  (g : β → α)
  (h1 : g ∘ f = id) :
  Function.LeftInverse g f :=
  by
  simp only [Function.LeftInverse]
  intro x
  exact congrFun h1 x


lemma Function.right_id_right_inverse
  {α β : Type}
  (f : α → β)
  (g : β → α)
  (h1 : f ∘ g = id) :
  Function.RightInverse g f :=
  by
  simp only [Function.RightInverse]
  exact Function.left_id_left_inverse g f h1


-- Function.updateITE

lemma Function.updateITE_eq_Function.updateITE'
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (a' : α)
  (b : β) :
  Function.updateITE f a' b = Function.updateITE' f a' b :=
  by
  simp only [Function.updateITE]
  simp only [Function.updateITE']
  funext a
  split_ifs
  case _ c1 c2 =>
    rfl
  case _ c1 c2 =>
    subst c1
    contradiction
  case _ c1 c2 =>
    subst c2
    contradiction
  case _ c1 c2 =>
    rfl


theorem Function.updateITE_comp_left
  {α β γ : Type}
  [DecidableEq α]
  (f : β → γ)
  (g : α → β)
  (a : α)
  (b : β) :
  f ∘ (Function.updateITE g a b) =
    Function.updateITE (f ∘ g) a (f b) :=
  by
  funext x
  simp only [Function.updateITE]
  simp
  split_ifs
  · rfl
  · rfl


theorem Function.updateITE_comp_right
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
  (Function.updateITE g a b) ∘ f =
    Function.updateITE (g ∘ f) (finv a) b :=
  by
  funext x
  simp only [Function.updateITE]
  simp
  congr!
  constructor
  · intro a1
    simp only [← a1]
    obtain s1 := Function.left_id_left_inverse f finv h1
    simp only [Function.LeftInverse] at s1
    simp only [s1 x]
  · intro a1
    simp only [a1]
    obtain s1 := Function.right_id_right_inverse f finv h2
    simp only [Function.RightInverse] at s1
    simp only [Function.LeftInverse] at s1
    exact s1 a


theorem Function.updateITE_comp_right_injective
  {α β γ : Type}
  [DecidableEq α]
  [DecidableEq β]
  (f : α → β)
  (g : β → γ)
  (a : α)
  (b : γ)
  (h1 : Function.Injective f) :
  (Function.updateITE g (f a) b) ∘ f =
    Function.updateITE (g ∘ f) a b :=
  by
  simp only [Function.Injective] at h1

  funext x
  simp only [Function.updateITE]
  simp
  congr!
  constructor
  · apply h1
  · intro a1
    subst a1
    rfl


theorem Function.updateITE_comm
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (a b : α)
  (u v : β)
  (h1 : ¬ a = b) :
  Function.updateITE (Function.updateITE f a v) b u =
    Function.updateITE (Function.updateITE f b u) a v :=
  by
  funext x
  simp only [Function.updateITE]
  split_ifs
  case _ c1 c2 =>
    subst c1 c2
    contradiction
  case _ | _ | _ =>
    rfl


theorem Function.updateITE_idem
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (a : α)
  (x y : β) :
  Function.updateITE (Function.updateITE f a x) a y =
    Function.updateITE f a y :=
  by
  funext v
  simp only [Function.updateITE]
  split_ifs
  · rfl
  · rfl


theorem Function.updateITE_id
  {α : Type}
  [DecidableEq α]
  (x : α) :
  Function.updateITE (id : α → α) x x = id :=
  by
  funext v
  simp only [Function.updateITE]
  split_ifs
  case _ c1 =>
    subst c1
    simp
  case _ =>
    rfl


theorem Function.updateITE_comm_id
  {α : Type}
  [DecidableEq α]
  (x a b : α)
  (h1 : ¬ x = a) :
  Function.updateITE (Function.updateITE id a b) x x =
    Function.updateITE id a b :=
  by
  funext y
  simp only [Function.updateITE]
  simp
  intro a1
  subst a1
  simp only [if_neg h1]


theorem Function.updateITE_coincide
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (x : α)
  (h1 : ∀ y : α, ¬ y = x → f y = g y) :
  Function.updateITE f x (g x) = g :=
  by
  funext y
  simp only [Function.updateITE]
  split_ifs
  case _ c1 =>
    subst c1
    rfl
  case _ c1 =>
    exact h1 y c1


theorem Function.updateITE_not_mem_list
  {α β : Type}
  [DecidableEq α]
  (l : List α)
  (f : α → β)
  (a : α)
  (b : β)
  (h1 : a ∉ l) :
  l.map (Function.updateITE f a b) = l.map f :=
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
      simp only [Function.updateITE]
      split_ifs <;> tauto


theorem Function.updateITE_not_mem_set
  {α β : Type}
  [DecidableEq α]
  [DecidableEq β]
  (S : Finset α)
  (f : α → β)
  (a : α)
  (b : β)
  (h1 : a ∉ S) :
  Finset.image (Function.updateITE f a b) S =
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
    · simp only [Function.updateITE]
      split_ifs
      case _ c1 =>
        subst c1
        contradiction
      case _ c1 =>
        rfl
    · exact S_ih h1_right


theorem Function.updateITE_symm
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (x y : α)
  (d d' : β)
  (h1 : ¬ x = y) :
  Function.updateITE (Function.updateITE f x d) y d' =
    Function.updateITE (Function.updateITE f y d') x d :=
  by
  funext a
  simp only [Function.updateITE]
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


-- Function.updateListITE

theorem Function.updateListITE_comp
  {α β γ : Type}
  [DecidableEq α]
  (f : α → β)
  (g : β → γ)
  (xs : List α)
  (ys : List β) :
  g ∘ Function.updateListITE f xs ys =
    Function.updateListITE (g ∘ f) xs (ys.map g) :=
  by
  induction xs generalizing ys
  case nil =>
    simp only [Function.updateListITE]
  case cons _ xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp
      simp only [Function.updateListITE]
    case cons ys_hd ys_tl =>
      simp
      simp only [Function.updateListITE]
      simp only [← xs_ih]
      apply Function.updateITE_comp_left


theorem Function.updateListITE_mem'
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (xs ys : List α)
  (x : α)
  (h1 : f x = g x) :
  Function.updateListITE f xs (List.map f ys) x =
    Function.updateListITE g xs (List.map f ys) x :=
  by
  induction xs generalizing ys
  case nil =>
    simp only [Function.updateListITE]
    exact h1
  case cons _ xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp
      simp only [Function.updateListITE]
      exact h1
    case cons ys_hd ys_tl =>
      simp
      simp only [Function.updateListITE]
      simp only [Function.updateITE]
      split_ifs
      · rfl
      · exact xs_ih ys_tl


theorem Function.updateListITE_mem_eq_len
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (v : α)
  (xs : List α)
  (ys : List β)
  (h1 : v ∈ xs)
  (h2 : xs.length = ys.length) :
  Function.updateListITE f xs ys v =
    Function.updateListITE g xs ys v :=
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
      simp only [Function.updateListITE]
      simp only [Function.updateITE]
      cases h1
      case inl h1 =>
        simp only [if_pos h1]
      case inr h1 =>
        split_ifs
        case pos =>
          rfl
        case neg c1 =>
          simp at h2
          exact xs_ih ys_tl h1 h2


theorem Function.updateListITE_mem
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (v : α)
  (xs : List α)
  (ys : List β)
  (h1 : v ∈ xs)
  (h2 : f v = g v) :
  Function.updateListITE f xs ys v =
    Function.updateListITE g xs ys v :=
  by
  induction xs generalizing ys
  case nil =>
    contradiction
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp at h1

      simp only [Function.updateListITE]
      exact h2
    case cons ys_hd ys_tl =>
      simp at h1

      simp only [Function.updateListITE]
      simp only [Function.updateITE]
      split_ifs
      case pos =>
        rfl
      case neg c1 =>
        cases h1
        case inl c2 =>
          contradiction
        case inr c2 =>
          exact xs_ih ys_tl c2


theorem Function.updateListITE_not_mem
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (v : α)
  (xs : List α)
  (ys : List β)
  (h1 : v ∉ xs) :
  Function.updateListITE f xs ys v = f v :=
  by
  induction xs generalizing ys
  case nil =>
    simp only [Function.updateListITE]
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [Function.updateListITE]
    case cons ys_hd ys_tl =>
      simp only [Function.updateListITE]
      simp only [Function.updateITE]
      split_ifs
      case pos c1 =>
        subst c1
        simp at h1
      case neg c1 =>
        simp at h1
        push_neg at h1
        cases h1
        case intro h1_left h1_right =>
          apply xs_ih ys_tl h1_right


theorem Function.updateListITE_updateIte
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (l1 : List α)
  (l2 : List β)
  (x y : α)
  (z : β)
  (h1 : ¬ x = y) :
  Function.updateListITE (Function.updateITE f y z) l1 l2 x =
    Function.updateListITE f l1 l2 x :=
  by
  induction l1 generalizing l2
  case nil =>
    simp only [Function.updateListITE]
    simp only [Function.updateITE]
    simp only [if_neg h1]
  case cons l1_hd l1_tl l1_ih =>
    cases l2
    case nil =>
      simp only [Function.updateListITE]
      simp only [Function.updateITE]
      simp only [if_neg h1]
    case cons l2_hd l2_tl =>
      simp only [Function.updateListITE]
      simp only [Function.updateITE]
      split_ifs
      case pos c1 =>
        rfl
      case neg c1 =>
        apply l1_ih


theorem Function.updateListITE_fun_coincide_mem_eq_len
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (xs ys : List α)
  (x : α)
  (h1 : ∀ (v : α), v ∈ ys → f v = g v)
  (h2 : x ∈ xs)
  (h3 : xs.length = ys.length):
  Function.updateListITE f xs (List.map f ys) x =
    Function.updateListITE g xs (List.map g ys) x :=
  by
  have s1 : List.map f ys = List.map g ys
  simp only [List.map_eq_map_iff]
  exact h1

  simp only [s1]
  apply Function.updateListITE_mem_eq_len
  · exact h2
  · simp
    exact h3


theorem Function.updateListITE_map_mem_ext
  {α β : Type}
  [DecidableEq α]
  (l1 l2 : List α)
  (f g h h' : α → β)
  (x : α)
  (h1 : ∀ y : α, y ∈ l2 → h y = h' y)
  (h2 : l1.length = l2.length)
  (h3 : x ∈ l1) :
  Function.updateListITE f l1 (List.map h l2) x =
      Function.updateListITE g l1 (List.map h' l2) x :=
  by
  have s1 : List.map h l2 = List.map h' l2
  simp only [List.map_eq_map_iff]
  exact h1

  simp only [s1]
  apply Function.updateListITE_mem_eq_len
  · exact h3
  · simp
    exact h2


theorem Function.updateListITE_map_mem
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (l : List α)
  (x : α)
  (h1 : x ∈ l) :
  Function.updateListITE f l (List.map g l) x = g x :=
  by
  induction l
  case nil =>
    simp at h1
  case cons hd tl ih =>
    simp at h1

    simp
    simp only [Function.updateListITE]
    simp only [Function.updateITE]
    split_ifs
    case _ c1 =>
      subst c1
      rfl
    case _ c1 =>
      tauto


theorem Function.updateListITE_map_updateIte
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (l1 l2 : List α)
  (v : α)
  (a : β)
  (x : α)
  (h1 : ∀ y : α, y ∈ l2 → ¬ y = v)
  (h2 : l1.length = l2.length)
  (h3 : x ∈ l1) :
  Function.updateListITE f l1 (List.map f l2) x =
  Function.updateListITE g l1 (List.map (Function.updateITE f v a) l2) x :=
  by
  have s1 : ∀ y : α, y ∈ l2 → f y =Function.updateITE f v a y
  intro y a1
  simp only [Function.updateITE]
  split_ifs
  case _ c1 =>
    specialize h1 y a1
    contradiction
  case _ c2 =>
    rfl

  exact Function.updateListITE_map_mem_ext l1 l2 f g f (Function.updateITE f v a) x s1 h2 h3


#lint
