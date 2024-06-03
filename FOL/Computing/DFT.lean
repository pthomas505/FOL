import Mathlib.Data.Finset.Basic


-- The depth first traversal of a directed graph.

-- Adapted from https://www.isa-afp.org/entries/Depth-First-Search.html.


lemma list_cons_to_set_union
  {α : Type}
  [inst : DecidableEq α]
  (ys : List α)
  (x : α) :
  (x :: ys).toFinset.toSet = {x} ∪ ys.toFinset.toSet :=
  by
    ext a
    simp

lemma list_append_to_set_union
  {α : Type}
  [inst : DecidableEq α]
  (xs ys : List α) :
  (xs ++ ys).toFinset.toSet = xs.toFinset.toSet ∪ ys.toFinset.toSet :=
  by
    ext a
    simp


/--
  The representation of a directed graph as a list of directed edges.
  `(x, ys)` is in the list if and only if there is a directed edge from `x` to each of the nodes in `ys`.
-/
@[reducible]
def Graph
  (Node : Type) :
  Type :=
  List (Node × List Node)


/--
  `direct_succ_list g x` := The image of `x` under `g`. The direct successors of `x` as a list.
-/
def direct_succ_list
  {Node : Type}
  [DecidableEq Node] :
  Graph Node → Node → List Node
  | [], _ => []
  | hd :: tl, x =>
    if hd.fst = x
    then hd.snd ++ direct_succ_list tl x
    else direct_succ_list tl x


/--
  `direct_succ_set g x` := The image of `x` under `g`. The direct successors of `x` as a set.
-/
def direct_succ_set
  {Node : Type}
  (g : Graph Node)
  (x : Node) :
  Set Node :=
  {y : Node | ∃ (ys : List Node), y ∈ ys ∧ (x, ys) ∈ g}


lemma mem_direct_succ_list_iff
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node) :
  ∀ (x y : Node), y ∈ direct_succ_list g x ↔ ∃ (ys : List Node), y ∈ ys ∧ (x, ys) ∈ g :=
  by
    induction g
    case nil =>
      simp only [direct_succ_list]
      simp
    case cons hd tl ih =>
      simp only [direct_succ_list]
      intro x y
      split_ifs
      case pos c1 =>
        subst c1
        simp
        simp only [ih]
        constructor
        · intro a1
          cases a1
          case _ left =>
            apply Exists.intro hd.snd
            tauto
          case _ right =>
            apply Exists.elim right
            intro zs a2
            apply Exists.intro zs
            tauto
        · intro a1
          simp only [Prod.eq_iff_fst_eq_snd_eq] at a1
          simp at a1
          apply Exists.elim a1
          intro zs a2
          cases a2
          case _ a2_left a2_right =>
            cases a2_right
            case _ left =>
              subst left
              tauto
            case _ right =>
              right
              apply Exists.intro zs
              tauto
      case neg c1 =>
        simp
        simp only [ih]
        constructor
        · intro a1
          apply Exists.elim a1
          intro zs a2
          cases a2
          case _ a2_left a2_right =>
            apply Exists.intro zs
            tauto
        · intro a1
          simp only [Prod.eq_iff_fst_eq_snd_eq] at a1
          tauto


lemma direct_succ_list_set_equiv
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (x : Node) :
  (direct_succ_list g x).toFinset.toSet = direct_succ_set g x :=
  by
    ext a
    simp only [direct_succ_set]
    simp
    simp only [mem_direct_succ_list_iff]


/--
  `list_direct_succ_list g xs` := The image of `xs` under `g`. The direct successors of `xs` as a list.
-/
def list_direct_succ_list
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (xs : List Node) :
  List Node :=
  (xs.map (fun (x : Node) => direct_succ_list g x)).join


/--
  `list_direct_succ_set g xs` := The image of `xs` under `g`. The direct successors of `xs` as a set.
-/
def list_direct_succ_set
  {Node : Type}
  (g : Graph Node)
  (xs : List Node) :
  Set Node :=
  {y : Node | ∃ (x : Node), x ∈ xs ∧ ∃ (ys : List Node), y ∈ ys ∧ (x, ys) ∈ g}


lemma mem_list_direct_succ_list_iff
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node) :
  ∀ (xs : List Node) (y : Node), y ∈ list_direct_succ_list g xs ↔ ∃ (x : Node), x ∈ xs ∧ ∃ (ys : List Node), y ∈ ys ∧ (x, ys) ∈ g :=
  by
    simp only [list_direct_succ_list]
    simp only [← mem_direct_succ_list_iff]
    simp


lemma list_direct_succ_list_set_equiv
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (xs : List Node) :
  (list_direct_succ_list g xs).toFinset.toSet = list_direct_succ_set g xs :=
  by
    simp only [list_direct_succ_set]
    simp only [← mem_list_direct_succ_list_iff]
    simp


lemma list_direct_succ_set_cons
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (x : Node)
  (xs : List Node) :
  list_direct_succ_set g (x :: xs) = (direct_succ_list g x).toFinset.toSet ∪ list_direct_succ_set g xs :=
  by
    simp only [list_direct_succ_set]
    simp only [← mem_direct_succ_list_iff]
    simp
    rfl


/--
  `Graph.nodes_of g` := The nodes of `g`.
-/
def Graph.nodes_of
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node) :
  List Node :=
  (g.map Prod.fst) ∪ (g.map Prod.snd).join


lemma not_mem_imp_no_direct_succ
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (x : Node)
  (h1 : x ∉ g.nodes_of) :
  direct_succ_list g x = [] :=
  by
    induction g
    case nil =>
      simp only [direct_succ_list]
    case cons hd tl ih =>
      simp only [Graph.nodes_of] at ih
      simp at ih

      simp only [Graph.nodes_of] at h1
      simp at h1

      simp only [direct_succ_list]
      split_ifs
      case pos c1 =>
        subst c1
        simp at h1
      case neg c1 =>
        tauto


lemma List.erase_diff_len_lt_diff_len
  {α : Type}
  [DecidableEq α]
  (l1 l2 : List α)
  (x : α)
  (h1 : x ∈ l1)
  (h2 : x ∉ l2) :
  ((l1.erase x).diff l2).length < (l1.diff l2).length :=
  by
    simp only [← List.diff_erase]

    have s1 : x ∈ l1.diff l2 := List.mem_diff_of_mem h1 h2

    have s2 : ((l1.diff l2).erase x).length = (l1.diff l2).length.pred := List.length_erase_of_mem s1
    simp only [s2]

    have s3 : 0 < (l1.diff l2).length := List.length_pos_of_mem s1

    exact Nat.pred_lt' s3


/--
  Helper function for `dft`.
-/
def dft_aux
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node)
  (visited : List Node) :
  List Node :=
  match stack with
  | [] => visited
  | x :: xs =>
    if x ∈ visited
    then dft_aux g xs visited
    else dft_aux g (direct_succ_list g x ++ xs) (x :: visited)

  termination_by ((g.nodes_of.diff visited).length, stack.length)
  decreasing_by
    case _ _ =>
      simp_wf
      decreasing_trivial
    case _ c1 =>
      simp_wf
      by_cases c2 : x ∈ g.nodes_of
      case pos =>
        have s1 : ((g.nodes_of.erase x).diff visited).length < (g.nodes_of.diff visited).length := List.erase_diff_len_lt_diff_len g.nodes_of visited x c2 c1

        exact Prod.Lex.left ((direct_succ_list g x).length + xs.length) (xs.length + 1) s1
      case neg =>
        have s1 : g.nodes_of.erase x = g.nodes_of := List.erase_of_not_mem c2
        simp only [s1]

        simp only [not_mem_imp_no_direct_succ g x c2]
        simp
        apply Prod.Lex.right (g.nodes_of.diff visited).length
        exact Nat.lt.base xs.length


/--
  `dft g start` := The depth first traversal of `g` from `start`. The nodes of `g` that are reachable from `start`.
-/
def dft
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (start : List Node) :
  List Node :=
  dft_aux g start []


example : dft [] [0] = [0] := by rfl
example : dft [(0, [0])] [0] = [0] := by rfl
example : dft [(1, [1])] [0] = [0] := by rfl
example : dft [(0, [1])] [0] = [1, 0] := by rfl
example : dft [(0, [1]), (1, [1])] [0] = [1, 0] := by rfl
example : dft [(0, [1]), (1, [0])] [0] = [1, 0] := by rfl
example : dft [(0, [1]), (1, [2])] [0] = [2, 1, 0] := by rfl
example : dft [(0, [1]), (1, [2]), (2, [0])] [0] = [2, 1, 0] := by rfl


example
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (visited : List Node) :
  dft_aux g [] visited = visited :=
  by
    simp only [dft_aux]


example
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node)
  (visited : List Node)
  (x : Node)
  (h1 : x ∈ visited) :
  dft_aux g stack visited = dft_aux g (x :: stack) visited :=
  by
    simp only [dft_aux]
    simp only [if_pos h1]


example
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (xs ys : List Node)
  (zs : List Node) :
  dft_aux g (xs ++ ys) zs = dft_aux g ys (dft_aux g xs zs) :=
  by
    induction xs, zs using dft_aux.induct g
    case _ visited =>
      simp only [dft_aux]
      simp
    case _ visited x xs c1 ih =>
      simp only [dft_aux]
      simp only [if_pos c1]
      simp only [← ih]
      simp
      simp only [dft_aux]
      simp only [if_pos c1]
    case _ visited x xs c1 ih =>
      simp only [dft_aux]
      simp only [if_neg c1]
      simp only [← ih]
      simp
      simp only [dft_aux]
      simp only [if_neg c1]


lemma visited_subset_dft_aux
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node)
  (visited : List Node) :
  visited ⊆ dft_aux g stack visited :=
  by
    induction stack, visited using dft_aux.induct g
    case _ visited =>
      simp only [dft_aux]
      simp
    case _ visited x stack c1 ih =>
      simp only [dft_aux]
      simp only [if_pos c1]
      exact ih
    case _ visited x stack c1 ih =>
      simp only [dft_aux]
      simp only [if_neg c1]
      trans (x :: visited)
      · simp
      · exact ih


theorem extracted_1
  {α : Type}
  (xs  : List α)
  (ys : List α)
  (zs : List α)
  (x : α)
  (h1 : zs ⊆ xs)
  (h2 : x ∈ ys)
  (h3 : ys ⊆ xs) :
  x :: zs ⊆ xs :=
  by
    simp
    constructor
    · apply Set.mem_of_subset_of_mem h3 h2
    · exact h1


theorem extracted_2
  {α : Type}
  (ws xs ys zs : List α)
  (x : α)
  (h1 : ws ++ ys ⊆ zs)
  (h2 : x :: xs ⊆ zs) :
  x :: ys ⊆ zs :=
  by
    simp at *
    tauto


lemma stack_subset_dft_aux
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node)
  (visited : List Node) :
  stack ⊆ dft_aux g stack visited :=
  by
    induction stack, visited using dft_aux.induct g
    case _ visited =>
      simp only [dft_aux]
      simp
    case _ visited x stack c1 ih =>
      simp only [dft_aux]
      simp only [if_pos c1]
      apply extracted_1 (dft_aux g stack visited) visited stack x ih c1
      exact visited_subset_dft_aux g stack visited
    case _ visited x stack c1 ih =>
      simp only [dft_aux]
      simp only [if_neg c1]
      apply extracted_2 (direct_succ_list g x) visited stack (dft_aux g (direct_succ_list g x ++ stack) (x :: visited)) x ih
      apply visited_subset_dft_aux g (direct_succ_list g x ++ stack) (x :: visited)


theorem extracted_3
  {α : Type}
  [inst : DecidableEq α]
  (xs ys : List α)
  (x : α)
  (h1 : x ∈ xs) :
  (x :: ys).toFinset.toSet ∪ xs.toFinset.toSet ⊆ ys.toFinset.toSet ∪ xs.toFinset.toSet :=
  by
    simp only [list_cons_to_set_union]
    apply Set.union_subset
    · apply Set.union_subset
      · simp
        right
        exact h1
      · exact Set.subset_union_left ys.toFinset.toSet xs.toFinset.toSet
    · exact Set.subset_union_right ys.toFinset.toSet xs.toFinset.toSet


theorem extracted_4
  {Node : Type}
  [inst : DecidableEq Node]
  (xs ys zs : List Node)
  (S : Set Node)
  (x : Node)
  (h1 : S ⊆ (x :: zs).toFinset.toSet ∪ ys.toFinset.toSet) :
  xs.toFinset.toSet ∪ S ⊆ (xs ++ zs).toFinset.toSet ∪ (x :: ys).toFinset.toSet :=
  by
    simp only [list_cons_to_set_union] at h1
    simp only [Set.subset_def] at h1
    simp at h1

    simp only [list_cons_to_set_union]
    simp only [list_append_to_set_union]
    simp only [Set.subset_def]
    simp
    intro a a1
    specialize h1 a
    tauto


lemma list_direct_succ_set_closed_dft_aux
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node)
  (visited : List Node)
  (h1 : list_direct_succ_set g visited ⊆ stack.toFinset.toSet ∪ visited.toFinset.toSet) :
  list_direct_succ_set g (dft_aux g stack visited) ⊆ (dft_aux g stack visited).toFinset.toSet :=
  by
    induction stack, visited using dft_aux.induct g
    case _ visited =>
      simp at h1

      simp only [dft_aux]
      simp
      exact h1
    case _ visited x stack c1 ih =>
      simp only [dft_aux]
      simp only [if_pos c1]
      apply ih
      trans (x :: stack).toFinset.toSet ∪ visited.toFinset.toSet
      · exact h1
      · exact extracted_3 visited stack x c1
    case _ visited x stack c1 ih =>
      simp only [dft_aux]
      simp only [if_neg c1]
      apply ih
      simp only [list_direct_succ_set_cons]
      exact extracted_4 (direct_succ_list g x) visited stack (list_direct_succ_set g visited) x h1


lemma list_direct_succ_set_closed_dft
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node) :
  list_direct_succ_set g (dft_aux g stack []) ⊆ (dft_aux g stack []).toFinset.toSet :=
  by
    apply list_direct_succ_set_closed_dft_aux
    simp only [list_direct_succ_set]
    simp


/--
  `reachable g xs` := The reflexive transitive closure of `xs` under `g`. The union of the nodes that are reachable from each node in `xs` through a sequence of zero or more directed edges in `g`.
-/
inductive reachable
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (xs : List Node) :
  Set Node
  | base
    (x : Node) :
    x ∈ xs →
    reachable g xs x

  | step
    (x : Node)
    (e : (Node × List Node)) :
    e ∈ g →
    x ∈ e.snd →
    reachable g xs e.fst →
    reachable g xs x


lemma subset_of_reachable_is_reachable
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (xs : List Node) :
  xs.toFinset.toSet ⊆ reachable g xs :=
  by
    simp only [Set.subset_def]
    intro x a1
    simp at a1
    exact reachable.base x a1


theorem extracted_5
  {α : Type}
  [inst : DecidableEq α]
  (g : Graph α)
  (xs : List α)
  (h1 : list_direct_succ_set g xs ⊆ xs.toFinset.toSet) :
  reachable g xs ⊆ xs.toFinset.toSet :=
  by
    simp only [list_direct_succ_set] at h1
    simp at h1

    simp only [Set.subset_def]
    simp
    intro a a1
    induction a1
    case _ _ ih =>
      exact ih
    case _ x e ih_1 ih_2 _ ih_4 =>
      exact h1 x e.1 ih_4 e.2 ih_2 ih_1


lemma list_direct_succ_set_closed_reachable
  {α : Type}
  [DecidableEq α]
  (g : Graph α)
  (xs : List α)
  (h1 : list_direct_succ_set g xs ⊆ xs.toFinset.toSet) :
  xs.toFinset.toSet = reachable g xs :=
  by
    apply Set.eq_of_subset_of_subset
    · apply subset_of_reachable_is_reachable
    · exact extracted_5 g xs h1


lemma reachable_mono
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (xs ys : List Node)
  (h1 : xs ⊆ ys) :
  reachable g xs ⊆ reachable g ys :=
  by
    intro x a1
    induction a1
    case base a ih =>
      apply reachable.base
      apply Set.mem_of_subset_of_mem h1 ih
    case step x e ih_1 ih_2 _ ih_4 =>
      exact reachable.step x e ih_1 ih_2 ih_4


lemma reachable_direct_succ_list_is_subset_of_reachable
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (x : Node) :
  reachable g (direct_succ_list g x) ⊆ reachable g [x] :=
  by
    intro a a1
    induction a1
    case _ x y ih =>
      obtain s1 := mem_direct_succ_list_iff g x y
      simp only [s1] at ih
      apply Exists.elim ih
      intro ys a2
      cases a2
      case _ a2_left a2_right =>
      apply reachable.step _ (x, ys) a2_right
      · exact a2_left
      · apply reachable.base x
        simp
    case _ x e ih_1 ih_2 _ ih_4 =>
      apply reachable.step x e ih_1 ih_2 ih_4


lemma reachable_of_append
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (xs ys : List Node) :
  reachable g (xs ++ ys) = reachable g xs ∪ reachable g ys :=
  by
    ext a
    simp
    constructor
    · intro a1
      induction a1
      case _ x ih =>
        simp at ih
        cases ih
        case inl c1 =>
          left
          exact reachable.base x c1
        case inr c1 =>
          right
          exact reachable.base x c1
      case _ x e ih_1 ih_2 ih_3 ih_4 =>
        simp at ih_3
        cases ih_3
        case base c1 =>
          cases ih_4
          case _ left =>
            left
            exact reachable.step x e ih_1 ih_2 left
          case _ right =>
            right
            exact reachable.step x e ih_1 ih_2 right
        case step x' e' ih_1' ih_2' ih_3' =>
          cases ih_4
          case _ left =>
            left
            apply reachable.step x e ih_1 ih_2 left
          case _ right =>
            right
            apply reachable.step x e ih_1 ih_2 right
    · intro a1
      cases a1
      case _ c1 =>
        apply reachable_mono g xs (xs ++ ys)
        simp
        exact c1
      case _ c1 =>
        apply reachable_mono g ys (xs ++ ys)
        simp
        exact c1


lemma dft_aux_is_subset_of_reachable_and_visited
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node)
  (visited : List Node) :
  (dft_aux g stack visited).toFinset.toSet ⊆
    reachable g stack ∪ visited.toFinset.toSet :=
  by
    induction stack, visited using dft_aux.induct g
    case _ visited =>
      simp only [dft_aux]
      simp
    case _ visited x stack c1 ih =>
      simp only [dft_aux]
      simp only [if_pos c1]

      intro a a1
      simp at a1

      have s1 : a ∈ reachable g stack ∪ visited.toFinset.toSet :=
      by
        apply Set.mem_of_subset_of_mem ih
        simp
        exact a1

      have s2 : reachable g stack ⊆ reachable g (x :: stack) :=
      by
        apply reachable_mono
        simp

      aesop
    case _ visited x stack c1 ih =>
      simp only [dft_aux]
      simp only [if_neg c1]

      have s1 : x ∈ reachable g (x :: stack) :=
      by
        have s1_1 : (x :: stack).toFinset.toSet ⊆ reachable g (x :: stack) := subset_of_reachable_is_reachable g (x :: stack)

        apply Set.mem_of_subset_of_mem s1_1
        simp

      have s2 : reachable g (direct_succ_list g x ++ stack) ⊆ reachable g (x :: stack) :=
      by
        have s2_1 : reachable g (direct_succ_list g x ++ stack) = reachable g (direct_succ_list g x) ∪ reachable g stack := reachable_of_append g (direct_succ_list g x) stack

        have s2_2 : reachable g (x :: stack) = reachable g [x] ∪ reachable g stack := reachable_of_append g [x] stack

        have s2_3 : reachable g (direct_succ_list g x) ⊆ reachable g [x] := reachable_direct_succ_list_is_subset_of_reachable g x

        simp only [s2_1, s2_2]
        exact Set.union_subset_union_left (reachable g stack) s2_3

      have s3 : (dft_aux g (direct_succ_list g x ++ stack) (x :: visited)).toFinset.toSet ⊆ reachable g (x :: stack) ∪ (x :: visited).toFinset.toSet :=
      by
        trans (reachable g (direct_succ_list g x ++ stack) ∪ (x :: visited).toFinset.toSet)
        · exact ih
        · exact Set.union_subset_union_left (x :: visited).toFinset.toSet s2

      trans (reachable g (x :: stack) ∪ ↑(x :: visited).toFinset)
      · exact s3
      · intro a a1
        simp at a1
        simp
        aesop


lemma reachable_closed_dft
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node) :
  reachable g stack ⊆ (dft_aux g stack []).toFinset.toSet :=
  by
    have s1 : (dft_aux g stack []).toFinset.toSet = reachable g (dft_aux g stack []) :=
    by
      apply list_direct_succ_set_closed_reachable g (dft_aux g stack [])
      exact list_direct_succ_set_closed_dft g stack

    simp only [s1]
    apply reachable_mono g stack (dft_aux g stack [])
    exact stack_subset_dft_aux g stack []


theorem dft_eq_reachable
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node) :
  (dft_aux g stack []).toFinset.toSet = reachable g stack :=
  by
    have s1 : (dft_aux g stack []).toFinset.toSet ⊆ reachable g stack ∪ [].toFinset.toSet := dft_aux_is_subset_of_reachable_and_visited g stack []

    have s2 : reachable g stack ⊆ (dft_aux g stack []).toFinset.toSet := reachable_closed_dft g stack

    aesop


theorem dft_eq_reachable_singleton
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (start : List Node) :
  (dft g start).toFinset.toSet = reachable g start :=
  by
    simp only [dft]
    exact dft_eq_reachable g start


lemma reachable_nil_graph
  {Node : Type}
  [DecidableEq Node]
  (xs : List Node) :
  reachable [] xs = xs.toFinset.toSet :=
  by
    ext x
    simp
    constructor
    · intro a1
      induction a1
      case _ _ a2 =>
        exact a2
      case _ x e ih_1 ih_2 ih_3 _ =>
        simp at ih_1
    · intro a1
      exact reachable.base x a1


#lint
