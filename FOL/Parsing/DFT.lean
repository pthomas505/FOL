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


-------------------------------------------------------------------------------


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


lemma list_direct_succ_list_cons
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (x : Node)
  (xs : List Node) :
  list_direct_succ_list g (x :: xs) = (direct_succ_list g x) ++ (list_direct_succ_list g xs) :=
  by
    simp only [list_direct_succ_list]
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


-------------------------------------------------------------------------------


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


example : dft [] [0] = [0] := by with_unfolding_all rfl
example : dft [(0, [0])] [0] = [0] := by with_unfolding_all rfl
example : dft [(1, [1])] [0] = [0] := by with_unfolding_all rfl
example : dft [(0, [1])] [0] = [1, 0] := by with_unfolding_all rfl
example : dft [(0, [1]), (1, [1])] [0] = [1, 0] := by with_unfolding_all rfl
example : dft [(0, [1]), (1, [0])] [0] = [1, 0] := by with_unfolding_all rfl
example : dft [(0, [1]), (1, [2])] [0] = [2, 1, 0] := by with_unfolding_all rfl
example : dft [(0, [1]), (1, [2]), (2, [0])] [0] = [2, 1, 0] := by with_unfolding_all rfl


example
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (visited : List Node) :
  dft_aux g [] visited = visited :=
  by
    simp only [dft_aux]


lemma dft_aux_cons
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node)
  (visited : List Node)
  (x : Node)
  (h1 : x ∈ visited) :
  dft_aux g (x :: stack) visited = dft_aux g stack visited :=
  by
    simp only [dft_aux]
    simp only [if_pos h1]


lemma dft_aux_append
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


lemma extracted_1
  {α : Type}
  (xs ys zs : List α)
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


lemma extracted_2
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


lemma extracted_3
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
      · exact Set.subset_union_left
    · exact Set.subset_union_right


lemma extracted_4
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


lemma list_direct_succ_set_closed_dft_aux_aux
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


lemma list_direct_succ_set_closed_dft_aux
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node) :
  list_direct_succ_set g (dft_aux g stack []) ⊆ (dft_aux g stack []).toFinset.toSet :=
  by
    apply list_direct_succ_set_closed_dft_aux_aux
    simp only [list_direct_succ_set]
    simp


-------------------------------------------------------------------------------


/--
  `reachable g x` := The reflexive transitive closure of `x` under `g`. The nodes that are reachable from `x` through a sequence of zero or more directed edges in `g`.
-/
inductive reachable
  {Node : Type}
  [DecidableEq Node]
  (g : List (Node × Node))
  (x : Node) :
  Set Node
  | base :
    reachable g x x

  | step
    (e : (Node × Node)) :
    e ∈ g →
    reachable g x e.fst →
    reachable g x e.snd


/--
  `reachable_from_list g xs` := The reflexive transitive closure of `xs` under `g`. The union of the nodes that are reachable from each node in `xs` through a sequence of zero or more directed edges in `g`.
-/
inductive reachable_from_list
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (xs : List Node) :
  Set Node
  | base
    (x : Node) :
    x ∈ xs →
    reachable_from_list g xs x

  | step
    (x : Node)
    (e : (Node × List Node)) :
    e ∈ g →
    x ∈ e.snd →
    reachable_from_list g xs e.fst →
    reachable_from_list g xs x


example
  {Node : Type}
  [DecidableEq Node]
  (g : List (Node × Node))
  (x : Node) :
  reachable g x ⊆ reachable_from_list (g.map (fun (e : Node × Node) => (e.fst, [e.snd]))) [x] :=
  by
    simp only [Set.subset_def]
    intro y a1
    induction a1
    case base =>
      apply reachable_from_list.base
      simp
    case step g e ih_2 _ ih_4 =>
      apply reachable_from_list.step _ (e.fst, [e.snd])
      · simp
        exact ih_2
      · simp
      · simp
        exact ih_4


lemma base_of_reachable_from_list_is_subset_of_reachable_from_list
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (xs : List Node) :
  xs.toFinset.toSet ⊆ reachable_from_list g xs :=
  by
    simp only [Set.subset_def]
    intro x a1
    simp at a1
    exact reachable_from_list.base x a1


lemma reachable_from_list_mono
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (xs ys : List Node)
  (h1 : xs ⊆ ys) :
  reachable_from_list g xs ⊆ reachable_from_list g ys :=
  by
    simp only [Set.subset_def]
    intro x a1
    induction a1
    case base a ih =>
      apply reachable_from_list.base
      apply Set.mem_of_subset_of_mem h1 ih
    case step x e ih_1 ih_2 _ ih_4 =>
      exact reachable_from_list.step x e ih_1 ih_2 ih_4


lemma reachable_from_list_of_append_left
  {Node : Type}
  [inst : DecidableEq Node]
  (g : Graph Node)
  (xs ys : List Node) :
  reachable_from_list g (xs ++ ys) ⊆ reachable_from_list g xs ∪ reachable_from_list g ys :=
  by
    simp only [Set.subset_def]
    intro x a1
    simp
    induction a1
    case _ x ih =>
      simp at ih
      cases ih
      case inl c1 =>
        left
        exact reachable_from_list.base x c1
      case inr c1 =>
        right
        exact reachable_from_list.base x c1
    case _ x e ih_1 ih_2 ih_3 ih_4 =>
      cases ih_4
      case _ left =>
        left
        exact reachable_from_list.step x e ih_1 ih_2 left
      case _ right =>
        right
        exact reachable_from_list.step x e ih_1 ih_2 right


lemma reachable_from_list_of_append_right
  {Node : Type}
  [inst : DecidableEq Node]
  (g : Graph Node)
  (xs ys : List Node) :
  reachable_from_list g xs ∪ reachable_from_list g ys ⊆ reachable_from_list g (xs ++ ys) :=
  by
    simp only [Set.subset_def]
    intro x a1
    simp at a1
    cases a1
    case _ left =>
      apply reachable_from_list_mono g xs (xs ++ ys)
      · simp
      · exact left
    case _ right =>
      apply reachable_from_list_mono g ys (xs ++ ys)
      · simp
      · exact right


lemma reachable_from_list_of_append
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (xs ys : List Node) :
  reachable_from_list g (xs ++ ys) = reachable_from_list g xs ∪ reachable_from_list g ys :=
  by
    apply Set.eq_of_subset_of_subset
    · apply reachable_from_list_of_append_left
    · apply reachable_from_list_of_append_right


lemma reachable_from_list_of_cons
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (x : Node)
  (ys : List Node) :
  reachable_from_list g (x :: ys) = reachable_from_list g [x] ∪ reachable_from_list g ys :=
  by
    simp only [← reachable_from_list_of_append]
    simp


lemma reachable_from_list_direct_succ_list_is_subset_of_reachable_from_list
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (x : Node) :
  reachable_from_list g (direct_succ_list g x) ⊆ reachable_from_list g [x] :=
  by
    simp only [Set.subset_def]
    intro a a1
    induction a1
    case _ x y ih =>
      obtain s1 := mem_direct_succ_list_iff g x y
      simp only [s1] at ih
      apply Exists.elim ih
      intro ys a2
      cases a2
      case _ a2_left a2_right =>
        apply reachable_from_list.step y (x, ys) a2_right a2_left
        apply reachable_from_list.base x
        simp
    case _ x e ih_1 ih_2 _ ih_4 =>
      exact reachable_from_list.step x e ih_1 ih_2 ih_4


lemma reachable_from_list_list_direct_succ_list_is_subset_of_reachable_from_list
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (xs : List Node) :
  reachable_from_list g (list_direct_succ_list g xs) ⊆ reachable_from_list g xs :=
  by
    simp only [Set.subset_def]
    intro x a1
    induction xs
    case nil =>
      simp only [list_direct_succ_list] at a1
      simp at a1
      exact a1
    case cons hd tl ih =>
      simp only [list_direct_succ_list_cons] at a1

      simp only [reachable_from_list_of_cons g hd tl]
      simp
      simp only [reachable_from_list_of_append] at a1
      simp at a1
      cases a1
      case _ left =>
        left
        obtain s1 := reachable_from_list_direct_succ_list_is_subset_of_reachable_from_list g hd
        exact Set.mem_of_subset_of_mem s1 left
      case _ right =>
        right
        exact ih right


lemma dft_aux_is_subset_of_reachable_from_list_and_visited
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node)
  (visited : List Node) :
  (dft_aux g stack visited).toFinset.toSet ⊆
    reachable_from_list g stack ∪ visited.toFinset.toSet :=
  by
    induction stack, visited using dft_aux.induct g
    case _ visited =>
      simp only [dft_aux]
      simp
    case _ visited x stack c1 ih =>
      simp only [reachable_from_list_of_cons g x stack]

      simp only [dft_aux]
      simp only [if_pos c1]

      simp only [Set.union_assoc ]
      exact Set.subset_union_of_subset_right ih (reachable_from_list g [x])
    case _ visited x stack c1 ih =>
      simp only [dft_aux]
      simp only [if_neg c1]

      simp only [reachable_from_list_of_append g (direct_succ_list g x) stack] at ih

      simp only [reachable_from_list_of_cons g x stack]

      trans (reachable_from_list g (direct_succ_list g x) ∪ reachable_from_list g stack ∪ (x :: visited).toFinset.toSet)
      · exact ih
      · have s1 : reachable_from_list g (direct_succ_list g x) ⊆ reachable_from_list g [x] := reachable_from_list_direct_succ_list_is_subset_of_reachable_from_list g x

        simp only [Set.subset_def] at *
        simp at *
        tauto


lemma extracted_5
  {α : Type}
  [inst : DecidableEq α]
  (g : Graph α)
  (xs : List α)
  (h1 : list_direct_succ_set g xs ⊆ xs.toFinset.toSet) :
  reachable_from_list g xs ⊆ xs.toFinset.toSet :=
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
      exact h1 x e.fst ih_4 e.snd ih_2 ih_1


lemma list_direct_succ_set_closed_reachable_from_list
  {α : Type}
  [DecidableEq α]
  (g : Graph α)
  (xs : List α)
  (h1 : list_direct_succ_set g xs ⊆ xs.toFinset.toSet) :
  xs.toFinset.toSet = reachable_from_list g xs :=
  by
    apply Set.eq_of_subset_of_subset
    · apply base_of_reachable_from_list_is_subset_of_reachable_from_list
    · exact extracted_5 g xs h1


lemma reachable_from_list_closed_dft_aux
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node) :
  reachable_from_list g stack ⊆ (dft_aux g stack []).toFinset.toSet :=
  by
    have s1 : (dft_aux g stack []).toFinset.toSet = reachable_from_list g (dft_aux g stack []) :=
    by
      apply list_direct_succ_set_closed_reachable_from_list g (dft_aux g stack [])
      exact list_direct_succ_set_closed_dft_aux g stack

    simp only [s1]
    apply reachable_from_list_mono g stack (dft_aux g stack [])
    exact stack_subset_dft_aux g stack []


-------------------------------------------------------------------------------


theorem dft_aux_eq_reachable_from_list
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node) :
  (dft_aux g stack []).toFinset.toSet = reachable_from_list g stack :=
  by
    have s1 : (dft_aux g stack []).toFinset.toSet ⊆ reachable_from_list g stack ∪ [].toFinset.toSet := dft_aux_is_subset_of_reachable_from_list_and_visited g stack []
    simp only [List.toFinset_nil, Finset.coe_empty, Set.union_empty] at s1

    have s2 : reachable_from_list g stack ⊆ (dft_aux g stack []).toFinset.toSet := reachable_from_list_closed_dft_aux g stack

    exact Set.eq_of_subset_of_subset s1 s2


-------------------------------------------------------------------------------


theorem dft_iff {α : Type} [DecidableEq α] (g : Graph α) (S : List α) (s' : α) :
  s' ∈ dft g S ↔ ∃ s ∈ S, Relation.ReflTransGen (fun a b => ∃ l, (a,l) ∈ g ∧ b ∈ l) s s' := by
  have := congrArg (s' ∈ ·) (dft_aux_eq_reachable_from_list g S)
  simp at this; simp [dft, this]; clear this
  constructor
  · intro h
    induction h with
    | base _ h => exact ⟨_, h, .refl⟩
    | step _ _ h1 h2 _ ih =>
      have ⟨_, h3, h4⟩ := ih
      exact ⟨_, h3, .tail h4 ⟨_, h1, h2⟩⟩
  · intro ⟨s, h1, h2⟩
    induction h2 with
    | refl => exact reachable_from_list.base _ h1
    | tail _ h ih =>
      have ⟨_, h3, h4⟩ := h
      exact reachable_from_list.step _ _ h3 h4 ih


#lint
