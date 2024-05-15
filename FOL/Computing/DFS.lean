import Mathlib.Data.Finset.Basic


-- Depth First Search

-- https://www.isa-afp.org/entries/Depth-First-Search.html


/--
  The adjacency list representation of a graph.
-/
abbrev Graph
  (Node : Type) :
  Type :=
  List (Node × Node)


/--
  `nexts g x` := The image of `x` under `g`. The neighbors of `x`.
  `nexts g x = {y | (x, y) ∈ g}`
-/
def nexts
  {Node : Type}
  [DecidableEq Node] :
  Graph Node → Node → List Node
  | [], _ => []
  | e :: es, n =>
    if e.fst = n
    then e.snd :: (nexts es n)
    else nexts es n


/--
  `nextss g xs` := The image of `xs` under `g`. The neighbors of `xs`.
-/
def nextss
  {Node : Type}
  (g : Graph Node)
  (xs : List Node) :
  Set Node :=
  {y | ∃ (x : Node), x ∈ xs ∧ (x, y) ∈ g}


lemma nexts_set
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node) :
  ∀ (x y : Node), y ∈ nexts g x ↔ (x, y) ∈ g :=
  by
    induction g
    case nil =>
      simp only [nexts]
      simp
    case cons hd tl ih =>
      simp only [nexts]
      intro x y
      split
      case inl c1 =>
        subst c1
        simp only [List.mem_cons]
        simp only [ih]
        constructor
        · tauto
        · intro a1
          simp only [Prod.eq_iff_fst_eq_snd_eq] at a1
          tauto
      case inr c1 =>
        simp only [List.mem_cons]
        simp only [ih]
        constructor
        · tauto
        · intro a1
          simp only [Prod.eq_iff_fst_eq_snd_eq] at a1
          tauto


lemma nextss_cons
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (x : Node)
  (xs : List Node) :
  nextss g (x :: xs) = (nexts g x).toFinset.toSet ∪ nextss g xs :=
  by
    simp only [nextss]
    simp only [← nexts_set]
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
  g.map Prod.fst ∪ g.map Prod.snd


lemma not_in_nodes_imp_nexts_empty
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (x : Node)
  (h1 : x ∉ g.nodes_of) :
  nexts g x = [] :=
  by
    induction g
    case nil =>
      simp only [nexts]
    case cons hd tl ih =>
      simp only [Graph.nodes_of] at ih
      simp only [List.mem_union_iff] at ih
      push_neg at ih

      simp only [Graph.nodes_of] at h1
      simp only [List.mem_union_iff] at h1
      push_neg at h1
      cases h1
      case _ h1_left h1_right =>
        simp only [List.map_cons, List.mem_cons] at h1_left
        push_neg at h1_left
        simp only [ne_eq] at h1_left
        cases h1_left
        case _ h1_left_left h1_left_right =>
          simp only [List.map_cons, List.mem_cons] at h1_right
          push_neg at h1_right
          simp only [ne_eq] at h1_right
          cases h1_right
          case _ h1_right_left h1_right_right =>
            simp only [nexts]
            split
            case _ c1 =>
              tauto
            case _ c1 =>
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
    obtain s1 := List.mem_diff_of_mem h1 h2
    obtain s2 := List.length_erase_of_mem s1
    obtain s3 := List.length_pos_of_mem s1
    obtain s4 := Nat.pred_lt' s3
    simp only [← s2] at s4
    obtain s5 := List.diff_erase l1 l2 x
    simp only [← s5]
    exact s4


/--
  Helper function for `dfs`.
-/
def dfs_aux
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
    then dfs_aux g xs visited
    else dfs_aux g (nexts g x ++ xs) (x :: visited)

  termination_by ((g.nodes_of.diff visited).length, stack.length)
  decreasing_by
    case _ _ =>
      simp_wf
      decreasing_trivial
    case _ c1 =>
      simp_wf
      by_cases c2 : x ∈ g.nodes_of
      case pos =>
        obtain s1 := List.erase_diff_len_lt_diff_len g.nodes_of visited x c2 c1
        exact Prod.Lex.left ((nexts g x).length + xs.length) (xs.length + 1) s1
      case neg =>
        have s1 : (g.nodes_of.erase x) = g.nodes_of := by
          exact List.erase_of_not_mem c2
        simp only [s1]

        simp only [not_in_nodes_imp_nexts_empty g x c2]
        simp
        apply Prod.Lex.right (g.nodes_of.diff visited).length
        exact Nat.lt.base xs.length


/--
  `dfs g start` := The depth first traversal of `g` from `start`. The nodes of `g` that are reachable from `start`.
-/
def dfs
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (start : Node) :
  List Node :=
  dfs_aux g [start] []


example : dfs [] 0 = [0] := by rfl
example : dfs [(0, 0)] 0 = [0] := by rfl
example : dfs [(1, 1)] 0 = [0] := by rfl
example : dfs [(0, 1)] 0 = [1, 0] := by rfl
example : dfs [(0, 1), (1, 1)] 0 = [1, 0] := by rfl
example : dfs [(0, 1), (1, 0)] 0 = [1, 0] := by rfl
example : dfs [(0, 1), (1, 2)] 0 = [2, 1, 0] := by rfl
example : dfs [(0, 1), (1, 2), (2, 0)] 0 = [2, 1, 0] := by rfl


example
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (visited : List Node) :
  dfs_aux g [] visited = visited :=
  by
    simp only [dfs_aux]


example
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node)
  (visited : List Node)
  (x : Node)
  (h1 : x ∈ visited) :
  dfs_aux g stack visited = dfs_aux g (x :: stack) visited :=
  by
    simp only [dfs_aux]
    simp only [if_pos h1]


lemma dfs_app
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (xs ys : List Node)
  (zs : List Node) :
  dfs_aux g (xs ++ ys) zs = dfs_aux g ys (dfs_aux g xs zs) :=
  by
    induction xs, zs using dfs_aux.induct g
    case _ visited =>
      simp only [dfs_aux]
      simp
    case _ visited x xs c1 ih =>
      simp only [dfs_aux]
      simp only [if_pos c1]
      simp only [← ih]
      simp
      simp only [dfs_aux]
      simp only [if_pos c1]
    case _ visited x xs c1 ih =>
      simp only [dfs_aux]
      simp only [if_neg c1]
      simp only [← ih]
      simp
      simp only [dfs_aux]
      simp only [if_neg c1]


lemma visit_subset_dfs
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node)
  (visited : List Node) :
  visited ⊆ dfs_aux g stack visited :=
  by
    induction stack, visited using dfs_aux.induct g
    case _ visited =>
      simp only [dfs_aux]
      simp
    case _ visited x stack c1 ih =>
      simp only [dfs_aux]
      simp only [if_pos c1]
      exact ih
    case _ visited x stack c1 ih =>
      simp only [dfs_aux]
      simp only [if_neg c1]
      trans (x :: visited)
      · simp
      · exact ih


lemma next_subset_dfs
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node)
  (visited : List Node) :
  stack ⊆ dfs_aux g stack visited :=
  by
    induction stack, visited using dfs_aux.induct g
    case _ visited =>
      simp only [dfs_aux]
      simp
    case _ visited x stack c1 ih =>
      simp only [dfs_aux]
      simp only [if_pos c1]
      simp
      constructor
      case left =>
        obtain s1 := visit_subset_dfs g stack visited
        apply Set.mem_of_subset_of_mem s1 c1
      case right =>
        exact ih
    case _ visited x stack c1 ih =>
      simp only [dfs_aux]
      simp only [if_neg c1]
      simp
      constructor
      · have s2 : x ∈ x :: visited := by { simp }
        obtain s1 := visit_subset_dfs g (nexts g x ++ stack) (x :: visited)
        apply Set.mem_of_subset_of_mem s1 s2
      · trans (nexts g x) ++ stack
        · simp
        · exact ih


lemma nextss_closed_dfs'
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node)
  (visited : List Node)
  (h1 : nextss g visited ⊆ stack.toFinset ∪ visited.toFinset.toSet) :
  nextss g (dfs_aux g stack visited) ⊆ (dfs_aux g stack visited).toFinset.toSet :=
  by
    induction stack, visited using dfs_aux.induct g
    case _ visited =>
      simp at h1
      simp only [dfs_aux]
      simp
      exact h1
    case _ visited x stack c1 ih =>
      simp only [dfs_aux]
      simp only [if_pos c1]
      apply ih
      trans ↑(x :: stack).toFinset ∪ ↑visited.toFinset
      · exact h1
      · simp only [List.toFinset_cons, Finset.coe_insert]
        simp only [Set.insert_union]

        have s1 : x ∈ (stack.toFinset.toSet ∪ visited.toFinset.toSet) :=
        by { simp; right; exact c1 }

        obtain s2 := Set.insert_eq_of_mem s1
        simp only [s2]
        simp
    case _ visited x stack c1 ih =>
      simp only [dfs_aux]
      simp only [if_neg c1]
      apply ih
      simp only [nextss_cons]
      simp only [Set.union_subset_iff]
      constructor
      · simp only [List.toFinset_append, Finset.coe_union]
        apply Set.subset_union_of_subset_left
        apply Set.subset_union_left
      · simp only [List.toFinset_cons] at h1
        simp at h1

        simp only [List.toFinset_cons]
        simp only [List.toFinset_append, Finset.coe_union, List.toFinset_cons, Set.union_insert]
        simp only [Set.union_assoc]
        apply Set.subset_union_of_subset_right

        have s1 : (insert x stack.toFinset.toSet) ∪ visited.toFinset.toSet = stack.toFinset.toSet ∪ (insert x visited.toFinset).toSet := by aesop
        simp only [<- s1]

        simp
        exact h1


lemma nextss_closed_dfs
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node) :
  nextss g (dfs_aux g stack []) ⊆ (dfs_aux g stack []).toFinset.toSet :=
  by
    apply nextss_closed_dfs'
    simp only [nextss]
    simp


inductive refl_trans_closure
  {α : Type}
  [DecidableEq α]
  (r : Set (α × α))
  (S : Set α) :
  Set α
  | base
    (x : α) :
    x ∈ S →
    refl_trans_closure r S x

  | step
    (x y : α) :
    (x, y) ∈ r →
    refl_trans_closure r S x →
    refl_trans_closure r S y


def relation_image
  {α : Type}
  [DecidableEq α]
  (r : Set (α × α))
  (S : Set α) :
  Set α :=
  {y | ∃ x, x ∈ S ∧ (x, y) ∈ r}


lemma image_closed_trancl
  {α : Type}
  [DecidableEq α]
  (r : Set (α × α))
  (S : Set α)
  (h1 : relation_image r S ⊆ S) :
  refl_trans_closure r S = S :=
  by
    simp only [relation_image] at h1
    have s1 : ∀ (x y : α), x ∈ S → (x, y) ∈ r → y ∈ S :=
    by
      intro x y a1 a2
      apply Set.mem_of_subset_of_mem h1
      simp
      apply Exists.intro x
      tauto
    ext a
    constructor
    · intro a1
      induction a1
      case _ x _ ih =>
        exact ih
      case _ x y ih_1 _ ih_3 =>
        exact s1 x y ih_3 ih_1
    · intro a1
      apply refl_trans_closure.base
      exact a1


/--
  `reachable g xs` := The reflexive transitive closure of `xs` under `g`. The union of the nodes that are reachable from each node in `xs` through a sequence of zero or more edges in `g`.
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
    (e : (Node × Node)) :
    e ∈ g →
    reachable g xs e.fst →
    reachable g xs e.snd


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
      apply Set.mem_of_subset_of_mem h1
      exact ih
    case step e ih_1 _ ih_3 =>
      apply reachable.step e ih_1 ih_3


lemma refl_trans_closure_eq_reachable
  {α : Type}
  [DecidableEq α]
  (g : Graph α)
  (xs : List α) :
  refl_trans_closure g.toFinset.toSet xs.toFinset.toSet = reachable g xs :=
  by
    ext a
    constructor
    · intro a1
      induction a1
      case _ x ih =>
        simp at ih
        exact reachable.base x ih
      case _ x y ih_1 _ ih_3 =>
        simp at ih_1
        apply reachable.step (x, y) ih_1 ih_3
    · intro a1
      induction a1
      case _ x ih =>
        simp
        exact refl_trans_closure.base x ih
      case _ e ih_1 _ ih_3 =>
        apply refl_trans_closure.step e.1
        · simp
          exact ih_1
        · exact ih_3


lemma reachable_closed_dfs
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (stack : List Node) :
  reachable g stack ⊆ (dfs_aux g stack []).toFinset.toSet :=
  by
    have s1 : reachable g stack ⊆ reachable g (dfs_aux g stack []) :=
    by
      apply reachable_mono g stack (dfs_aux g stack [])
      exact next_subset_dfs g stack []

    have s2 : reachable g (dfs_aux g stack []) = (dfs_aux g stack []).toFinset.toSet :=
    by
      have s3 : relation_image g.toFinset.toSet (dfs_aux g stack []).toFinset.toSet ⊆ (dfs_aux g stack []).toFinset.toSet :=
      by
        simp only [relation_image]
        obtain s4 := nextss_closed_dfs g stack
        simp only [nextss] at s4
        aesop

      obtain s5 := image_closed_trancl g.toFinset.toSet (dfs_aux g stack []).toFinset.toSet
      specialize s5 s3

      rw [← s5]
      simp only [refl_trans_closure_eq_reachable]

    simp only [← s2]
    exact s1


lemma reachable_nexts
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (x : Node) :
  reachable g (nexts g x) ⊆ reachable g [x] :=
  by
    intro a a1
    induction a1
    case _ x y ih =>
      obtain s1 := nexts_set g x y
      apply reachable.step (x, y)
      · simp only [← s1]
        exact ih
      · simp
        apply reachable.base x
        simp
    case _ e ih_1 _ ih_3 =>
      apply reachable.step e ih_1 ih_3


--#lint
