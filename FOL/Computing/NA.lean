import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Defs


structure Step
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ] :
  Type :=
  (beginState : σ)
  (symbol : α)
  (endStateList : List σ)
  deriving Repr


structure EpsilonStep
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ] :
  Type :=
  (beginState : σ)
  (endStateList : List σ)
  deriving Repr


structure NDFA
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ] :
  Type :=
  (stepList : List (Step α σ))
  (epsilonStepList : List (EpsilonStep α σ))
  (startingStateList : List σ)
  (acceptingStateList : List σ)
  deriving Repr


-- https://www.isa-afp.org/entries/Depth-First-Search.html


abbrev Graph
  (Node : Type)
  [DecidableEq Node] :
  Type :=
  List (Node × Node)


/--
  nexts g x := The image of x under g if g is treated as a binary relation.
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
  nextss g xs := The image of xs under g if g is treated as a binary relation.
-/
def nextss
  {Node : Type}
  [DecidableEq Node]
  (g : Graph Node)
  (xs : List Node) :
  Set Node :=
  {y | ∃ x, x ∈ xs ∧ (x, y) ∈ g}


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
  by simp only [dfs_aux]


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
  by sorry


partial
def breadth_first_traversal_aux
  {Vertex : Type}
  [DecidableEq Vertex]
  (edges : List (Vertex × Vertex))
  (visited : List Vertex)
  (queue : Std.Queue Vertex) :
  List Vertex :=
  match queue.dequeue? with
  | Option.some (current, next) =>
    let frontier := (edges.filter (fun (e : Vertex × Vertex) => e.fst = current ∧ e.snd ∉ visited)).map Prod.snd

    breadth_first_traversal_aux edges (visited ++ frontier) (next.enqueueAll frontier)
  | Option.none => visited


/--
  `breadth_first_traversal E start` := All of the vertices that are reachable from the vertex `start` by following a sequence of zero or more edges in `E`.
-/
def breadth_first_traversal
  {Vertex : Type}
  [DecidableEq Vertex]
  (edges : List (Vertex × Vertex))
  (start : Vertex) :
  List Vertex :=
  breadth_first_traversal_aux edges [start] (Std.Queue.empty.enqueue start)


#eval breadth_first_traversal [] 0 = [0]
#eval breadth_first_traversal [(0, 0)] 0 = [0]
#eval breadth_first_traversal [(1, 1)] 0 = [0]
#eval breadth_first_traversal [(0, 1)] 0 = [0, 1]
#eval breadth_first_traversal [(0, 1), (1, 1)] 0 = [0, 1]
#eval breadth_first_traversal [(0, 1), (1, 0)] 0 = [0, 1]
#eval breadth_first_traversal [(0, 1), (1, 2)] 0 = [0, 1, 2]
#eval breadth_first_traversal [(0, 1), (1, 2), (2, 0)] 0 = [0, 1, 2]
