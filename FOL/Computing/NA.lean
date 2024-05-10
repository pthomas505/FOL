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


partial
def breadth_first_traversal_aux
  {Vertex : Type}
  [DecidableEq Vertex]
  (edges : List (Vertex × Vertex))
  (visited : List Vertex)
  (queue : Std.Queue Vertex) :
  List Vertex :=
  match queue.dequeue? with
  | Option.some (current, queue) =>
    let frontier := (edges.filter (fun (e : Vertex × Vertex) => e.fst = current ∧ e.snd ∉ visited)).map Prod.snd

    breadth_first_traversal_aux edges (visited ++ frontier) (queue.enqueueAll frontier)
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
#eval breadth_first_traversal [(0, 1)] 0 = [0, 1]
#eval breadth_first_traversal [(0, 1), (1, 0)] 0 = [0, 1]
#eval breadth_first_traversal [(0, 1), (1, 2)] 0 = [0, 1, 2]
#eval breadth_first_traversal [(0, 1), (1, 2), (2, 0)] 0 = [0, 1, 2]
