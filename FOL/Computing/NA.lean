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



-- Not efficient but simpler to understand.
partial
def simple_breadth_first_traversal_aux
  {Vertex : Type}
  [DecidableEq Vertex]
  (outside : List Vertex)
  (inside : List Vertex)
  (edges : List (Vertex × Vertex)) :
  List Vertex :=
  -- All of the vertices that are outside and adjacent to at least one vertex inside.
  let next : List Vertex := List.filter (fun (out : Vertex) => ∃ (b : Vertex), b ∈ inside ∧ (b, out) ∈ edges) outside
  if next = []
  then inside
  else simple_breadth_first_traversal_aux (outside \ next) (inside ∪ next) edges

/--
  `simple_breadth_first_traversal V E start` := All of the vertices in `V` that are reachable from the vertex `start` by following a sequence of zero or more edges in `E`.
-/
def simple_breadth_first_traversal
  {Vertex : Type}
  [DecidableEq Vertex]
  (vertices : List Vertex)
  (edges : List (Vertex × Vertex))
  (start : Vertex) :
  List Vertex :=
  simple_breadth_first_traversal_aux vertices [start] edges

#eval simple_breadth_first_traversal [0, 1, 2, 3] [(0, 1), (0, 2)] 0




partial
def breadth_first_traversal_aux
  {Vertex : Type}
  [DecidableEq Vertex]
  (outside : List Vertex)
  (boundary : List Vertex)
  (inside : List Vertex)
  (edges : List (Vertex × Vertex)) :
  List Vertex :=
  -- All of the vertices that are outside and adjacent to at least one vertex in the boundary.
  let next : List Vertex := List.filter (fun (out : Vertex) => ∃ (b : Vertex), b ∈ boundary ∧ (b, out) ∈ edges) outside
  if next = []
  then inside ∪ boundary
  else breadth_first_traversal_aux (outside \ next) next (inside ∪ next) edges

/--
  `breadth_first_traversal V E start` := All of the vertices in `V` that are reachable from the vertex `start` by following a sequence of zero or more edges in `E`.
-/
def breadth_first_traversal
  {Vertex : Type}
  [DecidableEq Vertex]
  (vertices : List Vertex)
  (edges : List (Vertex × Vertex))
  (start : Vertex) :
  List Vertex :=
  breadth_first_traversal_aux vertices [start] [start] edges

#eval breadth_first_traversal [0, 1, 2, 3] [(0, 1), (0, 1), (0, 2)] 0
