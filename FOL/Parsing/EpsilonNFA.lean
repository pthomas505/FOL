import FOL.Parsing.DFT


set_option autoImplicit false


structure SymbolArrow
  (α : Type)
  (σ : Type) :
  Type :=
  (start_state : σ)
  (symbol : α)
  (stop_state_list : List σ)
  deriving Repr


structure EpsilonArrow
  (σ : Type) :
  Type :=
  (start_state : σ)
  (stop_state_list : List σ)
  deriving Repr


structure EpsilonNFA
  (α : Type)
  (σ : Type) :
  Type :=
  (symbol_arrow_list : List (SymbolArrow α σ))
  (epsilon_arrow_list : List (EpsilonArrow σ))
  (starting_state_list : List σ)
  (accepting_state_list : List σ)
  deriving Repr


def epsilon_arrow_list_to_graph
  {σ : Type} :
  List (EpsilonArrow σ) → Graph σ
  | [] => []
  | (hd :: tl) => (hd.start_state, hd.stop_state_list) :: epsilon_arrow_list_to_graph tl


def EpsilonNFA.epsilon_closure
  {α : Type}
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (state_list : List σ) :
  List σ :=
  dft (epsilon_arrow_list_to_graph e.epsilon_arrow_list) state_list


/--
  The accumulated stop states of all of the arrows in the list that have a start state and symbol matching the given state and symbol.
-/
def symbol_arrow_list_to_fun
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (symbol_arrow_list : List (SymbolArrow α σ))
  (start_state : σ)
  (symbol : α) :
  List σ :=
  (symbol_arrow_list.filterMap (fun (arrow : SymbolArrow α σ) =>
    if arrow.start_state = start_state ∧ arrow.symbol = symbol
    then Option.some arrow.stop_state_list
    else Option.none)).join.dedup


example : symbol_arrow_list_to_fun ([] : List (SymbolArrow Char Nat)) 0 'a' = [] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩] 0 'a' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩] 0 'b' = [] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩] 0 'a' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩] 0 'b' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩] 0 'a' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩] 0 'b' = [2] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'a', [2]⟩] 0 'a' = [1, 2] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'a', [1]⟩] 0 'a' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'a', [1]⟩, ⟨0, 'a', [2]⟩] 0 'a' = [1, 2] := by rfl


/--
  `EpsilonNFA.eval_one e l c` := Returns the list of states that the nondeterministic automaton `e` transitions to if it starts at the list of states `l` and consumes the symbol `c`.
-/
def EpsilonNFA.eval_one
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (state_list : List σ)
  (symbol : α) :
  List σ :=
  e.epsilon_closure (state_list.map (fun (state : σ) => (symbol_arrow_list_to_fun e.symbol_arrow_list) state symbol)).join.dedup


def EpsilonNFA.eval_from
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (starting_state_list : List σ)
  (input : List α) :
  List σ :=
  List.foldl e.eval_one (e.epsilon_closure starting_state_list) input


def EpsilonNFA.eval
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (input : List α) :
  List σ :=
  e.eval_from e.starting_state_list input


def EpsilonNFA.accepts
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (input : List α) :
  Prop :=
  ∃ (s : σ), s ∈ e.eval input ∧ s ∈ e.accepting_state_list


instance
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (input : List α) :
  Decidable (e.accepts input) :=
  by
  induction input
  all_goals
    simp only [EpsilonNFA.accepts]
    infer_instance



example : EpsilonNFA.eval_from ⟨ [⟨0, 'a', [1]⟩], [⟨0, [1]⟩], [0], [1] ⟩ [] ([] : List Char) = [] := by rfl

example : EpsilonNFA.eval ⟨ [], [], [0], [1] ⟩ ([] : List Char) = [0] := by rfl

example : EpsilonNFA.eval ⟨ [], [], [0], [1] ⟩ ['a'] = [] := by rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩], [], [0], [1] ⟩ ['a'] = [1] := by rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩], [], [0], [1] ⟩ ['b'] = [] := by rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩], [], [0], [1] ⟩ ['a'] = [1] := by rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩], [], [0], [1] ⟩ ['b'] = [1] := by rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩], [], [0], [1] ⟩ ['a'] = [1] := by rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩], [], [0], [1] ⟩ ['b'] = [2] := by rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'a', [2]⟩], [], [0], [1] ⟩ ['a'] = [2, 1] := by rfl

example : EpsilonNFA.eval ⟨ [], [⟨ 0, [1] ⟩], [0], [1] ⟩ ([] : List Char) = [1, 0] := by rfl

example : EpsilonNFA.eval ⟨ [], [⟨ 0, [1]⟩], [0], [1] ⟩ ['a'] = [] := by rfl


-------------------------------------------------------------------------------


structure AbstractEpsilonNFA
  (α : Type)
  (σ : Type) :
  Type :=
  (symbol : σ → α → σ → Prop)
  (epsilon : σ → σ → Prop)
  (start : σ → Prop)
  (accepting : σ → Prop)


inductive AbstractEpsilonNFA.Eval
  {α σ : Type}
  (M : AbstractEpsilonNFA α σ) :
  σ → List α → Prop
  | eps
    {s s' : σ}
    {as : List α} :
    M.epsilon s s' →
    Eval M s' as →
    Eval M s as

  | sym
    {s s' : σ}
    {a : α}
    {as : List α} :
    M.symbol s a s' →
    Eval M s' as →
    Eval M s (a :: as)

  | accept
    {s : σ} :
    M.accepting s →
    Eval M s []


def AbstractEpsilonNFA.Accepts
  {α : Type}
  {σ : Type}
  (M : AbstractEpsilonNFA α σ)
  (as : List α) :
  Prop :=
  ∃ (s : σ), M.start s ∧ M.Eval s as


def EpsilonNFA.toAbstract
  {α : Type}
  {σ : Type}
  (M : EpsilonNFA α σ) :
  AbstractEpsilonNFA α σ :=
  {
    symbol := fun (start_state : σ) (symbol : α) (stop_state : σ) => ∃ (stop_state_list : List σ), ⟨start_state, symbol, stop_state_list⟩ ∈ M.symbol_arrow_list ∧ stop_state ∈ stop_state_list,

    epsilon := fun (start_state : σ) (stop_state : σ) => ∃ (stop_state_list : List σ), ⟨start_state, stop_state_list⟩ ∈ M.epsilon_arrow_list ∧ stop_state ∈ stop_state_list,

    start := fun (s : σ) => s ∈ M.starting_state_list,

    accepting := fun (s : σ) => s ∈ M.accepting_state_list
  }


def EpsilonNFA.eval_one'
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (state_list : List σ)
  (symbol : α) :
  List σ :=
  (state_list.map (fun (state : σ) => (symbol_arrow_list_to_fun e.symbol_arrow_list) state symbol)).join.dedup


theorem EpsilonNFA.eval_one'_def
  {α : Type} [DecidableEq α] {σ : Type} [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (state_list : List σ)
  (symbol : α) {s} :
  s ∈ e.eval_one' state_list symbol ↔
  (∃ a ∈ state_list, s ∈ symbol_arrow_list_to_fun e.symbol_arrow_list a symbol) := by simp [eval_one']


theorem EpsilonNFA.eval_one'_iff {α σ} [DecidableEq α] [DecidableEq σ]
    (M : EpsilonNFA α σ) {S s' a} :
    s' ∈ M.eval_one' S a ↔ (∃ s ∈ S, M.toAbstract.symbol s a s') := by
  simp [eval_one', toAbstract, symbol_arrow_list_to_fun]
  constructor
  · rintro ⟨_, h1, _, ⟨⟨⟩, h2, ⟨rfl, rfl⟩, rfl⟩, h3⟩
    exact ⟨_, h1, _, h2, h3⟩
  · rintro ⟨_, h1, _, h2, h3⟩
    exact ⟨_, h1, _, ⟨_, h2, ⟨rfl, rfl⟩, rfl⟩, h3⟩


@[simp]
theorem EpsilonNFA.eval_from_nil
  {α : Type} [DecidableEq α] {σ : Type} [DecidableEq σ]
  (e : EpsilonNFA α σ) (S : List σ) :
  e.eval_from S [] = e.epsilon_closure S := rfl

@[simp]
theorem EpsilonNFA.eval_from_cons
  {α : Type} [DecidableEq α] {σ : Type} [DecidableEq σ]
  (e : EpsilonNFA α σ) (S : List σ) (a as) :
  e.eval_from S (a :: as) = e.eval_from (e.eval_one' (e.epsilon_closure S) a) as := rfl


abbrev AbstractEpsilonNFA.EpsilonClosure {α σ} (M : AbstractEpsilonNFA α σ) :=
  Relation.ReflTransGen M.epsilon


theorem EpsilonNFA.epsilon_closure_iff
  {α : Type} [DecidableEq α] {σ : Type} [DecidableEq σ]
  (e : EpsilonNFA α σ) {S s'} :
  s' ∈ e.epsilon_closure S ↔ ∃ s ∈ S, e.toAbstract.EpsilonClosure s s' := by
  simp [epsilon_closure, dft_iff]
  congr! with a b c
  simp [toAbstract]
  induction e.epsilon_arrow_list <;> simp [*, epsilon_arrow_list_to_graph, or_and_right, exists_or]
  apply or_congr_left <| exists_congr fun a => and_congr_left fun _ => ?_
  constructor <;> [rintro ⟨rfl, rfl⟩; rintro rfl] <;> [rfl; constructor <;> rfl]


theorem EpsilonNFA.eval_from_iff {α σ} [DecidableEq α] [DecidableEq σ]
    (M : EpsilonNFA α σ) {S input} :
    (∃ s ∈ M.eval_from S input, s ∈ M.accepting_state_list) ↔
    (∃ s ∈ S, M.toAbstract.Eval s input) := by
  induction input generalizing S with simp
  | nil =>
    simp [epsilon_closure_iff]
    constructor
    · intro ⟨s, ⟨s', h1, h2⟩, h3⟩
      refine ⟨_, h1, ?_⟩
      clear h1
      induction h2 using Relation.ReflTransGen.head_induction_on with
      | refl => exact .accept h3
      | head h _ ih => exact .eps h ih
    · intro ⟨s, h1, h2⟩
      obtain ⟨s', h3, h4⟩ : ∃ s', M.toAbstract.EpsilonClosure s s' ∧ s' ∈ M.accepting_state_list := by
        clear h1; generalize e : [] = l at h2
        induction h2 with cases e
        | accept h' => exact ⟨_, .refl, h'⟩
        | eps h1 _ ih =>
          have ⟨s', h3, h4⟩ := ih rfl
          exact ⟨_, .head h1 h3, h4⟩
      exact ⟨_, ⟨_, h1, h3⟩, h4⟩
  | cons a as IH =>
    simp [IH, epsilon_closure_iff, eval_one'_iff]
    constructor
    · intro ⟨s₁, ⟨s₂, ⟨s₃, h1, h2⟩, h3⟩, h4⟩
      refine ⟨_, h1, ?_⟩
      clear h1
      induction h2 using Relation.ReflTransGen.head_induction_on with
      | refl => exact .sym h3 h4
      | head h _ ih => exact .eps h ih
    · intro ⟨s, h1, h2⟩
      obtain ⟨s₁, s₂, h3, h4, h5⟩ :
          ∃ s₁ s₂, M.toAbstract.EpsilonClosure s s₂ ∧
            M.toAbstract.symbol s₂ a s₁ ∧ M.toAbstract.Eval s₁ as := by
        clear h1; generalize e : a::as = l at h2
        induction h2 with cases e
        | sym h1 h2 => exact ⟨_, _, .refl, h1, h2⟩
        | eps h1 _ ih =>
          have ⟨s₁, s₂, h3, h4, h5⟩ := ih rfl
          exact ⟨_, _, .head h1 h3, h4, h5⟩
      exact ⟨_, ⟨_, ⟨_, h1, h3⟩, h4⟩, h5⟩


theorem EpsilonNFA.accepts_iff {α σ} [DecidableEq α] [DecidableEq σ]
    (M : EpsilonNFA α σ) {input} : M.accepts input ↔ M.toAbstract.Accepts input := by
  simp [accepts, eval]; rw [EpsilonNFA.eval_from_iff]; rfl







def EpsilonNFA.map
  {α : Type}
  {σ₁ σ₂ : Type}
  (f : σ₁ → σ₂)
  (e : EpsilonNFA α σ₁) :
  EpsilonNFA α σ₂ :=
  {
    symbol_arrow_list := e.symbol_arrow_list.map (fun (arrow : SymbolArrow α σ₁) => ⟨
      f arrow.start_state,
      arrow.symbol,
      arrow.stop_state_list.map f
    ⟩),
    epsilon_arrow_list := e.epsilon_arrow_list.map (fun (arrow : EpsilonArrow σ₁) => ⟨
      f arrow.start_state,
      arrow.stop_state_list.map f
    ⟩),
    starting_state_list := e.starting_state_list.map f,
    accepting_state_list := e.accepting_state_list.map f
  }


def AbstractEpsilonNFA.comap
  {α : Type}
  {σ₁ σ₂ : Type}
  (f_inv : σ₂ → σ₁)
  (e : AbstractEpsilonNFA α σ₁) :
  AbstractEpsilonNFA α σ₂ :=
  {
    symbol := fun (start_state : σ₂) (symbol : α) (stop_state: σ₂) =>
    (e.symbol (f_inv start_state) symbol (f_inv stop_state)),

    epsilon := fun (start_state : σ₂) (stop_state: σ₂) =>
    (e.epsilon (f_inv start_state) (f_inv stop_state)),

    start := fun (state : σ₂) => e.start (f_inv state),

    accepting := fun (state : σ₂) => e.accepting (f_inv state)
  }


def AbstractEpsilonNFA.map
  {α : Type}
  {σ₁ σ₂ : Type}
  (f : σ₁ → σ₂)
  (e : AbstractEpsilonNFA α σ₁) :
  AbstractEpsilonNFA α σ₂ :=
  {
    symbol :=
      fun (start_state : σ₂) (symbol : α) (stop_state: σ₂) =>
        ∃ (start_state' : σ₁) (stop_state': σ₁),
          f start_state' = start_state ∧
          f stop_state' = stop_state ∧
          e.symbol start_state' symbol stop_state',

    epsilon :=
      fun (start_state : σ₂) (stop_state: σ₂) =>
        ∃ (start_state' : σ₁) (stop_state': σ₁),
          f start_state' = start_state ∧
          f stop_state' = stop_state ∧
          e.epsilon start_state' stop_state',

    start :=
      fun (state : σ₂) =>
        ∃ (state' : σ₁), f state' = state ∧ e.start state',

    accepting :=
      fun (state : σ₂) =>
        ∃ (state' : σ₁), f state' = state ∧ e.accepting state'
  }