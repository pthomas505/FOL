import FOL.Parsing.DFA
import FOL.Parsing.RegExp


set_option autoImplicit false


/-
  https://people.cs.uchicago.edu/~jhr/papers/2009/jfp-re-derivatives.pdf
-/

/-
We assume a finite alphabet Σ of symbols and use Σ∗ to denote the set of all finite strings over Σ. We use a, b, c, etc. to represent symbols and u, v, w to represent strings. The empty string is denoted by ε. A language of Σ is a (possibly infinite) set of finite strings L ⊆ Σ∗.
-/

/-
  This formalization uses α for Σ since Σ is reserved in Lean.
-/

-- Str α is Σ∗.
abbrev Str (α : Type) : Type := List α

-- Language α is L.
abbrev Language (α : Type) : Type := Set (Str α)


/--
Definition 3.1
The derivative of a language L ⊆ Σ∗ with respect to a string u ∈ Σ∗ is defined to be ∂u L = {v | u · v ∈ L}.
-/
def derivative
  {α : Type}
  (S : Set (Str α))
  (u : Str α) :
  Set (Str α) :=
  { v : Str α | u ++ v ∈ S }


/--
  The regular languages are those languages that can be described by regular expressions.
-/
def Language.isRegular
  {α : Type}
  (L : Language α) :
  Prop :=
  ∃ (e : RegExp α), L = e.languageOf


/-
We say that an RE r is nullable if the language it defines contains the
empty string, that is if ε ∈ L[[r]].
-/

def RegExp.is_nullable
  {α : Type} :
  RegExp α → Prop
  | char _ => False
  | epsilon => True
  | zero => False
  | union r s => r.is_nullable ∨ s.is_nullable
  | concat r s => r.is_nullable ∧ s.is_nullable
  | closure _ => True


instance (α : Type) (e : RegExp α) : Decidable e.is_nullable :=
  by
    induction e
    all_goals
      simp only [RegExp.is_nullable]
      infer_instance


lemma is_nullable_def
  {α : Type}
  (e : RegExp α) :
  e.is_nullable ↔ [] ∈ e.languageOf :=
  by
    induction e
    case char a =>
      simp only [RegExp.languageOf]
      simp only [RegExp.is_nullable]
      simp
    case epsilon =>
      simp only [RegExp.languageOf]
      simp only [RegExp.is_nullable]
      simp
    case zero =>
      simp only [RegExp.languageOf]
      simp only [RegExp.is_nullable]
      simp
    case union r s r_ih s_ih =>
      simp only [RegExp.languageOf]
      simp only [RegExp.is_nullable]
      simp
      simp only [r_ih]
      simp only [s_ih]
    case concat r s r_ih s_ih =>
      simp only [RegExp.languageOf]
      simp only [RegExp.is_nullable]
      simp
      simp only [r_ih]
      simp only [s_ih]
    case closure e _ =>
      simp only [equiv_language_of_closure]
      simp only [RegExp.languageOf]
      simp only [RegExp.is_nullable]
      simp


def RegExp.delta
  {α : Type} :
  RegExp α → RegExp α
  | char _ => RegExp.zero
  | epsilon => RegExp.epsilon
  | zero => RegExp.zero
  | union r s => RegExp.union r.delta s.delta
  | concat r s => RegExp.concat r.delta s.delta
  | closure _ => RegExp.epsilon


lemma language_of_delta
  (α : Type)
  (e : RegExp α) :
  e.delta.languageOf =
    if e.is_nullable
    then RegExp.epsilon.languageOf
    else RegExp.zero.languageOf :=
  by
    induction e
    case char a =>
      simp only [RegExp.is_nullable]
      simp only [RegExp.languageOf]
      simp
    case epsilon =>
      simp only [RegExp.is_nullable]
      simp only [RegExp.languageOf]
      simp
    case zero =>
      simp only [RegExp.is_nullable]
      simp only [RegExp.languageOf]
      simp
    case union r s r_ih s_ih =>
      simp only [RegExp.languageOf] at r_ih
      simp only [RegExp.languageOf] at s_ih

      simp only [RegExp.languageOf]
      simp only [r_ih]
      simp only [s_ih]
      simp only [RegExp.is_nullable]
      ext cs
      simp
      tauto
    case concat r s r_ih s_ih =>
      simp only [RegExp.languageOf] at r_ih
      simp only [RegExp.languageOf] at s_ih

      simp only [RegExp.languageOf]
      simp only [r_ih]
      simp only [s_ih]
      simp only [RegExp.is_nullable]
      ext cs
      simp
      constructor
      · intro a1
        apply Exists.elim a1
        intro xs a2
        clear a1
        cases a2
        case _ a2_left a2_right =>
          cases a2_left
          case _ a2_left_left a2_left_right =>
            apply Exists.elim a2_right
            intro ys a3
            clear a2_right
            cases a3
            case _ a3_left a3_right =>
              cases a3_left
              case _ a3_left_left a3_left_right =>
                simp only [a2_left_left]
                simp only [a3_left_left]
                simp only [a2_left_right] at a3_right
                simp only [a3_left_right] at a3_right
                simp at a3_right
                tauto
      · intro a1
        cases a1
        case _ a1_left a2_right =>
          cases a1_left
          case _ a1_left_left a1_left_right =>
            simp only [a1_left_left]
            simp only [a1_left_right]
            simp
            simp only [a2_right]
    case closure e _ =>
      simp only [RegExp.languageOf]
      simp only [RegExp.is_nullable]
      simp


example
  (α : Type)
  (e : RegExp α) :
  e.delta.languageOf ⊆ e.languageOf :=
  by
    simp only [language_of_delta]
    simp only [RegExp.languageOf]
    split_ifs
    case _ c1 =>
      simp only [is_nullable_def] at c1
      simp
      exact c1
    case _ c1 =>
      simp


example
  (α : Type)
  (e : RegExp α)
  (h1 : e.is_nullable) :
  e.delta.is_nullable :=
  by
    simp only [is_nullable_def] at h1

    simp only [is_nullable_def]
    simp only [language_of_delta]
    simp only [RegExp.languageOf]
    simp
    simp only [is_nullable_def]
    exact h1


example
  (α : Type)
  (e : RegExp α)
  (cs : List α)
  (h1 : cs ∈ e.delta.languageOf) :
  cs = [] :=
  by
    simp only [language_of_delta] at h1
    simp only [RegExp.languageOf] at h1
    simp at h1
    tauto


example
  (α : Type)
  (R : RegExp α)
  (cs : List α) :
  cs ∈ R.delta.languageOf ↔ R.is_nullable ∧ cs = [] :=
  by
    simp only [is_nullable_def]
    simp only [language_of_delta]
    simp only [RegExp.languageOf]
    simp
    intro _
    simp only [is_nullable_def]


/-
The derivative, D_a(r) of a regular expression r by alphabet letter a is defined as D_a(r) = {w : aw ∈ r}. The derivative represents the set of continuations after letter a that the regular expression r can match.
-/
def RegExp.derivative_set
  {α : Type}
  [DecidableEq α]
  (r : RegExp α)
  (a : α) :
  Set (List α) :=
  {w : List α | (a :: w) ∈ r.languageOf}


def RegExp.derivative
  {α : Type}
  [DecidableEq α]
  (a : α) :
  RegExp α → RegExp α
  | char b =>
      if a = b
      then RegExp.epsilon
      else RegExp.zero

  | epsilon => RegExp.zero

  | zero => RegExp.zero

  | union r s => RegExp.union (r.derivative a) (s.derivative a)

  | concat r s =>
      if r.is_nullable
      then RegExp.concat (r.derivative a) s
      else RegExp.concat r.delta (s.derivative a)

  | closure r => RegExp.concat (r.derivative a) r.closure


lemma derivative_def
  {α : Type}
  [DecidableEq α]
  (a : α)
  (w : List α)
  (e : RegExp α) :
  w ∈ (e.derivative a).languageOf ↔ a :: w ∈ e.languageOf :=
  by
    induction e generalizing w
    case char b =>
      simp only [RegExp.derivative]
      split_ifs
      case pos c1 =>
        simp only [c1]
        simp only [RegExp.languageOf]
        simp
      case neg c1 =>
        simp only [RegExp.languageOf]
        simp
        intro a1
        contradiction
    case epsilon =>
      simp only [RegExp.derivative]
      simp only [RegExp.languageOf]
      simp
    case zero =>
      simp only [RegExp.derivative]
      simp only [RegExp.languageOf]
      simp
    case union r s r_ih s_ih =>
      simp only [RegExp.derivative]
      simp only [RegExp.languageOf]
      specialize r_ih w
      specialize s_ih w
      simp
      tauto
    case concat r s r_ih s_ih =>
      simp only [RegExp.derivative]
      split_ifs
      case pos c1 =>
        simp only [RegExp.languageOf]
        simp
        constructor
        · intro a1
          apply Exists.elim a1
          intro xs a2
          clear a1
          cases a2
          case _ a2_left a2_right =>
            apply Exists.elim a2_right
            intro ys a3
            clear a2_right
            cases a3
            case _ a3_left a3_right =>
              apply Exists.intro (a :: xs)
              constructor
              · simp only [← r_ih]
                exact a2_left
              · apply Exists.intro ys
                constructor
                · exact a3_left
                · simp only [← a3_right]
                  simp
        · intro a1
          apply Exists.elim a1
          intro xs a2
          clear a1
          cases a2
          case _ a2_left a2_right =>
            apply Exists.elim a2_right
            intro ys a3
            clear a2_right
            cases a3
            case _ a3_left a3_right =>
              simp only [is_nullable_def] at c1

              apply Exists.intro (a :: w)
              constructor
              · simp only [← a3_right]
                sorry
              · apply Exists.intro []
                sorry
    case closure e ih =>
      simp only [RegExp.derivative]
      simp only [RegExp.languageOf]
      simp
      sorry


def RegExp.is_match
  {α : Type}
  [DecidableEq α]
  (e : RegExp α) :
  List α → Prop
  | [] => e.is_nullable
  | hd :: tl => (e.derivative hd).is_match tl


example
  {α : Type}
  [DecidableEq α]
  (e : RegExp α)
  (input : List α) :
  e.is_match input ↔ input ∈ e.languageOf :=
  by
    induction input generalizing e
    case nil =>
      simp only [RegExp.is_match]
      exact is_nullable_def e
    case cons hd tl ih =>
      simp only [RegExp.is_match]
      simp only [ih]
      exact derivative_def hd tl e


lemma lem_3_1
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (a : α)
  (h1 : Language.isRegular L) :
  Language.isRegular (derivative L [a]) :=
  by
    simp only [Language.isRegular] at h1
    apply Exists.elim h1
    intro r a1
    clear h1
    subst a1
    simp only [Language.isRegular]
    simp only [derivative]
    simp
    apply Exists.intro (r.derivative a)
    ext cs
    simp

    induction r
    case h.char b =>
      simp only [RegExp.derivative]
      simp only [RegExp.languageOf]
      simp
      split_ifs
      case pos c1 =>
        tauto
      case neg c1 =>
        tauto
    case h.epsilon =>
      simp only [RegExp.derivative]
      simp only [RegExp.languageOf]
      simp
    case h.zero =>
      simp only [RegExp.derivative]
      simp only [RegExp.languageOf]
      simp
    case h.union r s r_ih s_ih =>
      simp only [RegExp.derivative]
      simp only [RegExp.languageOf]
      simp
      tauto
    case concat r s r_ih s_ih =>
      simp only [RegExp.derivative]
      simp only [RegExp.languageOf]
      simp
      constructor
      · intro a1
        apply Exists.elim a1
        intro xs a2
        clear a1
        cases a2
        case _ a2_left a2_right =>
          apply Exists.elim a2_right
          intro ys a3
          clear a2_right
          cases a3
          case _ a3_left a3_right =>
            simp only [← a3_right] at r_ih
            simp only [← a3_right] at s_ih
            by_cases c1 : (∃ r_1 ∈ RegExp.languageOf α (RegExp.derivative a r), ∃ s_1 ∈ RegExp.languageOf α s, r_1 ++ s_1 = cs)
            case pos =>
              left
              exact c1
            case neg =>
              right
              simp at c1
              sorry
      · sorry
    case h.closure r ih =>
      simp only [RegExp.derivative]
      simp only [RegExp.languageOf]
      simp
      constructor
      case _ =>
        intro a1
        apply Exists.elim a1
        intro xs a2
        clear a1
        cases a2
        case _ a2_left a2_right =>
          sorry
      sorry




/-
Theorem 3.1
If L ⊆ Σ∗ is regular, then ∂u L is regular for all strings u ∈ Σ∗.
-/
theorem thm_3_1
  {α : Type}
  (L : Language α)
  (h1 : Language.isRegular L) :
  ∀ (u : Str α), Language.isRegular (derivative L u) :=
  by
    sorry




example
  {α : Type}
  [DecidableEq α]
  (r : RegExp α)
  (a : α) :
  RegExp.derivative_set r a = (r.derivative a).languageOf :=
  by
  ext cs
  induction r
  case char a b =>
    simp only [RegExp.derivative_set]
    simp only [RegExp.derivative]
    split_ifs
    case pos c1 =>
      simp only [RegExp.languageOf]
      simp
      intro _
      exact c1
    case neg c1 =>
      simp only [RegExp.languageOf]
      simp
      intro contra
      contradiction
  case epsilon =>
    simp only [RegExp.derivative_set]
    simp only [RegExp.derivative]
    simp only [RegExp.languageOf]
    simp
  case zero =>
    simp only [RegExp.derivative_set]
    simp only [RegExp.derivative]
    simp only [RegExp.languageOf]
    simp
  case union r s r_ih s_ih =>
    simp only [RegExp.languageOf]
    simp
    simp only [← r_ih]
    simp only [← s_ih]
    simp only [RegExp.derivative_set]
    simp only [RegExp.languageOf]
    simp
  case concat r s r_ih s_ih =>
    simp only [RegExp.derivative_set] at r_ih
    simp at r_ih

    simp only [RegExp.derivative_set] at s_ih
    simp at s_ih

    simp only [RegExp.derivative_set]
    simp

    simp only [RegExp.derivative]

    simp only [RegExp.languageOf]
    simp

    constructor
    · intro a1
      apply Exists.elim a1
      intro r' a2
      clear a1
      cases a2
      case _ a2_left a2_right =>
        apply Exists.elim a2_right
        intro s' a3
        clear a2_right
        cases a3
        case _ a3_left a3_right =>
          sorry
    · intro a1
      cases a1
      case _ a1_left =>
        apply Exists.elim a1_left
        intro r' a2
        clear a1_left
        cases a2
        case _ a2_left a2_right =>
          apply Exists.elim a2_right
          intro s' a3
          clear a2_right
          cases a3
          case _ a3_left a3_right =>
            sorry
      case _ a1_right =>
        sorry
  case closure r r_ih =>
    simp only [RegExp.derivative_set] at r_ih
    simp at r_ih

    simp only [RegExp.derivative_set]
    simp only [RegExp.derivative]
    simp only [RegExp.languageOf]
    simp
    constructor
    · intro a1
      apply Exists.elim a1
      intro rs a2
      clear a1
      cases a2
      case _ a2_left a2_right =>
        simp only [← a2_right] at r_ih
        cases r_ih
        case _ mp mpr =>
          cases rs
          case nil =>
            simp at a2_right
          case cons hd tl =>
            simp at a2_left
            cases a2_left
            case _ a2_left_left a2_left_right =>
              simp at a2_right
              apply Exists.intro cs
              sorry
    · sorry
