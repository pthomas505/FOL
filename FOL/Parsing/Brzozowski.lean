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

def RegExp.nullable
  {α : Type}
  (e : RegExp α) :
  Prop :=
  [] ∈ e.languageOf


def RegExp.delta
  {α : Type} :
  RegExp α → RegExp α
  | char _ => RegExp.zero
  | epsilon => RegExp.epsilon
  | zero => RegExp.zero
  | union r s => RegExp.union r.delta s.delta
  | concat r s => RegExp.concat r.delta s.delta
  | closure _ => RegExp.epsilon


example
  (α : Type)
  (R : RegExp α)
  (cs : List α) :
  cs ∈ R.delta.languageOf ↔ R.nullable ∧ cs = [] :=
  by
    induction R generalizing cs
    case char a =>
      simp only [RegExp.delta]
      simp only [RegExp.nullable]
      simp only [RegExp.languageOf]
      simp
    case epsilon =>
      simp only [RegExp.delta]
      simp only [RegExp.nullable]
      simp only [RegExp.languageOf]
      simp
    case zero =>
      simp only [RegExp.delta]
      simp only [RegExp.nullable]
      simp only [RegExp.languageOf]
      simp
    case union r s r_ih s_ih =>
      simp only [RegExp.nullable] at r_ih
      simp only [RegExp.nullable] at s_ih

      simp only [RegExp.delta]
      simp only [RegExp.nullable]
      simp only [RegExp.languageOf]
      simp

      specialize r_ih cs
      specialize s_ih cs
      tauto
    case concat r s r_ih s_ih =>
      simp only [RegExp.nullable] at r_ih
      simp only [RegExp.nullable] at s_ih

      simp only [RegExp.delta]
      simp only [RegExp.nullable]
      simp only [RegExp.languageOf]

      aesop
    case closure r _ =>
      simp only [RegExp.delta]
      simp only [RegExp.nullable]
      simp only [RegExp.languageOf]

      simp
      intro _
      apply Exists.intro []
      simp


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
    RegExp.union
      (RegExp.concat (r.derivative a) s)
      (RegExp.concat r.delta (s.derivative a))

  | closure r => RegExp.concat (r.derivative a) r.closure


lemma lem_3_1
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (h1 : Language.isRegular L)
  (a : α) :
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
