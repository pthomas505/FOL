import FOL.Computing.RegExp


set_option autoImplicit false


-- Take the set of strings in S that start with u and then remove the u from them.

/--
  The Brzozowski derivative u^{-1}S of a set S of strings and a string u is the set of all strings obtainable from a string in S by cutting off the prefix u.
-/
def Brzozowski_derivative
  (S : Set (String))
  (u : String) :
  Set String :=
  { v : String | u ++ v ∈ S }


/-
The derivative, D_a(r) of a regular expression r by alphabet letter a is defined as D_a(r) = {w : aw ∈ r}. The derivative represents the set of continuations after letter a that the regular expression r can match.
-/


def RegExp.delta
  {α : Type} :
  RegExp α → RegExp α
  | char _ => RegExp.zero
  | epsilon => RegExp.epsilon
  | zero => RegExp.zero
  | union r s => RegExp.union r.delta s.delta
  | concat r s => RegExp.concat r.delta s.delta
  | closure _ => RegExp.epsilon


def RegExp.Brzozowski_derivative_set
  {α : Type}
  [DecidableEq α]
  (r : RegExp α)
  (a : α) :
  Set (List α) :=
  {w : List α | (a :: w) ∈ r.languageOf}


def RegExp.Brzozowski_derivative
  {α : Type}
  [DecidableEq α]
  (a : α) :
  RegExp α → RegExp α
  | char b => if a = b then RegExp.epsilon else RegExp.zero
  | epsilon => RegExp.zero
  | zero => RegExp.zero
  | union r s => RegExp.union (r.Brzozowski_derivative a) (s.Brzozowski_derivative a)
  | concat r s => RegExp.union (RegExp.concat (r.Brzozowski_derivative a) s) (RegExp.concat r.delta (s.Brzozowski_derivative a))
  | closure r => RegExp.concat (r.Brzozowski_derivative a) r.closure


example
  {α : Type}
  [DecidableEq α]
  (r : RegExp α)
  (a : α) :
  RegExp.Brzozowski_derivative_set r a = (r.Brzozowski_derivative a).languageOf :=
  by
  ext cs
  induction r
  case char a b =>
    simp only [RegExp.Brzozowski_derivative_set]
    simp only [RegExp.Brzozowski_derivative]
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
    simp only [RegExp.Brzozowski_derivative_set]
    simp only [RegExp.Brzozowski_derivative]
    simp only [RegExp.languageOf]
    simp
  case zero =>
    simp only [RegExp.Brzozowski_derivative_set]
    simp only [RegExp.Brzozowski_derivative]
    simp only [RegExp.languageOf]
    simp
  case union r s r_ih s_ih =>
    simp only [RegExp.languageOf]
    simp
    simp only [← r_ih]
    simp only [← s_ih]
    simp only [RegExp.Brzozowski_derivative_set]
    simp only [RegExp.languageOf]
    simp
  case concat r s r_ih s_ih =>
    simp only [RegExp.Brzozowski_derivative_set] at r_ih
    simp at r_ih

    simp only [RegExp.Brzozowski_derivative_set] at s_ih
    simp at s_ih

    simp only [RegExp.Brzozowski_derivative_set]
    simp

    simp only [RegExp.Brzozowski_derivative]

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
    simp only [RegExp.Brzozowski_derivative_set] at r_ih
    simp at r_ih

    simp only [RegExp.Brzozowski_derivative_set]
    simp only [RegExp.Brzozowski_derivative]
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
