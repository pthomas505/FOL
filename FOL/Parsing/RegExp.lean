import Mathlib.Data.Finset.Basic


set_option autoImplicit false


inductive RegExp
  (α : Type) :
  Type
  | char : α → RegExp α
  | epsilon : RegExp α
  | zero : RegExp α
  | union : RegExp α → RegExp α → RegExp α
  | concat : RegExp α → RegExp α → RegExp α
  | closure : RegExp α → RegExp α
  deriving Repr


def RegExp.languageOf
  (α : Type) :
  RegExp α → Set (List α)
  | char x => { [x] }
  | epsilon => { [] }
  | zero => ∅
  | union R S => R.languageOf ∪ S.languageOf

  -- For each string r in L(R) and each string s in L(S), the string rs, the concatenation of strings r and s, is in L(RS).
  | concat R S => { r ++ s | (r ∈ R.languageOf) (s ∈ S.languageOf) }

  -- l is the concatenation of a list of strings, each of which is in L(R).
  | closure R => { l | ∃ rs : List (List α), (∀ (r : List α), r ∈ rs → r ∈ R.languageOf) ∧ rs.join = l }


example
  {α : Type}
  (R : RegExp α) :
  RegExp.languageOf α (RegExp.closure R) =
    RegExp.languageOf α (RegExp.union RegExp.epsilon (RegExp.concat R (RegExp.closure R))) :=
  by
    ext cs
    simp only [RegExp.languageOf]
    simp
    constructor
    · intro a1
      apply Exists.elim a1
      intro xs a2
      clear a1
      cases a2
      case _ a2_left a2_right =>
        simp only [← a2_right]
        cases xs
        case nil =>
          left
          simp
        case cons hd tl =>
          right
          simp at a2_left
          cases a2_left
          case _ a2_left_left a2_left_right =>
            apply Exists.intro hd
            tauto
    · intro a1
      cases a1
      case _ left =>
        apply Exists.intro []
        simp
        simp only [left]
      case _ right =>
        apply Exists.elim right
        intro xs a2
        clear right
        cases a2
        case _ a2_left a2_right =>
          apply Exists.elim a2_right
          intro ys a3
          clear a2_right
          cases a3
          case _ a3_left a3_right =>
            apply Exists.intro ([xs] ++ ys)
            simp
            tauto


example
  {α : Type}
  (R : RegExp α) :
  (RegExp.union R RegExp.zero).languageOf = R.languageOf ∧
    (RegExp.union RegExp.zero R).languageOf = R.languageOf :=
  by
  simp only [RegExp.languageOf]
  simp


example
  {α : Type}
  (R : RegExp α) :
  (RegExp.concat R RegExp.epsilon).languageOf = R.languageOf ∧
    (RegExp.concat RegExp.epsilon R).languageOf = R.languageOf :=
  by
  simp only [RegExp.languageOf]
  simp


example
  {α : Type}
  (R : RegExp α) :
  (RegExp.concat R RegExp.zero).languageOf = RegExp.zero.languageOf ∧
    (RegExp.concat RegExp.zero R).languageOf = RegExp.zero.languageOf :=
  by
  simp only [RegExp.languageOf]
  simp


example
  {α : Type}
  (R S : RegExp α) :
  (RegExp.union R S).languageOf = (RegExp.union S R).languageOf :=
  by
  simp only [RegExp.languageOf]
  exact Set.union_comm (RegExp.languageOf α R) (RegExp.languageOf α S)


example
  {α : Type}
  (R S T : RegExp α) :
  (RegExp.union (RegExp.union R S) T).languageOf =
    (RegExp.union R (RegExp.union S T)).languageOf :=
  by
  simp only [RegExp.languageOf]
  exact Set.union_assoc (RegExp.languageOf α R) (RegExp.languageOf α S) (RegExp.languageOf α T)


example
  {α : Type}
  (R S T : RegExp α) :
  (RegExp.concat (RegExp.concat R S) T).languageOf =
    (RegExp.concat R (RegExp.concat S T)).languageOf :=
  by
  simp only [RegExp.languageOf]
  simp


example
  {α : Type}
  (R S T : RegExp α) :
  (RegExp.concat R (RegExp.union S T)).languageOf =
    (RegExp.union (RegExp.concat R S) (RegExp.concat R T)).languageOf :=
  by
  simp only [RegExp.languageOf]
  ext cs
  constructor
  · simp
    intro xs a1 ys a2 a3
    subst a3
    cases a2
    case _ c1 =>
      left
      apply Exists.intro xs
      constructor
      · exact a1
      · apply Exists.intro ys
        tauto
    case _ c1 =>
      right
      apply Exists.intro xs
      constructor
      · exact a1
      · apply Exists.intro ys
        tauto
  · simp
    intro a1
    cases a1
    all_goals
      case _ c1 =>
        apply Exists.elim c1
        intro xs a2
        clear c1
        cases a2
        case _ a2_left a2_right =>
          apply Exists.elim a2_right
          intro ys a3
          apply Exists.intro xs
          constructor
          · tauto
          · apply Exists.intro ys
            tauto


example
  {α : Type}
  (R S T : RegExp α) :
  (RegExp.concat (RegExp.union S T) R).languageOf =
    (RegExp.union (RegExp.concat S R) (RegExp.concat T R)).languageOf :=
  by
  simp only [RegExp.languageOf]
  aesop


example
  {α : Type} :
  (RegExp.closure RegExp.zero).languageOf α = RegExp.epsilon.languageOf :=
  by
  simp only [RegExp.languageOf]
  ext cs
  simp
  constructor
  · aesop
  · intro a1
    apply Exists.intro []
    simp
    simp only [a1]


example
  {α : Type}
  (R : RegExp α) :
  (RegExp.concat R (RegExp.closure R)).languageOf =
    (RegExp.concat (RegExp.closure R) R).languageOf :=
  by
    simp only [RegExp.languageOf]
    ext cs
    simp
    constructor
    · intro a1
      apply Exists.elim a1
      intro r a2
      clear a1

      cases a2
      case _ a2_left a2_right =>
        apply Exists.elim a2_right
        intro rs a3
        clear a2_right

        cases a3
        case _ a3_left a3_right =>
          · obtain s1 := List.eq_nil_or_concat (r :: rs)
            simp at s1

            apply Exists.elim s1
            intro rs' a4
            clear s1

            apply Exists.elim a4
            intro r' a5
            clear a4

            have s2 : ∀ (x : List α), x ∈ (r :: rs) →
              x ∈ RegExp.languageOf α R :=
            by
              simp
              tauto

            apply Exists.intro rs'
            constructor
            · intro x a6
              apply s2
              simp only [a5]
              simp
              left
              exact a6

            · apply Exists.intro r'
              constructor
              · apply s2
                simp only [a5]
                simp
              · simp only [← a3_right]

                have s3 : List.join rs' ++ r' = List.join (rs' ++ [r']) :=
                by
                  simp

                simp only [s3]

                have s4 : r ++ List.join rs = List.join (r :: rs) :=
                by
                  simp

                simp only [s4]

                simp only [a5]
    · intro a1
      apply Exists.elim a1
      intro rs a2
      clear a1
      cases a2
      case _ a2_left a2_right =>
        apply Exists.elim a2_right
        intro r a3
        clear a2_right
        cases a3
        case _ a3_left a3_right =>
          subst a3_right

          have s2 : List.join rs ++ r = List.join (rs ++ [r]) :=
          by
            simp

          simp only [s2]
          clear s2

          have s3 : r ++ List.join rs = List.join ([r] ++ rs) :=
          by
            simp

          cases rs
          case nil =>
            apply Exists.intro r
            constructor
            · exact a3_left
            · apply Exists.intro []
              simp
          case cons hd tl =>
            simp at a2_left
            cases a2_left
            case _ a2_left_left a2_left_right =>
              apply Exists.intro hd
              constructor
              · exact a2_left_left
              · apply Exists.intro (tl ++ [r])
                constructor
                · simp
                  intro r' a4
                  cases a4
                  case _ a4_left =>
                    apply a2_left_right
                    exact a4_left
                  case _ a4_right =>
                    subst a4_right
                    exact a3_left
                · simp
