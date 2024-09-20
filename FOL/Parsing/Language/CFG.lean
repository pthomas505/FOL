import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic

import FOL.List
import FOL.Parsing.Language.Kleene


set_option autoImplicit false


-- https://github.com/mn200/CFL-HOL
-- https://arxiv.org/pdf/1509.02032.pdf
-- https://core.ac.uk/download/pdf/156629067.pdf


/-
  The definition of a context free grammar.

  An alphabet Σ is a finite, non-empty set of indivisible symbols.
  A string over an alphabet Σ is a finite sequence of members of Σ.

  N is a non-terminal alphabet.
  T is a terminal alphabet such that N ∩ T = ∅.
  P ⊆ N × (N ∪ T)* is a set of productions.
  S ∈ N is the start symbol.
-/


inductive Symbol (NTS : Type) (TS : Type)
| nts : NTS → Symbol NTS TS
| ts : TS → Symbol NTS TS


def Symbol.isNTS
  {NTS : Type}
  {TS : Type} :
  Symbol NTS TS → Prop
  | nts _ => True
  | ts _ => False

instance
  (NTS : Type)
  (TS : Type)
  (c : Symbol NTS TS) :
  Decidable c.isNTS :=
  by
    simp only [Symbol.isNTS]
    cases c
    all_goals
      infer_instance


def Symbol.isTS
  {NTS : Type}
  {TS : Type} :
  Symbol NTS TS → Prop
  | nts _ => False
  | ts _ => True

instance
  (NTS : Type)
  (TS : Type)
  (c : Symbol NTS TS) :
  Decidable c.isTS :=
  by
    simp only [Symbol.isTS]
    cases c
    all_goals
      infer_instance


def Symbol.getNTS
  (NTS : Type)
  (TS : Type) :
  (c : Symbol NTS TS) → (h1 : c.isNTS) → NTS
  | nts a, _ => a


lemma symbol_is_nts_imp_exists_nts
  {NTS : Type}
  {TS : Type}
  (c : Symbol NTS TS)
  (h1 : c.isNTS) :
  ∃ (x : NTS), c = Symbol.nts x :=
  by
    cases c
    case nts x =>
      apply Exists.intro x
      rfl
    case ts x =>
      simp only [Symbol.isNTS] at h1


def Symbol.getTS
  (NTS : Type)
  (TS : Type) :
  (c : Symbol NTS TS) → (h1 : c.isTS) → TS
  | ts a, _ => a


lemma symbol_is_ts_imp_exists_ts
  {NTS : Type}
  {TS : Type}
  (c : Symbol NTS TS)
  (h1 : c.isTS) :
  ∃ (x : TS), c = Symbol.ts x :=
  by
    cases c
    case nts x =>
      simp only [Symbol.isTS] at h1
    case ts x =>
      apply Exists.intro x
      rfl


lemma symbol_not_nts_iff_is_ts
  {NTS : Type}
  {TS : Type}
  (c : Symbol NTS TS) :
  ¬ c.isNTS ↔ c.isTS :=
  by
    cases c
    case _ x =>
      simp only [Symbol.isNTS]
      simp only [Symbol.isTS]
      simp
    case _ x =>
      simp only [Symbol.isNTS]
      simp only [Symbol.isTS]
      simp


lemma symbol_not_ts_iff_is_nts
  {NTS : Type}
  {TS : Type}
  (c : Symbol NTS TS) :
  ¬ c.isTS ↔ c.isNTS :=
  by
    cases c
    case _ x =>
      simp only [Symbol.isNTS]
      simp only [Symbol.isTS]
      simp
    case _ x =>
      simp only [Symbol.isNTS]
      simp only [Symbol.isTS]
      simp


structure Rule (NTS : Type) (TS : Type) :=
  (lhs : NTS)
  (rhs : Str (Symbol NTS TS))


def Rule.isEpsilonRule
  {NTS : Type}
  {TS : Type}
  (P : Rule NTS TS) :
  Prop :=
  P.rhs = []


structure CFG (NTS : Type) (TS : Type) :=
  (rule_list : List (Rule NTS TS))
  (start_symbol : NTS)


/--
  is_derivation_step G lsl rsl := lsl =>G rsl
-/
def is_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS)) :
  Prop :=
    ∃
      (R : Rule NTS TS)
      (sl_1 sl_2 : Str (Symbol NTS TS)),
      R ∈ G.rule_list ∧
      lsl = sl_1 ++ [Symbol.nts R.lhs] ++ sl_2 ∧
      rsl = sl_1 ++ R.rhs ++ sl_2


def is_leftmost_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS)) :
  Prop :=
    ∃
      (R : Rule NTS TS)
      (sl_1 sl_2 : Str (Symbol NTS TS)),
      (∀ (c : Symbol NTS TS), c ∈ sl_1 → c.isTS) ∧
      R ∈ G.rule_list ∧
      lsl = sl_1 ++ [Symbol.nts R.lhs] ++ sl_2 ∧
      rsl = sl_1 ++ R.rhs ++ sl_2


def is_rightmost_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS)) :
  Prop :=
    ∃
      (R : Rule NTS TS)
      (sl_1 sl_2 : Str (Symbol NTS TS)),
      (∀ (c : Symbol NTS TS), c ∈ sl_2 → c.isTS) ∧
      R ∈ G.rule_list ∧
      lsl = sl_1 ++ [Symbol.nts R.lhs] ++ sl_2 ∧
      rsl = sl_1 ++ R.rhs ++ sl_2


inductive is_derivation_alt
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Str (Symbol NTS TS) → Str (Symbol NTS TS) → Prop
| refl
  (sl : Str (Symbol NTS TS)) :
  is_derivation_alt G sl sl

| trans
  (sl_1 sl_2 sl_3 : Str (Symbol NTS TS)) :
  is_derivation_alt G sl_1 sl_2 →
  is_derivation_step G sl_2 sl_3 →
  is_derivation_alt G sl_1 sl_3


example
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  is_derivation_alt G = Relation.ReflTransGen (is_derivation_step G) :=
  by
    ext lsl rsl
    constructor
    · intro a1
      induction a1
      case _ =>
        exact Relation.ReflTransGen.refl
      case _ sl_1 sl_2 _ ih_2 ih_3 =>
        exact Relation.ReflTransGen.tail ih_3 ih_2
    · intro a1
      induction a1
      case _ =>
        exact is_derivation_alt.refl lsl
      case _ sl_1 sl_2 _ ih_2 ih_3 =>
        exact is_derivation_alt.trans lsl sl_1 sl_2 ih_3 ih_2


def CFG.LanguageOf
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Language.Language TS :=
  { s : Str TS | Relation.ReflTransGen (is_derivation_step G) [Symbol.nts G.start_symbol] (s.map Symbol.ts) }


def CFG.LeftLanguageOf
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Language.Language TS :=
  { s : Str TS | Relation.ReflTransGen (is_leftmost_derivation_step G) [Symbol.nts G.start_symbol] (s.map Symbol.ts) }


def CFG.RightLanguageOf
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS) :
  Language.Language TS :=
  { s : Str TS | Relation.ReflTransGen (is_rightmost_derivation_step G) [Symbol.nts G.start_symbol] (s.map Symbol.ts) }


lemma is_derivation_step_same_append_left
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (u v : Str (Symbol NTS TS))
  (x : Str (Symbol NTS TS))
  (h1 : is_derivation_step G u v) :
  is_derivation_step G (x ++ u) (x ++ v) :=
  by
    simp only [is_derivation_step] at h1
    obtain ⟨R, sl_1, sl_2, a1, a2, a3⟩ := h1
    rw [a2]
    rw [a3]
    simp only [is_derivation_step]
    apply Exists.intro R
    apply Exists.intro (x ++ sl_1)
    apply Exists.intro sl_2
    constructor
    · exact a1
    · constructor
      · simp
      · simp


lemma is_derivation_step_same_append_right
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (u v : Str (Symbol NTS TS))
  (x : Str (Symbol NTS TS))
  (h1 : is_derivation_step G u v) :
  is_derivation_step G (u ++ x) (v ++ x) :=
  by
    simp only [is_derivation_step] at h1
    obtain ⟨R, sl_1, sl_2, a1, a2, a3⟩ := h1
    rw [a2]
    rw [a3]
    simp only [is_derivation_step]
    apply Exists.intro R
    apply Exists.intro sl_1
    apply Exists.intro (sl_2 ++ x)
    constructor
    · exact a1
    · constructor
      · simp
      · simp


lemma rtc_is_derivation_step_same_append_left
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (u v : Str (Symbol NTS TS))
  (x : Str (Symbol NTS TS))
  (h1 : Relation.ReflTransGen (is_derivation_step G) u v) :
  Relation.ReflTransGen (is_derivation_step G) (x ++ u) (x ++ v) :=
  by
    induction h1 using Relation.ReflTransGen.head_induction_on
    case refl =>
      exact Relation.ReflTransGen.refl
    case head a b ih_1 _ ih_3 =>
      apply Relation.ReflTransGen.head
      · exact is_derivation_step_same_append_left G a b x ih_1
      · exact ih_3


lemma rtc_is_derivation_step_same_append_right
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (u v : Str (Symbol NTS TS))
  (x : Str (Symbol NTS TS))
  (h1 : Relation.ReflTransGen (is_derivation_step G) u v) :
  Relation.ReflTransGen (is_derivation_step G) (u ++ x) (v ++ x) :=
  by
    induction h1 using Relation.ReflTransGen.head_induction_on
    case refl =>
      exact Relation.ReflTransGen.refl
    case head a b ih_1 _ ih_3 =>
      apply Relation.ReflTransGen.head
      · exact is_derivation_step_same_append_right G a b x ih_1
      · exact ih_3


lemma derives_append
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (M N P Q : Str (Symbol NTS TS))
  (h1 : Relation.ReflTransGen (is_derivation_step G) M N)
  (h2 : Relation.ReflTransGen (is_derivation_step G) P Q) :
  Relation.ReflTransGen (is_derivation_step G) (M ++ P) (N ++ Q) :=
  by
    -- (M ++ P) (N ++ P) ; (N ++ P) (N ++ Q)

    have s1 : Relation.ReflTransGen (is_derivation_step G) (M ++ P) (N ++ P) :=
      rtc_is_derivation_step_same_append_right G M N P h1

    have s2 : Relation.ReflTransGen (is_derivation_step G) (N ++ P) (N ++ Q) := rtc_is_derivation_step_same_append_left G P Q N h2

    exact Relation.ReflTransGen.trans s1 s2


lemma res1
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lhs: NTS)
  (rhs: Str (Symbol NTS TS))
  (h1 : ⟨lhs, rhs⟩ ∈ G.rule_list) :
  is_derivation_step G [Symbol.nts lhs] rhs :=
  by
    simp only [is_derivation_step]
    apply Exists.intro ⟨lhs, rhs⟩
    apply Exists.intro []
    apply Exists.intro []
    simp
    exact h1


lemma res2
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (a b c : Str (Symbol NTS TS))
  (h1 : is_derivation_step G a b)
  (h2 : is_derivation_step G b c) :
  Relation.ReflTransGen (is_derivation_step G) a c :=
  by
    apply Relation.ReflTransGen.head h1
    apply Relation.ReflTransGen.head h2
    exact Relation.ReflTransGen.refl


lemma res3
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (a b c : Str (Symbol NTS TS))
  (h1 : is_derivation_step G a b)
  (h2 : Relation.ReflTransGen (is_derivation_step G) b c) :
  Relation.ReflTransGen (is_derivation_step G) a c :=
  by
    apply Relation.ReflTransGen.head h1
    exact h2


lemma slres
  {NTS : Type}
  {TS : Type}
  (lhs s : NTS)
  (sl_1 sl_2 : Str (Symbol NTS TS))
  (h1 : sl_1 ++ [Symbol.nts lhs] ++ sl_2 = [Symbol.nts s]) :
  lhs = s :=
  by
    cases sl_1
    case nil =>
      simp at h1
      exact h1.left
    case cons hd tl =>
      simp at h1


lemma slres2
  {NTS : Type}
  {TS : Type}
  (lhs s : NTS)
  (sl_1 sl_2 : Str (Symbol NTS TS))
  (h1 : sl_1 ++ [Symbol.nts lhs] ++ sl_2 = [Symbol.nts s]) :
  (sl_1 = []) ∧ (sl_2 = []) :=
  by
    cases sl_1
    case nil =>
      simp at h1
      simp
      exact h1.right
    case cons hd tl =>
      simp at h1


lemma rgr_r8
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (sym : Symbol NTS TS)
  (r r1 r2 : Str (Symbol NTS TS))
  (l : NTS)
  (h1 : r = r1 ++ [sym] ++ r2)
  (h2 : is_derivation_step G [Symbol.nts l] r) :
  ∃ (a b : Str (Symbol NTS TS)), is_derivation_step G [Symbol.nts l] (a ++ [sym] ++ b) :=
  by
    apply Exists.intro r1
    apply Exists.intro r2
    rw [h1] at h2
    exact h2


def is_derivation_list
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (x y : Str (Symbol NTS TS)) :=
  ∃ (l : Str (Symbol NTS TS)), List.Chain' (is_derivation_step G) ([x] ++ [l] ++ [y])


lemma upgr_r7
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (u z : Str (Symbol NTS TS))
  (x y : Str (Symbol NTS TS))
  (h1 : is_derivation_list G u z)
  (h2 : u = x ++ y) :
  ∃ (x' y' : Str (Symbol NTS TS)), (z = x' ++ y') →
    is_derivation_list G x x' ∧
    is_derivation_list G y y' :=
  by
    simp only [is_derivation_list] at h1
    rw [h2] at h1
    sorry


-------------------------------------------------------------------------------

lemma leftmost_derivation_step_is_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS))
  (h1 : is_leftmost_derivation_step G lsl rsl) :
  is_derivation_step G lsl rsl :=
  by
    simp only [is_leftmost_derivation_step] at h1
    obtain ⟨R, sl_1, sl_2, _, a2, a3⟩ := h1
    simp only [is_derivation_step]
    exact ⟨R, sl_1, sl_2, a2, a3⟩


lemma rightmost_derivation_step_is_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS))
  (h1 : is_rightmost_derivation_step G lsl rsl) :
  is_derivation_step G lsl rsl :=
  by
    simp only [is_rightmost_derivation_step] at h1
    obtain ⟨R, sl_1, sl_2, _, a2, a3⟩ := h1
    simp only [is_derivation_step]
    exact ⟨R, sl_1, sl_2, a2, a3⟩


lemma derivation_step_to_terminal_string_is_leftmost_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (sl s : Str (Symbol NTS TS))
  (h1 : is_derivation_step G sl s)
  (h2 : ∀ (c : Symbol NTS TS), c ∈ s → c.isTS) :
  is_leftmost_derivation_step G sl s :=
  by
    simp only [is_derivation_step] at h1
    obtain ⟨R, sl_1, sl_2, a1, a2, a3⟩ := h1
    rw [a3] at h2
    have s1 : ∀ (c : Symbol NTS TS), c ∈ sl_1 → c.isTS :=
    by
      intro c a4
      apply h2 c
      simp
      left
      exact a4
    simp only [is_leftmost_derivation_step]
    exact ⟨R, sl_1, sl_2, s1, a1, a2, a3⟩


lemma derivation_step_to_terminal_string_is_rightmost_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (sl s : Str (Symbol NTS TS))
  (h1 : is_derivation_step G sl s)
  (h2 : ∀ (c : Symbol NTS TS), c ∈ s → c.isTS) :
  is_rightmost_derivation_step G sl s :=
  by
    simp only [is_derivation_step] at h1
    obtain ⟨R, sl_1, sl_2, a1, a2, a3⟩ := h1
    rw [a3] at h2
    have s1 : ∀ (c : Symbol NTS TS), c ∈ sl_2 → c.isTS :=
    by
      intro c a4
      apply h2 c
      simp
      right
      right
      exact a4
    simp only [is_rightmost_derivation_step]
    exact ⟨R, sl_1, sl_2, s1, a1, a2, a3⟩


lemma exists_nts_imp_exists_leftmost_nts
  {NTS : Type}
  {TS : Type}
  (sl : Str (Symbol NTS TS))
  (h1 : ∃ (c : Symbol NTS TS), c ∈ sl ∧ c.isNTS) :
  ∃
    (sl_1 : Str (Symbol NTS TS))
    (A : NTS)
    (sl_2 : Str (Symbol NTS TS)),
    (∀ (c : Symbol NTS TS), c ∈ sl_1 → c.isTS) ∧
    sl = sl_1 ++ [Symbol.nts A] ++ sl_2 :=
  by
    obtain s1 := List.exists_mem_imp_exists_leftmost_mem sl (Symbol.isNTS) h1
    obtain ⟨sl_1, A, sl_2, a1, a2, a3⟩ := s1
    obtain s2 := symbol_is_nts_imp_exists_nts A a2
    obtain ⟨x, a4⟩ := s2
    apply Exists.intro sl_1
    apply Exists.intro x
    apply Exists.intro sl_2
    constructor
    · simp only [symbol_not_nts_iff_is_ts] at a3
      exact a3
    · rw [a4] at a1
      exact a1


lemma exists_nts_imp_exists_rightmost_nts
  {NTS : Type}
  {TS : Type}
  (sl : Str (Symbol NTS TS))
  (h1 : ∃ (c : Symbol NTS TS), c ∈ sl ∧ c.isNTS) :
  ∃
    (sl_1 : Str (Symbol NTS TS))
    (A : NTS)
    (sl_2 : Str (Symbol NTS TS)),
    (∀ (c : Symbol NTS TS), c ∈ sl_2 → c.isTS) ∧
    sl = sl_1 ++ [Symbol.nts A] ++ sl_2 :=
  by
    obtain s1 := List.exists_mem_imp_exists_rightmost_mem sl (Symbol.isNTS) h1
    obtain ⟨sl_1, A, sl_2, a1, a2, a3⟩ := s1
    obtain s2 := symbol_is_nts_imp_exists_nts A a2
    obtain ⟨x, a4⟩ := s2
    apply Exists.intro sl_1
    apply Exists.intro x
    apply Exists.intro sl_2
    constructor
    · simp only [symbol_not_nts_iff_is_ts] at a3
      exact a3
    · rw [a4] at a1
      exact a1


lemma is_derivation_step_and_is_not_leftmost_derivation_step_aux
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS))
  (h1 : is_derivation_step G lsl rsl)
  (h2 : ¬ is_leftmost_derivation_step G lsl rsl) :
    ∃
      (R : Rule NTS TS)
      (sl_1 sl_2 : Str (Symbol NTS TS)),
      ¬ (∀ (c : Symbol NTS TS), c ∈ sl_1 → c.isTS) ∧
      R ∈ G.rule_list ∧
      lsl = sl_1 ++ [Symbol.nts R.lhs] ++ sl_2 ∧
      rsl = sl_1 ++ R.rhs ++ sl_2 :=
  by
    simp only [is_derivation_step] at h1
    obtain ⟨R, sl_1, sl_2, ih_1, ⟨ih_2, ih_3⟩⟩  := h1

    simp only [is_leftmost_derivation_step] at h2
    simp at h2
    specialize h2 R sl_1

    apply Exists.intro R
    apply Exists.intro sl_1
    apply Exists.intro sl_2
    constructor
    · intro contra
      simp at ih_2
      specialize h2 contra ih_1 sl_2 ih_2
      simp at ih_3
      contradiction
    · exact ⟨ih_1, ih_2, ih_3⟩


lemma is_derivation_step_and_is_not_leftmost_derivation_step
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl rsl : Str (Symbol NTS TS))
  (h1 : is_derivation_step G lsl rsl)
  (h2 : ¬ is_leftmost_derivation_step G lsl rsl) :
  ∃
    (sl_1 sl_2 sl_3 sl_4 : Str (Symbol NTS TS))
    (A B : NTS),
    (∀ (c : Symbol NTS TS), c ∈ sl_1 → c.isTS) ∧
    ⟨B, sl_3⟩ ∈ G.rule_list ∧
    lsl = sl_1 ++ [Symbol.nts A] ++ sl_2 ++ [Symbol.nts B] ++ sl_4 ∧
    rsl = sl_1 ++ [Symbol.nts A] ++ sl_2 ++ sl_3 ++ sl_4 :=
  by
    obtain s1 := is_derivation_step_and_is_not_leftmost_derivation_step_aux G lsl rsl h1 h2
    obtain ⟨R, sl_1, sl_2, a1, a2, a3, a4⟩ := s1
    rw [a3]
    rw [a4]

    simp at a1
    simp only [symbol_not_ts_iff_is_nts] at a1
    obtain s2 := exists_nts_imp_exists_leftmost_nts sl_1 a1
    obtain ⟨sl_3, A, sl_4, ⟨a5, a6⟩⟩ := s2
    rw [a6]

    exact ⟨sl_3, sl_4, R.rhs, sl_2, A, R.lhs, a5, a2, rfl, rfl⟩


theorem extracted_1
  {NTS TS : Type}
  (G : CFG NTS TS)
  (w : Str (Symbol NTS TS))
  {alpha_1 : Str (Symbol NTS TS)}
  (u mu delta rho : Str (Symbol NTS TS))
  (A : NTS)
  (h1 : Relation.TransGen (is_leftmost_derivation_step G) alpha_1 w)
  (h2 : ∀ c ∈ u, c.isTS)
  (h3 : alpha_1 = u ++ [Symbol.nts A] ++ mu ++ delta ++ rho) :
  ∃ gamma,
    { lhs := A, rhs := gamma } ∈ G.rule_list ∧
     Relation.TransGen (is_leftmost_derivation_step G) (u ++ gamma ++ mu ++ delta ++ rho) w :=
  by
    sorry


example
  {NTS : Type}
  {TS : Type}
  (G : CFG NTS TS)
  (lsl w : Str (Symbol NTS TS))
  (h1 : Relation.TransGen (is_derivation_step G) lsl w)
  (h2 : ∀ (c : Symbol NTS TS), c ∈ w → c.isTS) :
  Relation.TransGen (is_leftmost_derivation_step G) lsl w :=
  by
    induction h1 using Relation.TransGen.head_induction_on
    case base sl ih =>
      apply Relation.TransGen.single
      exact derivation_step_to_terminal_string_is_leftmost_derivation_step G sl w ih h2
    case ih alpha alpha_1 ih_1 ih_2 ih_3 =>
      by_cases c1 : is_leftmost_derivation_step G alpha alpha_1
      case pos =>
        apply Relation.TransGen.trans
        · exact Relation.TransGen.single c1
        · exact ih_3
      case neg =>
        obtain s1 := is_derivation_step_and_is_not_leftmost_derivation_step G alpha alpha_1 ih_1 c1
        obtain ⟨u, mu, delta, rho, A, B, a1, a2, a3, a4⟩ := s1

        sorry
