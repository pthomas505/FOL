import Mathlib.Data.String.Lemmas


def List.str_max_len :
  List String → ℕ
| [] => 0
| hd :: tl => max hd.length (List.str_max_len tl)

lemma list_str_max_len_mem
  (s : String)
  (l : List String)
  (h1 : s ∈ l) :
  s.length <= List.str_max_len l :=
  by
  induction l
  case nil =>
    simp at h1
  case cons hd tl ih =>
    simp at h1
    unfold List.str_max_len
    cases h1
    case inl c1 =>
      simp only [c1]
      simp
    case inr c1 =>
      specialize ih c1
      trans List.str_max_len tl
      · exact ih
      · simp

def variant
  (s : String)
  (c : Char)
  (l : List String) :=
  if h : s ∈ l
  then
  have : List.str_max_len l + 1 - (String.length s + String.length (Char.toString c)) < List.str_max_len l + 1 - String.length s :=
    by
    have s1 : (Char.toString c).length = 1
    simp only [String.length]
    unfold Char.toString
    simp
    simp only [s1]
    simp
    obtain s2 := list_str_max_len_mem s l h
    simp only [le_iff_lt_or_eq] at s2
    cases s2
    case inl c1 =>   
      have s3 := c1.le
      refine Iff.mpr (tsub_lt_tsub_iff_right s3) ?_
      simp
    case inr c1 =>
      simp only [c1]
      simp
  variant (s ++ c.toString) c l
  else s
  termination_by variant s _ l => List.str_max_len l + 1 - s.length


#eval variant "a" '+' ["a+", "a"]
