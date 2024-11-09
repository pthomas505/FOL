import FOL.Parsing.Language.RegExp.Similar


set_option autoImplicit false


-- https://people.cs.uchicago.edu/~jhr/papers/2009/jfp-re-derivatives.pdf


namespace RegExp


partial
def goto
  {α : Type}
  [DecidableEq α]
  (Sigma : List α)
  (q : RegExp α)
  (pair : (Finset (RegExp α)) × Finset (RegExp α × α × RegExp α))
  (c : α) :=
  let Q := pair.fst
  let δ := pair.snd
  let q_c := simp_derivative q c
  if ∃ q', q' ∈ Q ∧ q' = q_c
  then (Q, δ ∪ {(q, c, q_c)})
  else
    let Q' := Q ∪ {q_c}
    let δ' := δ ∪ {(q, c, q_c)}
    Sigma.foldl (goto Sigma q_c) (Q', δ')
