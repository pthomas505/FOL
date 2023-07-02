import Mathlib.Tactic


section
open Lean Parser Tactic
syntax (name := simp') "simp" (config)? (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*) "]")? (location)? : tactic

macro_rules (kind := simp')
  | stx => `(tactic| fail_if_no_progress $(⟨stx.setKind ``Tactic.simp⟩))
end
