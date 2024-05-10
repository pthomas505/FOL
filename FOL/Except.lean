import Batteries


set_option autoImplicit false


theorem Except.bind_eq_ok
  {ε : Type}
  {α : Type}
  {β : Type}
  (x : Except ε α)
  (f : α → Except ε β)
  (a : β):
  (Except.bind x f = .ok a) ↔ ∃ b, x = .ok b ∧ f b = .ok a :=
  by
  cases x
  case error x =>
    simp only [Except.bind]
    simp
  case ok x =>
    simp only [Except.bind]
    simp


def Option.toExcept
  {α : Type}
  (opt : Option α)
  (message : String) :
  Except String α :=
  if h : Option.isSome opt
  then
    let a := Option.get opt h
    Except.ok a
  else Except.error message
