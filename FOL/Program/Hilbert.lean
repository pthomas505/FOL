set_option autoImplicit false


notation "ℕ" => Nat


inductive Formula : Type
  | var_ : String → Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  deriving Inhabited, DecidableEq

open Formula

def Formula.toString : Formula → String
  | var_ phi => phi
  | not_ phi => s! "(¬ {phi.toString})"
  | imp_ phi psi => s! "({phi.toString} → {psi.toString})"

instance : ToString Formula :=
  { toString := fun F => F.toString }

instance : Repr Formula :=
  { reprPrec := fun F _ => F.toString.toFormat }


inductive Step : Type
| ax_1 : Formula → Formula → Step
| ax_2 : Formula → Formula → Formula → Step
| ax_3 : Formula → Formula → Step
| mp : ℕ → ℕ → Step

open Step




def checkStep (Γ : List Formula) : Step → Except String Formula

| ax_1 phi psi =>
    Except.ok (phi.imp_ (psi.imp_ phi))

| ax_2 phi psi chi =>
    Except.ok ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi)))

| ax_3 phi psi =>
    Except.ok (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi))

| mp major_index minor_index =>
    match List.get? Γ major_index with
    | Option.none => Except.error s! "The index of the major premise is out of range."
    | Option.some major =>
        match major with
        | imp_ major_left major_right =>
            match List.get? Γ minor_index with
            | Option.some minor =>
                if minor = major_left
                then Except.ok major_right
                else Except.error "The minor premise does not match the antecedent of the major premise."
            | Option.none => Except.error "The index of the minor premise is out of range."
        | _ => Except.error "The major premise is not an implication."


#eval checkStep [(var_ "P"), imp_ (var_ "P") (var_ "Q")] (mp 1 0)
