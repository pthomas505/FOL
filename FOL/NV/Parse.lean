import Lean

import FOL.NV.Formula


set_option autoImplicit false


open Formula_

open Lean Elab Meta


declare_syntax_cat var_name
declare_syntax_cat pred_name
declare_syntax_cat formula

syntax ident : var_name

syntax ident : pred_name

syntax pred_name "(" var_name,* ")" : formula
syntax "(" var_name "=" var_name ")" : formula
syntax "T" : formula
syntax "F" : formula
syntax "~" formula : formula
syntax "(" formula "->" formula ")" : formula
syntax "(" formula "/\\" formula ")" : formula
syntax "(" formula "\\/" formula ")" : formula
syntax "(" formula "<->" formula ")" : formula
syntax "(" "A." var_name formula ")" : formula
syntax "(" "E." var_name formula ")" : formula


partial def elabVarName : Syntax → MetaM Expr
  | `(var_name| $x:ident) =>
    let x' : Expr := Lean.mkStrLit x.getId.toString
    mkAppM ``VarName_.mk #[x']

  | _ => throwUnsupportedSyntax


partial def elabPredName : Syntax → MetaM Expr
  | `(pred_name| $X:ident) =>
    let X' : Expr := Lean.mkStrLit X.getId.toString
    mkAppM ``PredName_.mk #[X']

  | _ => throwUnsupportedSyntax


partial def elabFormula : Syntax → MetaM Expr
  | `(formula| $X:pred_name ($xs,*)) => do
    let X' : Expr ← elabPredName X

    let xs' : Array Expr ← xs.getElems.mapM (fun x => elabVarName x)
    let xs'' : Expr ← mkListLit (.const ``VarName_ []) xs'.toList

    mkAppM ``Formula_.pred_var_ #[X', xs'']

  | `(formula| ($x:var_name = $y:var_name)) => do
    let x' : Expr ← elabVarName x
    let y' : Expr ← elabVarName y
    mkAppM ``Formula_.eq_ #[x', y']

  | `(formula| T) => mkAppM ``Formula_.true_ #[]

  | `(formula| F) => mkAppM ``Formula_.false_ #[]

  | `(formula| ~ $phi) => do
    let phi' : Expr ← elabFormula phi
    mkAppM ``Formula_.not_ #[phi']

  | `(formula| ($phi:formula -> $psi:formula)) => do
    let phi' : Expr ← elabFormula phi
    let psi' : Expr ← elabFormula psi
    mkAppM ``Formula_.imp_ #[phi', psi']

  | `(formula| ($phi:formula /\ $psi:formula)) => do
    let phi' : Expr ← elabFormula phi
    let psi' : Expr ← elabFormula psi
    mkAppM ``Formula_.and_ #[phi', psi']

  | `(formula| ($phi:formula \/ $psi:formula)) => do
    let phi' : Expr ← elabFormula phi
    let psi' : Expr ← elabFormula psi
    mkAppM ``Formula_.or_ #[phi', psi']

  | `(formula| ($phi:formula <-> $psi:formula)) => do
    let phi' : Expr ← elabFormula phi
    let psi' : Expr ← elabFormula psi
    mkAppM ``Formula_.iff_ #[phi', psi']

  | `(formula| (A. $x:var_name $phi)) => do
    let x' : Expr ← elabVarName x
    let phi' : Expr ← elabFormula phi
    mkAppM ``Formula_.forall_ #[x', phi']

  | `(formula| (E. $x:var_name $phi)) => do
    let x' : Expr ← elabVarName x
    let phi' : Expr ← elabFormula phi
    mkAppM ``Formula_.exists_ #[x', phi']

  | _ => throwUnsupportedSyntax


elab "(Formula_|" p:formula ")" : term => elabFormula p

#check (Formula_| P () )
#check (Formula_| P (x) )
#check (Formula_| P (x, y) )
#check (Formula_| ((x = y) /\ (y = x)) )
#check (Formula_| ( A. x P () ) )
#check (Formula_| ( A. x (A. y (P (x) <-> P (y, z) ) ) ) )
