import Lean

import FOL.NV.Formula


set_option autoImplicit false


namespace FOL.NV

open Formula

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
    mkAppM ``PredName.mk #[X']

  | _ => throwUnsupportedSyntax


partial def elabFormula : Syntax → MetaM Expr
  | `(formula| $X:pred_name ($xs,*)) => do
    let X' : Expr ← elabPredName X

    let xs' : Array Expr ← xs.getElems.mapM (fun x => elabVarName x)
    let xs'' : Expr ← mkListLit (.const ``VarName_ []) xs'.toList

    mkAppM ``Formula.pred_var_ #[X', xs'']

  | `(formula| ($x:var_name = $y:var_name)) => do
    let x' : Expr ← elabVarName x
    let y' : Expr ← elabVarName y
    mkAppM ``Formula.eq_ #[x', y']

  | `(formula| T) => mkAppM ``Formula.true_ #[]

  | `(formula| F) => mkAppM ``Formula.false_ #[]

  | `(formula| ~ $phi) => do
    let phi' : Expr ← elabFormula phi
    mkAppM ``Formula.not_ #[phi']

  | `(formula| ($phi:formula -> $psi:formula)) => do
    let phi' : Expr ← elabFormula phi
    let psi' : Expr ← elabFormula psi
    mkAppM ``Formula.imp_ #[phi', psi']

  | `(formula| ($phi:formula /\ $psi:formula)) => do
    let phi' : Expr ← elabFormula phi
    let psi' : Expr ← elabFormula psi
    mkAppM ``Formula.and_ #[phi', psi']

  | `(formula| ($phi:formula \/ $psi:formula)) => do
    let phi' : Expr ← elabFormula phi
    let psi' : Expr ← elabFormula psi
    mkAppM ``Formula.or_ #[phi', psi']

  | `(formula| ($phi:formula <-> $psi:formula)) => do
    let phi' : Expr ← elabFormula phi
    let psi' : Expr ← elabFormula psi
    mkAppM ``Formula.iff_ #[phi', psi']

  | `(formula| (A. $x:var_name $phi)) => do
    let x' : Expr ← elabVarName x
    let phi' : Expr ← elabFormula phi
    mkAppM ``Formula.forall_ #[x', phi']

  | `(formula| (E. $x:var_name $phi)) => do
    let x' : Expr ← elabVarName x
    let phi' : Expr ← elabFormula phi
    mkAppM ``Formula.exists_ #[x', phi']

  | _ => throwUnsupportedSyntax


elab "(Formula|" p:formula ")" : term => elabFormula p

#check (Formula| P () )
#check (Formula| P (x) )
#check (Formula| P (x, y) )
#check (Formula| ((x = y) /\ (y = x)) )
#check (Formula| ( A. x P () ) )
#check (Formula| ( A. x (A. y (P (x) <-> P (y, z) ) ) ) )
