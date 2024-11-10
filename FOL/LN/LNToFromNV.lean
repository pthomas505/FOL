import FOL.LN.Binders
import MathlibExtra.Fresh


set_option autoImplicit false


-- named variables to locally nameless


/--
  The conversion of named variables to locally nameless variables.
-/
def NVVarToLNVar
  (outer : ℕ)
  (context : Std.HashMap String ℕ)
  (x : String) :
  LN.Var :=
  let opt := context.get? x
  if h : Option.isSome opt
  then
    let n := Option.get opt h
    LN.Var.bound_ (outer - n)
  else LN.Var.free_ x

/--
  Helper function for NVToLN.
-/
def NVToLNAux
  (outer : ℕ)
  (context : Std.HashMap String ℕ) :
  NV.Formula → LN.Formula

  | NV.Formula.pred_ X xs => LN.Formula.pred_ X (xs.map (NVVarToLNVar outer context))

  | NV.Formula.not_ phi => LN.Formula.not_ (NVToLNAux outer context phi)

  | NV.Formula.imp_ phi psi => LN.Formula.imp_ (NVToLNAux outer context phi) (NVToLNAux outer context psi)

  | NV.Formula.forall_ x phi =>
    let context' := context.insert x (outer + 1)
    LN.Formula.forall_ x (NVToLNAux (outer + 1) context' phi)

/--
  The conversion of named variable formulas to locally nameless formulas.
-/
def NVToLN (F : NV.Formula) : LN.Formula :=
  NVToLNAux 0 ∅ F


-- locally nameless to named variable

/--
  The conversion of locally nameless variables to named variables.
-/
def LNVarToNVVar
  (outer : ℕ)
  (context : Std.HashMap ℤ String) :
  LN.Var → Option String
  | LN.Var.free_ x => Option.some x
  | LN.Var.bound_ n => context.get? (outer - n)

/--
  Helper function for LNToNV.
-/
def LNToNVAux
  (c : Char)
  (outer : ℕ)
  (context : Std.HashMap ℤ String) :
  LN.Formula → Option NV.Formula

  | LN.Formula.pred_ X xs => do
      let xs' ← xs.mapM (LNVarToNVVar outer context)
      Option.some (NV.Formula.pred_ X xs')

  | LN.Formula.not_ phi => do
      let phi' ← LNToNVAux c outer context phi
      Option.some (NV.Formula.not_ phi')

  | LN.Formula.imp_ phi psi => do
      let phi' ← LNToNVAux c outer context phi
      let psi' ← LNToNVAux c outer context psi
      Option.some (NV.Formula.imp_ phi' psi')

  | LN.Formula.forall_ x phi => do
      let x' := fresh x c phi.freeStringSet
      let phi' ← LNToNVAux c (outer + 1) (context.insert (outer + 1) x') phi
      Option.some (NV.Formula.forall_ x' phi')

/--
  The conversion of locally nameless formulas to named variable formulas.
-/
def LNToNV
  (c : Char)
  (F : LN.Formula) :
  Option NV.Formula :=
  LNToNVAux c 0 ∅ F


#lint
