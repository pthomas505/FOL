import Mathlib.Data.Finset.Basic

set_option autoImplicit false


def LF : Char := Char.ofNat 10


inductive Formula : Type
  | var_ : String → Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  deriving Inhabited, DecidableEq

open Formula

def Formula.toString : Formula → String
  | var_ phi => phi
  | not_ phi => s! "¬ {phi.toString}"
  | imp_ phi psi => s! "({phi.toString} → {psi.toString})"

instance : ToString Formula :=
  { toString := fun x => x.toString }

instance : Repr Formula :=
  { reprPrec := fun x _ => x.toString.toFormat }


inductive ArgumentStep : Type
  | thin : String → List Formula → ArgumentStep
  | assume : Formula → ArgumentStep
  | prop_1 : Formula → Formula → ArgumentStep
  | prop_2 : Formula → Formula → Formula → ArgumentStep
  | prop_3 : Formula → Formula → ArgumentStep
  | mp : String → String → ArgumentStep

open ArgumentStep

def ArgumentStep.toString : ArgumentStep → String
  | thin label hypotheses => s! "thin {label} {hypotheses}"
  | assume hypothesis => s! "assume {hypothesis}"
  | prop_1 phi psi => s! "prop_1 {phi} {psi}"
  | prop_2 phi psi chi => s! "prop_2 {phi} {psi} {chi}"
  | prop_3 phi psi => s! "prop_3 {phi} {psi}"
  | mp major_label minor_label => s! "mp {major_label} {minor_label}"

instance : ToString ArgumentStep :=
  { toString := fun x => x.toString }

instance : Repr ArgumentStep :=
  { reprPrec := fun x _ => x.toString.toFormat }


structure labeledArgumentStep : Type :=
  (label : String)
  (step : ArgumentStep)

def labeledArgumentStep.toString (x : labeledArgumentStep) : String :=
  s! "{x.label} : {x.step}"

instance : ToString labeledArgumentStep :=
  { toString := fun x => x.toString }

instance : Repr labeledArgumentStep :=
  { reprPrec := fun x _ => x.toString.toFormat }


structure Statement : Type :=
  (hypotheses : List Formula)
  (conclusion : Formula)

def Statement.toString (x : Statement) : String :=
  s! "{x.hypotheses} ⊢ {x.conclusion}"

instance : ToString Statement :=
  { toString := fun x => x.toString }

instance : Repr Statement :=
  { reprPrec := fun x _ => x.toString.toFormat }


structure labeledStatement : Type :=
  (label : String)
  (statement : Statement)

def labeledStatement.toString (x : labeledStatement) : String :=
  s! "{x.label} : {x.statement}"

instance : ToString labeledStatement :=
  { toString := fun x => x.toString }

instance : Repr labeledStatement :=
  { reprPrec := fun x _ => x.toString.toFormat }


def Context : Type := List labeledStatement

def Context.toString : Context → String
  | [] => ""
  | hd :: tl => s! "{Context.toString tl}{LF}{hd}"

instance : ToString Context :=
  { toString := fun x => x.toString }

instance : Repr Context :=
  { reprPrec := fun x _ => x.toString.toFormat }


def Context.find
  (context : Context)
  (label : String) :
  Except String Statement :=
  if let Option.some val := context.find? (fun val => val.label = label)
  then Except.ok val.statement
  else Except.error s!"{label} not found in context."


def checkArgumentStep
  (globalContext : Context)
  (localContext : Context) :
  ArgumentStep → Except String Statement

  | thin label hypotheses => do
    let statement ← localContext.find label
    Except.ok {
      hypotheses := hypotheses ++ statement.hypotheses
      conclusion := statement.conclusion
    }

  | assume hypothesis =>
    Except.ok {
      hypotheses := [hypothesis]
      conclusion := hypothesis }

  | prop_1 phi psi =>
      Except.ok {
        hypotheses := []
        conclusion := (phi.imp_ (psi.imp_ phi)) }

  | prop_2 phi psi chi =>
      Except.ok {
        hypotheses := []
        conclusion := ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi))) }

  | prop_3 phi psi =>
      Except.ok {
        hypotheses := []
        conclusion := (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi)) }

  | mp major_label minor_label => do
    let major ← localContext.find major_label
    let minor ← localContext.find minor_label
    if major.hypotheses.toFinset = minor.hypotheses.toFinset
    then
      if let imp_ major_conclusion_antecedent major_conclusion_consequent := major.conclusion
      then
        if minor.conclusion = major_conclusion_antecedent
        then Except.ok {
          hypotheses := major.hypotheses
          conclusion := major_conclusion_consequent
        }
        else Except.error s! "major premise : {major_label} : {major}{LF}minor premise : {minor_label} : {minor}{LF}The conclusion of the minor premise must match the antecedent of the conclusion of the major premise."
      else Except.error s! "major premise : {major_label} : {major}{LF}The conclusion of the major premise must be an implication."
    else Except.error s! "major premise : {major_label} : {major}{LF}minor premise : {minor_label} : {minor}{LF}The hypotheses of the minor premise must match the hypotheses of the major premise."


def Argument : Type := List labeledArgumentStep

structure labeledArgument : Type :=
  (label : String)
  (argument : Argument)


def checkArgumentAux
  (globalContext : Context)
  (localContext : Context) :
  Argument → Except String Context
  | [] => Except.ok localContext
  | hd :: tl =>
    match checkArgumentStep globalContext localContext hd.step with
    | Except.ok statement =>
        checkArgumentAux
          globalContext
          (
            {
              label := hd.label
              statement := statement
            } :: localContext
          )
          tl
    | Except.error message => Except.error s! "Global Context{LF}{globalContext}{LF}-----{LF}Local Context{localContext}{LF}-----{LF}Error{LF}{hd}{LF}{message}"

def checkArgument
  (globalContext : Context)
  (xs : List labeledArgumentStep) :
  Except String Context :=
  checkArgumentAux globalContext [] xs

def checkArgumentListAux
  (globalContext : Context) :
  List labeledArgument →
  Except String Context
  | [] => Except.ok globalContext
  | hd :: tl =>
    match checkArgument globalContext hd.argument with
    | Except.ok localContext =>
      if let Option.some labeled_statement := localContext.head?
      then checkArgumentListAux
        (
          {
            label := hd.label
            statement := labeled_statement.statement
          } :: globalContext
        )
        tl
      else checkArgumentListAux globalContext tl
    | Except.error message => Except.error s! "{hd.label}{LF}{message}"


def checkArgumentList
  (xs : List labeledArgument) :
  Except String Context :=
  checkArgumentListAux [] xs


def ExceptToString : Except String Context → String
  | Except.ok localContext => localContext.toString
  | Except.error E => E


#eval checkArgumentList []


#eval IO.print
(
  ExceptToString
  (
    checkArgumentList
    [
      ⟨ "id", [
          ⟨ "s1", (prop_2 (Formula.var_ "P") (Formula.imp_ (Formula.var_ "P") (Formula.var_ "P")) (Formula.var_ "P")) ⟩,
          ⟨ "s2", (prop_1 (Formula.var_ "P") (Formula.imp_ (Formula.var_ "P") (Formula.var_ "P"))) ⟩,
          ⟨ "s3", (mp "s1" "s2") ⟩,
          ⟨ "s4", (prop_1 (Formula.var_ "P") (Formula.var_ "P")) ⟩,
          ⟨ "s5", (mp "s3" "s4") ⟩ 
        ]
      ⟩
    ]
  )
)
