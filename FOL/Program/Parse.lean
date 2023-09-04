import Mathlib.Control.Basic
import Std.Data.String.Basic

import FOL.Program.Editor


/-
space = ' '
left_paren = '('
right_paren = ')'
ident = [a-z A-Z _] [a-z A-Z 0-9 _ ']+
formula_ = pred | eq | true | not | imp | forall
pred = ident (left_paren ident (space ident)* right_paren)?
eq = left_paren ident space 'eq' space ident right_paren
true = 'true'
not = left_paren 'not' space formula right_paren
imp = left_paren formula space 'imp' space formula right_paren
forall = left_paren 'forall' space ident space formula right_paren
-/


abbrev Parser := ReaderT String <| StateT String.Pos Option

def Parser.run
  {α : Type}
  (p : Parser α)
  (s : String) :
  Option α :=
  (·.1) <$> p s 0


-- match or fail
def parseChar
  (c : Char) :
  Parser Unit :=
  fun (s : String) (pos : String.Pos) =>
  guard (pos < s.endPos && s.get pos == c) *> pure ((), s.next pos)


-- match or fail
def parseEOF :
  Parser Unit :=
  fun (s : String) (pos : String.Pos) =>
  guard (pos == s.endPos) *> pure ((), pos)


-- match or fail
def parseString
  (tk : String) :
  Parser Unit :=
  fun s pos => do
  let s ← Substring.dropPrefix? ⟨s, pos, s.endPos⟩ tk.toSubstring
  pure ((), s.startPos)


def takeChar
  (f : Char → Bool) :
  Parser Char :=
  fun (s : String) (pos : String.Pos) =>
  let c := s.get pos
  if f c
  then pure (c, s.next pos)
  else none


-- zero or more
partial def takeWhile
  (f : Char → Bool) :
  Parser String :=
  fun (s : String) (start : String.Pos) =>
  let rec go pos :=
    if pos < s.endPos && f (s.get pos)
    then go (s.next pos)
    else pure (s.extract start pos, pos)
  go start


-- one or more
def takeWhile1
  (f : Char → Bool) :
  Parser String := do
  let s ← takeWhile f
  if s.isEmpty
  then none
  else pure s


-- Runs the given parser repeatedly until it fails.
partial def many
  {α : Type}
  (p : Parser α) :
  Parser (Array α) := do
  let rec go (acc : Array α) := do
    match ← try? p with
    | none => pure acc
    | some a => go (acc.push a)
  go #[]


def isAlpha (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

def isDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

def isAlphaOrDigit (c : Char) : Bool :=
  isAlpha c || isDigit c

def isIdentChar (c : Char) : Bool :=
  isAlphaOrDigit c || c == '_' || c == '\''


def parseIdent :
  Parser String := do
  let hd ← takeChar isAlpha
  let tl ← takeWhile isIdentChar
  pure (hd.toString ++ tl)

def parseIdentList :
  Parser (List String) := do
    parseChar '('
    let x ← parseIdent
    let xs ← many (parseChar ' ' *> parseIdent)
    parseChar ')'
    pure (x :: xs.toList)


/-
partial def parsePred : Parser Formula := do
  let X ← parseIdent
  let xs ← parseIdentList
  parseEOF
  pure (Formula.pred_ X xs)

#eval parsePred.run "P(a b)"
-/


def parseVar : Parser Formula := do
  let X ← parseIdent
  parseChar '('
  parseChar ')'
  pure (Formula.var_ X)

def parseTrue : Parser Formula := do
  parseChar 'T'
  pure (Formula.true_)

def parseFalse : Parser Formula := do
  parseChar 'F'
  pure (Formula.false_)

mutual
  partial def parseFormula :
    Parser Formula :=
    parseVar <|>
    parseTrue <|>
    parseFalse <|>
    parseNot <|>
    parseImp

  partial def parseNot : Parser Formula := do
    parseString "~ "
    let phi ← parseFormula
    pure (Formula.not_ phi)

  partial def parseImp : Parser Formula := do
    parseChar '('
    let phi ← parseFormula
    parseString " -> "
    let psi ← parseFormula
    parseChar ')'
    pure (Formula.imp_ phi psi)
end

#eval parseFormula.run "(~ P() -> ~ Q())"


def parseLabel :
  Parser String :=
  takeWhile1 isIdentChar


def parseNilList
  (α : Type) :
  Parser (List α) := do
  parseString "[]"
  pure []

def parseConsList
  (α : Type)
  (p : Parser α) :
  Parser (List α) := do
  parseChar '['
  let hd ← p
  let tl ← many (parseString ", " *> p)
  parseChar ']'
  pure (hd :: tl.toList)

def parseFormulaList :
  Parser (List Formula) :=
  parseNilList Formula <|> parseConsList Formula parseFormula


#eval parseFormulaList.run "[P(), Q(), ~ P()]"

def parse_thin :
  Parser Justification := do
  parseString "thin"
  parseChar ' '
  let label ← parseLabel
  parseChar ' '
  let xs ← parseFormulaList
  pure (Justification.thin_ label xs)

def parse_assume :
  Parser Justification := do
  parseString "assume"
  parseChar ' '
  let x ← parseFormula
  pure (Justification.assume_ x)

def parse_prop_true :
  Parser Justification := do
  parseString "prop_true"
  pure Justification.prop_true_

def parse_prop_1 :
  Parser Justification := do
  parseString "prop_1"
  parseChar ' '
  let phi ← parseFormula
  parseChar ' '
  let psi ← parseFormula
  pure (Justification.prop_1_ phi psi)

def parse_prop_2 :
  Parser Justification := do
  parseString "prop_2"
  parseChar ' '
  let phi ← parseFormula
  parseChar ' '
  let psi ← parseFormula
  parseChar ' '
  let chi ← parseFormula
  pure (Justification.prop_2_ phi psi chi)

def parse_prop_3 :
  Parser Justification := do
  parseString "prop_3"
  parseChar ' '
  let phi ← parseFormula
  parseChar ' '
  let psi ← parseFormula
  pure (Justification.prop_3_ phi psi)

def parse_mp :
  Parser Justification := do
  parseString "mp"
  parseChar ' '
  let major_step_label ← parseLabel
  parseChar ' '
  let minor_step_label ← parseLabel
  pure (Justification.mp_ major_step_label minor_step_label)

def parseTactic :
  Parser Justification :=
  parse_thin <|>
  parse_assume <|>
  parse_prop_true <|>
  parse_prop_1 <|>
  parse_prop_2 <|>
  parse_prop_3 <|>
  parse_mp


def parse_tactic :
  Parser (String × Justification) := do
  let label ← parseLabel
  parseChar '.'
  parseChar ' '
  let tactic ← parseTactic
  pure (label, tactic)


def parse_tactic_list :
  Parser (List (String × Justification)) := do
  let hd ← parse_tactic 
  let tl ← many (parseString "; " *> parse_tactic)
  pure (hd :: tl.toList)


#eval createStepList {} (Option.get! (parse_tactic_list.run "1. prop_true; 2. prop_true"))
