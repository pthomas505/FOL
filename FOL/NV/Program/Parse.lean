-- https://serokell.io/blog/parser-combinators-in-haskell
-- https://gist.github.com/heitor-lassarote/3e7314956e86b8227f6f6040e69aca9d

import FOL.NV.Formula

import Mathlib.Control.Basic


set_option autoImplicit false


inductive Error (i e : Type) : Type
  | EndOfInput : Error i e
  | ExpectedEndOfFile : i → Error i e
  | Expected : i → i → Error i e
  | Custom : e → Error i e
  deriving BEq, Repr

open Error


abbrev Offset : Type := Int


/--
  i : The input stream. For most cases this is going to be Char.
  e : The type of custom error messages.
  a : The type of the structure parsed from the consumed input.
--/
structure Parser (i e a : Type) : Type :=
  (runParser : List i → Offset →
    Except (List (Offset × Error i e)) (Offset × a × List i))


instance (i e : Type) : Functor (Parser i e) := {
  map :=
    fun {α β : Type} (f : α → β) (p : Parser i e α) => {
      runParser := fun (input : List i) (offset : Offset) => do
        let (offset', output, rest) ← p.runParser input offset
        return (offset', f output, rest) } }


instance (i e : Type) : Applicative (Parser i e) := {
  pure :=
    fun {α : Type} (a : α) => {
      runParser := fun (input : List i) (offset : Offset) => Except.ok (offset, a, input) },

  seq :=
    fun {α β : Type} (f : Parser i e (α → β)) (p : Unit → Parser i e α) => {
      runParser := fun (input : List i) (offset : Offset) => do
        let (offset', f', rest) ← f.runParser input offset
        let (offset'', output, rest') ← (p ()).runParser rest offset'
        return (offset'', f' output, rest') } }


instance (i e : Type) : Monad (Parser i e) := {
  pure := pure

  bind :=
    fun {α β : Type} (p : Parser i e α) (k : α → Parser i e β) => {
      runParser := fun (input : List i) (offset : Offset) => do
        let (offset', output, rest) ← p.runParser input offset
        let p' : Parser i e β := k output
        p'.runParser rest offset' } }


instance (i e : Type) [BEq i] [BEq e] : Alternative (Parser i e) := {
  failure := { runParser := fun (_ : List i) (_ : Offset) => Except.error [] }

  orElse := fun {α : Type} (l : Parser i e α) (r : Unit → Parser i e α) => {
    runParser := fun (input : List i) (offset : Offset) =>
      match l.runParser input offset with
      | Except.error err =>
          match (r ()).runParser input offset with
          | Except.error err' =>
              Except.error (List.eraseDups (err ++ err'))
          | Except.ok result => Except.ok result
      | Except.ok result => Except.ok result } }


def parse
  {i e a : Type}
  (p : Parser i e a)
  (input : List i) :
  Except (List (Offset × Error i e)) (Offset × a × List i) :=
  p.runParser input 0

def parseStr
  {e a : Type}
  (p : Parser Char e a)
  (input : String) :
  Except (List (Offset × Error Char e)) (Offset × a × List Char) :=
  parse p input.data


def eof
  (i e : Type) :
  Parser i e Unit := {
    runParser :=
      fun (input : List i) (offset : Offset) =>
        match input with
        | [] => Except.ok (offset, (), [])
        | hd :: _ => Except.error [(offset, ExpectedEndOfFile hd)] }


def satisfy
  {i e : Type}
  (mkErr : i → Error i e)
  (predicate : i → Bool) :
  Parser i e i := {
    runParser :=
      fun (input : List i) (offset : Offset) =>
        match input with
        | [] => Except.error [(offset, EndOfInput)]
        | hd :: tl =>
            if predicate hd
            then Except.ok (offset + 1, hd, tl)
            else Except.error [(offset, mkErr hd)] }


def exact_one
  {i : Type}
  [BEq i]
  (e : Type)
  (c : i) :
  Parser i e i :=
  satisfy (Expected c) (· == c)

def char
  (e : Type)
  (c : Char) :
  Parser Char e Char :=
  exact_one e c

#eval parseStr (char Unit 'a') ""
#eval parseStr (char Unit 'a') "a"
#eval parseStr (char Unit 'a') "b"


def exact_list
  {i : Type}
  [BEq i]
  (e : Type) :
  List i → Parser i e (List i)
  | [] => return []
  | x :: xs => do
    let y <- exact_one e x
    let ys <- exact_list e xs
    return (y :: ys)

def char_list
  (e : Type)
  (cs : List Char) :
  Parser Char e (List Char) :=
  exact_list e cs

def str
  (e : Type)
  (s : String) :
  Parser Char e String := do
  let cs ← char_list e s.data
  return cs.asString

#eval parseStr (str Unit "") ""
#eval parseStr (str Unit "") "a"
#eval parseStr (str Unit "a") "a"
#eval parseStr (str Unit "b") "a"
#eval parseStr (str Unit "ab") ""
#eval parseStr (str Unit "ab") "a"
#eval parseStr (str Unit "ab") "ab"
#eval parseStr (str Unit "ab") "ac"


def zero_or_one
  {i e a : Type}
  [BEq i]
  [BEq e]
  (p : Parser i e a) :
  Parser i e (Option a) := do
  try? p

def zero_or_one_char
  (e : Type)
  [BEq e]
  (c : Char) :
  Parser Char e String := do
  if let Option.some a ← zero_or_one (char e c)
  then return a.toString
  else return ""

#eval parseStr (zero_or_one_char Unit 'a') ""
#eval parseStr (zero_or_one_char Unit 'a') "b"
#eval parseStr (zero_or_one_char Unit 'a') "a"
#eval parseStr (zero_or_one_char Unit 'a') "ab"


partial def zero_or_more
  {i e a : Type}
  [BEq i]
  [BEq e]
  (p : Parser i e a) :
  Parser i e (Array a) := do
  let rec go (acc : Array a) := do
    match ← try? p with
    | none => return acc
    | some a => go (acc.push a)
  go #[]

def zero_or_more_char
  (e : Type)
  [BEq e]
  (c : Char) :
  Parser Char e String := do
  let a ← zero_or_more (char e c)
  return a.toList.asString

#eval parseStr (zero_or_more_char Unit 'a') ""
#eval parseStr (zero_or_more_char Unit 'a') "b"
#eval parseStr (zero_or_more_char Unit 'a') "bb"
#eval parseStr (zero_or_more_char Unit 'a') "a"
#eval parseStr (zero_or_more_char Unit 'a') "aa"
#eval parseStr (zero_or_more_char Unit 'a') "ab"
#eval parseStr (zero_or_more_char Unit 'a') "abb"


def one_or_more
  {i e a : Type}
  [BEq i]
  [BEq e]
  (p : Parser i e a) :
  Parser i e (Array a) := do
    let hd ← p
    let tl ← zero_or_more p
    return { data := hd :: tl.data }

def one_or_more_char
  (e : Type)
  [BEq e]
  (c : Char) :
  Parser Char e String := do
  let a ← one_or_more (char e c)
  return a.toList.asString

#eval parseStr (one_or_more_char Unit 'a') ""
#eval parseStr (one_or_more_char Unit 'a') "b"
#eval parseStr (one_or_more_char Unit 'a') "bb"
#eval parseStr (one_or_more_char Unit 'a') "a"
#eval parseStr (one_or_more_char Unit 'a') "aa"
#eval parseStr (one_or_more_char Unit 'a') "ab"
#eval parseStr (one_or_more_char Unit 'a') "aab"


#eval parseStr (char Unit 'a' <|> char Unit 'b') "a"
#eval parseStr (char Unit 'a' <|> char Unit 'b') "b"
#eval parseStr (char Unit 'a' <|> char Unit 'b') "c"

#eval parseStr ((failure <|> pure ()) : Parser Char Unit Unit) ""
#eval parseStr ((pure () <|> failure) : Parser Char Unit Unit) ""


def one_or_more_delimited
  {i e a1 a2 : Type}
  [BEq i]
  [BEq e]
  (delimiter : Parser i e a1)
  (p : Parser i e a2) :
  Parser i e (Array a2) := do
  let hd ← p
  let tl ← zero_or_more (delimiter *> p)
  return { data := hd :: tl.data }

def zero_or_more_delimited
  {i e a1 a2 : Type}
  [BEq i]
  [BEq e]
  (delimiter : Parser i e a1)
  (p : Parser i e a2) := do
  if let Option.some a ← zero_or_one (one_or_more_delimited delimiter p)
  then return a
  else return #[]


def whitespace :=
  satisfy (fun (c : Char) => Custom s! "Expected whitespace. Found '{c}'.") Char.isWhitespace

def alpha :=
  satisfy (fun (c : Char) => Custom s! "Expected alpha. Found '{c}'.") Char.isAlpha

def digit :=
  satisfy (fun (c : Char) => Custom s! "Expected digit. Found '{c}'.") Char.isDigit


def name := do
  let hd ← alpha <|> char String '_'
  let tl ← zero_or_more (alpha <|> digit <|> char String '_')
  return (Array.toList { data := hd :: tl.data }).asString

#eval parseStr name "_abc_0"


#eval parseStr (zero_or_more_delimited ((zero_or_more whitespace) *> char String ',' *> (zero_or_more whitespace)) name) "a , b , c"


open FOL.NV


mutual
  def takeFormula := do
    takePred <|>
    takeEq <|>
    takeTrue <|>
    takeFalse <|>
    takeNot <|>
    takeBin <|>
    takeForall <|>
    takeExists


  def takePred := do
    let pred_name ← name
    _ ← zero_or_more whitespace
    _ ← char String '('
    _ ← zero_or_more whitespace
    let delimiter := zero_or_more whitespace *> char String ',' *> zero_or_more whitespace
    let xs ← zero_or_more_delimited delimiter name
    _ ← zero_or_more whitespace
    _ ← char String ')'

    return Formula.pred_var_ (PredName.mk pred_name) (xs.toList.map (VarName.mk ∘ toString))


  def takeEq := do
    _ ← zero_or_more whitespace
    _ ← char String '('
    _ ← zero_or_more whitespace
    let x ← name
    _ ← zero_or_more whitespace
    _ ← char String '='
    _ ← zero_or_more whitespace
    let y ← name
    _ ← zero_or_more whitespace
    _ ← char String ')'

    return Formula.eq_ (VarName.mk x) (VarName.mk y)


  def takeTrue := do
    _ ← str String "T."
    return Formula.true_


  def takeFalse := do
    _ ← str String "F."
    return Formula.false_


  def takeNot := do
    _ ← char String '~'
    _ ← zero_or_more whitespace
    let phi ← takeFormula

    return (Formula.not_ phi)


  def takeBin := do
    _ ← char String '('
    _ ← zero_or_more whitespace
    let phi ← takeFormula
    _ ← zero_or_more whitespace
    let op ← str String "->" <|> str String "/\\" <|> str String "\\/" <|> str String "<->"
    _ ← zero_or_more whitespace
    let psi ← takeFormula
    _ ← zero_or_more whitespace
    _ ← char String ')'

    match op with
    | "->" => return Formula.imp_ phi psi
    | "/\\" => return Formula.and_ phi psi
    | "\\/" => return Formula.or_ phi psi
    | "<->" => return Formula.iff_ phi psi
    | _ => sorry


  def takeForall := do
    _ ← str String "A."
    _ ← zero_or_more whitespace
    let x ← name
    _ ← zero_or_more whitespace
    let phi ← takeFormula

    return Formula.forall_ (VarName.mk x) phi


  def takeExists := do
    _ ← str String "E."
    _ ← zero_or_more whitespace
    let x ← name
    _ ← zero_or_more whitespace
    let phi ← takeFormula

    return Formula.exists_ (VarName.mk x) phi
end


/-
def eoi (i e : Type) : Parser i e Unit :=
  {
    runParser :=
      fun (input : List i) =>
        match input with
        | [] => Except.ok ((), [])
        | hd :: _ => Except.error [Error.Unexpected hd]
  }


def empty (i e : Type) : Parser i e Unit :=
  {
    runParser :=
      fun (input : List i) => Except.ok ((), input)
  }


-- ordered pair
def compose
  (i e a1 a2 : Type)
  (p1 : Parser i e a1)
  (p2 : Parser i e a2) :
  Parser i e (a1 × a2) :=
    {
      runParser :=
        fun (input : List i) =>
          match p1.runParser input with
          | Except.ok (output_1, rest_1) =>
            match p2.runParser rest_1 with
            | Except.ok (output_2, rest_2) =>
                Except.ok ((output_1, output_2), rest_2)
            | Except.error err => Except.error err
          | Except.error err => Except.error err
    }


-- one of pair
def choice
  (i e a : Type)
  (p1 : Parser i e a)
  (p2 : Parser i e a) :
  Parser i e a :=
    {
      runParser :=
        fun (input : List i) =>
          match p1.runParser input with
          | Except.ok (output, rest) => Except.ok (output, rest)
          | Except.error _ => p2.runParser input
    }


-- zero or more

partial def zero_or_more_aux
  (i e a : Type)
  (p : Parser i e a)
  (acc : List a)
  (input : List i) :
  Except (List (Error i e)) (List a × List i) :=
  match p.runParser input with
  | Except.ok (output, rest) =>
      zero_or_more_aux i e a p (acc.concat output) rest
  | Except.error _ => Except.ok (acc, input)

def zero_or_more
  (i e a : Type)
  (p : Parser i e a) :
  Parser i e (List a) :=
    {
      runParser :=
        fun (input : List i) =>
          zero_or_more_aux i e a p [] input
    }


def zero_or_one
  (i e a : Type)
  (p : Parser i e a) :
  Parser i e (Option a) :=
    {
      runParser :=
        fun (input : List i) =>
          match p.runParser input with
        | Except.ok (output, rest) => Except.ok (Option.some output, rest)
        | Except.error _ => Except.ok (Option.none, input)
    }


-- one or more of parser
def one_or_more
  (i e a : Type)
  (p : Parser i e a) :
  Parser i e (List a) :=
    let q := compose i e a (List a) p (zero_or_more i e a p)
    {
      runParser :=
        fun (input : List i) =>
          match q.runParser input with
        | Except.ok ((fst, snd), rest) => Except.ok (fst :: snd, rest)
        | Except.error err => Except.error err
    }



-- ordered list of parsers
def compose_list (i e a : Type) (ps : List (Parser i e a)) : Parser i e (List a) :=
  if ps.isEmpty
  then fun _ => Except.error "Empty parser list."
  else List.foldl (compose i e a a) empty ps


-- one of list of parsers
def choice_list (ps : List Parser) : Parser :=
  List.foldl choice (fun (_ : String) => Except.error "Empty parser list.") ps


-- exact character
def match_one (c : Char) : Parser :=
  satisfy (fun (x : Char) => x = c) c.toString


-- ordered list of characters
def match_compose_list (cs : List Char) : Parser :=
  compose_list (cs.map match_one)


-- one of list of characters
def match_choice_list (cs : List Char) : Parser :=
  choice_list (cs.map match_one)


-- exact string
def match_string (s : String) : Parser :=
  match_compose_list s.data


-- one of 'a - z' or 'A - Z'
def match_alpha : Parser :=
  satisfy (Char.isAlpha) "alpha"


-- one of '0 - 9'
def match_digit : Parser :=
  satisfy (Char.isDigit) "digit"


-- alpha (alpha | digit | '_')*
def match_identifier : Parser :=
  compose_list [match_alpha, (zero_or_more (choice_list [match_alpha, match_digit, (match_one '_')]))]


#eval parse (choice (match_one 'e') (match_one 'a')) "abc"

#eval parse (zero_or_more (match_one 'a')) "aaabc"

#eval parse match_alpha "a"

#eval parse match_digit ""

#eval parse (compose_list []) "a"

#eval parse (compose_list [match_digit]) "a"

#eval parse (choice_list []) "a"

#eval parse (compose match_identifier eoi) "a_019a"

#eval parse (compose match_identifier eoi) "a_019a"


structure State : Type :=
  (consumed : String)
  (remaining : String)
  deriving Inhabited, Nonempty

def State.toString (state: State) : String :=
  s! "consumed: {state.consumed}\nremaining: {state.remaining}"

instance : ToString State :=
  { toString := fun (state : State) => state.toString }


def Parser : Type := String → Except String State

def parse (p : Parser) (s : String) : Except String State := p s


-- base parsers


def empty : Parser :=
  fun (s : String) => Except.ok { consumed := "", remaining := s }


-- end of input
def eoi : Parser :=
  fun (s : String) =>
    if s.isEmpty
    then Except.ok { consumed := "", remaining := s }
    else Except.error s! "Expected empty string. Found {s}."


-- single character predicate
def satisfy (p : Char → Bool) (e : String) : Parser :=
  fun (s : String) =>
    match s.data with
    | [] => Except.error s! "Expected {e}. Found empty string."
    | c :: cs =>
      if p c
      then Except.ok { consumed := c.toString, remaining := cs.asString }
      else Except.error s! "Expected {e}. Found {c}."


-- ordered pair of parsers
def compose (p1 : Parser) (p2 : Parser) : Parser :=
  fun (s : String) =>
    match parse p1 s with
    | Except.ok { consumed := a, remaining := s1 } =>
      match parse p2 s1 with
      | Except.ok { consumed := b, remaining := s2 } =>
        Except.ok { consumed := a ++ b, remaining := s2 }
      | e2 => e2
    | e1 => e1


-- one of pair of parsers
def choice (p1 : Parser) (p2 : Parser) : Parser :=
  fun (s : String) =>
    match parse p1 s with
    | Except.ok s => Except.ok s
    | Except.error _ => parse p2 s


-- zero or more of parser

partial def zero_or_more_aux (p : Parser) (acc : String) (s : String) : State :=
  match parse p s with
  | Except.ok { consumed := a, remaining := s1 } => zero_or_more_aux p (acc.append a) s1
  | Except.error _ => { consumed := acc, remaining := s }

def zero_or_more (p : Parser) : Parser :=
  fun (s : String) =>
    Except.ok (zero_or_more_aux p "" s)


-- derived parsers


def zero_or_one (p : Parser) : Parser :=
  choice p empty


-- one or more of parser
def one_or_more (p : Parser) : Parser :=
  compose p (zero_or_more p)


-- ordered list of parsers
def compose_list (ps : List Parser) : Parser :=
  if ps.isEmpty
  then fun _ => Except.error "Empty parser list."
  else List.foldl compose empty ps


-- one of list of parsers
def choice_list (ps : List Parser) : Parser :=
  List.foldl choice (fun (_ : String) => Except.error "Empty parser list.") ps


-- exact character
def match_one (c : Char) : Parser :=
  satisfy (fun (x : Char) => x = c) c.toString


-- ordered list of characters
def match_compose_list (cs : List Char) : Parser :=
  compose_list (cs.map match_one)


-- one of list of characters
def match_choice_list (cs : List Char) : Parser :=
  choice_list (cs.map match_one)


-- exact string
def match_string (s : String) : Parser :=
  match_compose_list s.data


-- one of 'a - z' or 'A - Z'
def match_alpha : Parser :=
  satisfy (Char.isAlpha) "alpha"


-- one of '0 - 9'
def match_digit : Parser :=
  satisfy (Char.isDigit) "digit"


-- alpha (alpha | digit | '_')*
def match_identifier : Parser :=
  compose_list [match_alpha, (zero_or_more (choice_list [match_alpha, match_digit, (match_one '_')]))]


#eval parse (choice (match_one 'e') (match_one 'a')) "abc"

#eval parse (zero_or_more (match_one 'a')) "aaabc"

#eval parse match_alpha "a"

#eval parse match_digit ""

#eval parse (compose_list []) "a"

#eval parse (compose_list [match_digit]) "a"

#eval parse (choice_list []) "a"

#eval parse (compose match_identifier eoi) "a_019a"

#eval parse (compose match_identifier eoi) "a_019a"
-/
