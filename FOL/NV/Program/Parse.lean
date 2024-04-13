-- https://serokell.io/blog/parser-combinators-in-haskell
-- https://gist.github.com/heitor-lassarote/3e7314956e86b8227f6f6040e69aca9d

import FOL.NV.Formula


inductive Error (i e : Type) : Type
  | EndOfInput : Error i e
  | Unexpected : i → Error i e
  | Expected : i → i → Error i e
  | ExpectedEndOfFile : i → Error i e
  | CustomError : e → Error i e
  | Empty : Error i e
  deriving DecidableEq, Repr

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


def parse
  {i e a : Type}
  (p : Parser i e a)
  (input : List i) :
  Except (List (Offset × Error i e)) (Offset × a × List i) :=
  p.runParser input 0


def token
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


def satisfy
  (i e : Type)
  (predicate : i → Bool) :
  Parser i e i :=
  token Unexpected predicate


def char
  (i e : Type)
  [BEq i]
  (c : i) :
  Parser i e i :=
  token (Expected c) (· == c)


#eval parse (char Char Unit 'h') "hello".data
#eval parse (char Char Unit 'h') "greetings".data
#eval parse (char Char Unit 'h') "".data


def eof
  (i e : Type) :
  Parser i e Unit := {
    runParser :=
      fun (input : List i) (offset : Offset) =>
        match input with
        | [] => Except.ok (offset, (), [])
        | hd :: _ => Except.error [(offset, ExpectedEndOfFile hd)] }


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


def string
  (i e : Type)
  [BEq i] :
  List i → Parser i e (List i)
  | [] => pure []
  | x :: xs => do
    let y <- char i e x
    let ys <- string i e xs
    return (y :: ys)


#eval parse (string Char String "Haskell".data) "Haskell".data
#eval parse (string Char String "Haskell".data) "Halloween".data


instance (i e : Type) [BEq (Error i e)] : Alternative (Parser i e) := {
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


#eval parse (string Char String "hello".data <|> string Char String "greetings".data) "hello, world".data

#eval parse (string Char String "hello".data <|> string Char String "greetings".data) "greetings, world".data

#eval parse (string Char String "hello".data <|> string Char String "greetings".data) "bye, world".data

#eval parse ((failure <|> pure ()) : Parser Char Unit Unit) "".data

#eval parse ((pure () <|> failure) : Parser Char Unit Unit) "".data

#eval parse ((string Char String "hello".data *> string Char String ", globe".data) <|> string Char String "greetings".data) "hello, world".data


def zero_or_one
  {i e a : Type}
  (p : Parser i e a) :
  Parser i e (Option a) := {
    runParser := fun (input : List i) (offset : Offset) =>
      match p.runParser input offset with
      | Except.ok (offset, output, rest) => Except.ok (offset + 1, Option.some output, rest)
      | Except.error _ => Except.ok (offset, Option.none, input) }


partial def zero_or_more_aux
  {i e a : Type}
  (p : Parser i e a)
  (acc : List a)
  (input : List i)
  (offset : Offset) :
  Except (List (Offset × Error i e)) (Offset × (List a) × List i) :=
  match p.runParser input offset with
  | Except.ok (offset, output, rest) => zero_or_more_aux p (acc ++ [output]) rest (offset + 1)
  | Except.error _ => Except.ok (offset, acc, input)

def zero_or_more
  {i e a : Type}
  (p : Parser i e a) :
  Parser i e (List a) := {
    runParser := fun (input : List i) (offset : Offset) =>
      zero_or_more_aux p [] input offset }


def one_or_more
  {i e a : Type}
  (p : Parser i e a) :
  Parser i e (List a) := {
    runParser := fun (input : List i) (offset : Offset) => do
      let (offset', hd, rest) ← p.runParser input offset
      let (offset'', tl, rest') ← (zero_or_more p).runParser rest (offset' + 1)
      return (offset'', (hd :: tl), rest') }


def whitespace :=
  token (fun (c : Char) => CustomError s! "Expected whitespace. Found '{c}'.") Char.isWhitespace

def alpha :=
  token (fun (c : Char) => CustomError s! "Expected alpha. Found '{c}'.") Char.isAlpha

def digit :=
  token (fun (c : Char) => CustomError s! "Expected digit. Found '{c}'.") Char.isDigit

def underscore :=
  token (fun (c : Char) => CustomError s! "Expected underscore. Found '{c}'.") (· == '_')

def left_paren :=
  token (fun (c : Char) => CustomError s! "Expected left parenthesis. Found '{c}'.") (· == '(')

def right_paren :=
  token (fun (c : Char) => CustomError s! "Expected right parenthesis. Found '{c}'.") (· == ')')


def ident : Parser Char String String := do
  let hd ← (alpha <|> underscore)
  let tl ← zero_or_more (alpha <|> digit <|> underscore)
  return (hd :: tl).asString

#eval parse ident "_abc_0".data


def ident_list := do
  let hd ← ident
  let tl ← (zero_or_more ((zero_or_more whitespace) *> ident))
  return hd :: tl


open FOL.NV


def pred := do
  let pred_name ← ident
  let _ ← zero_or_more whitespace *> left_paren *> zero_or_more whitespace
  let ident_list_option ← zero_or_one ident_list
  let _ ← zero_or_more whitespace *> right_paren
  match ident_list_option with
  | Option.some ident_list =>
      return Formula.pred_var_ (PredName.mk pred_name) (ident_list.map VarName.mk)
  | Option.none =>
      return Formula.pred_var_ (PredName.mk pred_name) []

#eval parse pred "P(a b c)".data


def eq := do
  let _ ← left_paren *> zero_or_more whitespace
  let x ← ident
  let _ ← zero_or_more whitespace *> char Char String '=' *> zero_or_more whitespace
  let y ← ident
  let _ ← zero_or_more whitespace *> right_paren
  return Formula.eq_ (VarName.mk x) (VarName.mk y)

#eval parse eq "(a = b)".data


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
