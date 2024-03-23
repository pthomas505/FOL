
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
