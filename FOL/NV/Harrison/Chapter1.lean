set_option autoImplicit false


inductive Expression : Type
  | var : String → Expression
  | const : Int → Expression
  | add : Expression → Expression → Expression
  | mul : Expression → Expression → Expression

def Expression.toString : Expression → String
  | var x => x
  | const n => n.repr
  | add a b => s! "{a.toString} + {b.toString}"
  | mul a b => s! "{a.toString} * {b.toString}"

instance : ToString Expression :=
  { toString := fun (e : Expression) => e.toString }


open Expression


def simplify1 : Expression → Expression
  | add (const m) (const n) => const (m + n)
  | mul (const m) (const n) => const (m * n)
  | add (const 0) x => x
  | add x (const 0) => x
  | mul (const 0) _ => const 0
  | mul _ (const 0) => const 0
  | mul (const 1) x => x
  | mul x (const 1) => x
  | e => e

def simplify : Expression → Expression
  | add e1 e2 => simplify1 (add (simplify e1) (simplify e2))
  | mul e1 e2 => simplify1 (mul (simplify e1) (simplify e2))
  | e => e

#eval simplify (add (mul (add (mul (const 0) (var "x")) (const 1)) (const 3)) (const 12))


def space := String.contains " \t\n\r"
def punctuation := String.contains "()[]{},"
def symbolic := String.contains "~`!@#$%^&*-+=|\\:;<>.?/"
def numeric := String.contains "0123456789"
def alphanumeric := String.contains "abcdefghijklmnopqrstuvwxyz_'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"

def lexWhileAux
  (prop : Char → Bool)
  (acc : List Char) :
  List Char → List Char × List Char
  | [] => (acc, [])
  | c :: cs =>
    if prop c
    then
      lexWhileAux prop (acc ++ [c]) cs
    else (acc, c :: cs)

def lexWhile
  (prop : Char → Bool)
  (inp : String) :
  String × String :=
  let (left, right) := lexWhileAux prop [] inp.toList
  (left.asString, right.asString)


#eval lexWhile alphanumeric "abc"
