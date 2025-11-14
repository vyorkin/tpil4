def m : Nat := 1
def n : Nat := 0

def b1 : Bool := true
def b2 : Bool := false

#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
#check b1 && b2
#check b1 || b2
#check true

-- Single line comment

#eval 5 * 4
#eval m + 2
#eval b1 && b2

/- Multiline
Comment -/

#check Nat → Nat
#check Nat × Nat
#check Prod Nat Nat

#check (Nat → Nat) → Nat
#check Nat → (Nat → Nat)

#check Nat.succ
#check (0, 1)
#check Nat.add
#check Nat.succ 2
#eval Nat.succ 2
#check Nat.add 3
#check Nat.add 2 3
#eval Nat.add 2 3
#check (5, 9).1
#eval (5, 9).1
#eval (5, 9).2

#check Nat
#check Bool
#check Nat → Bool
#check Nat × Bool
#check Nat × Nat → Nat

def α : Type := Nat
def β : Type := Bool
def γ : Type := Nat → Nat

def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α
#check β
#check γ

#check F α
#check G α β
#check G α Nat

#check Prod α β
#check α × β

#check Type
#check Type 1
#check Type 2
#check Type 3

#check Prop
#check Sort 0
#check Sort 1

#check List Nat
#check List Type
#check List (Type 4)

#check Prod Nat Bool
#check Prod (Type 2) (Type 3)
#check Type 4 × Type 32
#check Type 14 × Type 9

universe uu
def P (α : Type uu) : Type uu := Prod α α
#check P

def Q.{un} (α : Type un) : Type un := α × α
#check Q

#check fun (x : Nat) => x + 5
#check λ (x : Nat) => x + 5

#check fun x => x + 5
#check λ x => x + 5

#eval (λ x : Nat => 5 + x) 10

#check fun x : Nat =>
  fun y : Bool =>
    if !y then x + 1 else x + 2

#check fun (x : Nat) (y : Bool) =>
  if !y then x + 1 else x + 2

#check λ x y =>
  if !y then x + 1 else x + 2


def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x
#check λ _ : Nat => true

#check fun x : Nat => g (f x)
#check fun x => g (f x)

#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)

def double0 (x : Nat) : Nat := x + x
def double1 : Nat → Nat := λ x => x + x
def double2 := λ (x : Nat) => x + x
#eval double0 3
#eval double1 3
#eval double2 3

def pi := 3.141592

def add0 (x y : Nat) := x + y
def add1 (x : Nat) (y : Nat) := x + y
#eval add0 2 3
#eval add1 2 3

def max(x y : Nat) :=
  if x > y
  then x
  else y

#check let y := 2 + 2; y * y
#eval let y := 2 + 2; y * y

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2

#check let y := 2 + 2; let z := y + y; z * z
#eval let y := 2 + 2; let z := y + y; z * z


def t (x : Nat) : Nat :=
   let y := x + x
   y * y


def compose0 (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

variable (α β γ : Type)
def compose1 (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)


section foo
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose2 := g (f x)
end foo

namespace Foo
  def aa : Nat := 5
  def ff (x : Nat) : Nat := x + 7

  #check ff aa
  #eval ff aa
end Foo

#check Foo.aa
#check Foo.ff

#check List.nil
#check List.cons
#check List.map

namespace Foo
  def bb : Nat := 3
end Foo

namespace Bar
  namespace Baz
    namespace Qux
      def cc : Nat := 5
    end Qux
  end Baz
end Bar

#check Bar.Baz.Qux.cc

#check @List.cons

namespace SigmaTypes
  universe u0 u1

  def f (α : Type u0) (β : α → Type u1) (a : α) (b : β a) :
    (a : α) × β a := Sigma.mk a b

  def g (α : Type u0) (β : α → Type u1) (a : α) (b : β a) :
    (a : α) × β a := ⟨a, b⟩

  def h1 (x : Nat) : Nat :=
    (f Type (fun α => α) Nat x).2

  -- (a : Type) × (Nat → Nat) Nat

  #eval h1 5
end SigmaTypes

namespace Lst
  universe u

  def T (α : Type u) : Type u := List α

  def cons {α : Type u} (a : α) (as : T α) : T α :=
    List.cons a as

  def nil {α : Type u} : T α :=
    List.nil

  def append {α : Type u} (as bs : T α) :=
    List.append as bs
end Lst

#check Lst.cons 0 Lst.nil

def as : Lst.T Nat := Lst.nil
def bs : Lst.T Nat := Lst.cons 5 as

#check Lst.append as bs

universe uuu
def ident {α : Type uuu} (x : α) := x

#check ident
#check ident 1
#check ident true
#check ident "hooy"

section
  universe u
  variable {α : Type u}
  variable (x : α)
  def identity := x
end

#check identity
#check identity true

#check id
#check (id : Nat -> Nat)
#check (id : Bool -> Bool)

#check 2
#check (2 : Int)

#check @id Nat
