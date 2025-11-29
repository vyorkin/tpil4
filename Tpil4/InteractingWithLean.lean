-- Можно ожидать конкретные ошибки

#guard_msgs in
def x : Nat := "whatever"

-- Тут фишка не в том, что ты ассертишь ошибку,
-- а в том, что ты её как бы затыкаешь и можешь
-- посмотреть в выводе, короче в том, что скэпчурелось ёпт.
-- Вот можешь мышь (или чё там у тебя) навести на #guard_msgs и посмотреть.

-- Можно ловить указанные категории сообщений
-- (ошибок/ворнингов/сообщений)
#guard_msgs(error) in
#eval (sorry : Nat)

#guard_msgs(warning) in
#eval (sorry : Nat)

#guard_msgs in
#eval (sorry : Nat)

protected def Foo.bar : Nat := 1
open Foo

#guard_msgs in
#check bar

section
-- Можно импортировать только нужное
open Nat (succ zero gcd)
#check zero
#eval gcd 15 6
end

section
-- Можно прятать не нужное
open Nat hiding succ gcd
#check zero

#guard_msgs in
#eval gcd 15 6
end

namespace My1
  -- Можно создавать алиасы при импорте
  open Nat renaming mul → times, add → plus
  #eval plus (times 2 2) 3

  -- Можно экспортировать эти созданные алисы
  export Nat (succ add sub)
end My1

-- К большинству команд можно применять модификатор local.
-- Он позволяет ограничить область действия команды
-- текущим файлом, неймспейсом или секцией.

def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

namespace My2
  @[simp] theorem List.isPrefix_self (as : List α)
                  : isPrefix as as :=
    ⟨[], by simp⟩

  -- Ну или в любой произвольный момент можно применить атрибут к теореме:
  -- attribute [simp] List.isPrefix_self

  -- В обоих случаях этот атрибут будет активен везде, где
  -- импортируется что-либо из файла, в котором есть это применение атрубута.

  -- Но модификатором local можно ограничить область действия атрибута.
  -- attribute [local simp] List.isPrefix_self

  example : isPrefix [1, 2, 3] [1, 2, 3] := by simp
end My2

-- namespace My3
--   instance : LE (List α) where
--     le := isPrefix

--   theorem List.isPrefix_self (as : List α) : as ≤ as :=
--     ⟨[], by simp⟩
-- end My3

namespace My4
  def instLe : LE (List α) := { le := isPrefix }

  section
  attribute [local instance] instLe

  example (as : List α) : as ≤ as :=
    ⟨[], by simp⟩
  end

-- Если раскоментишь My3, то увидишь, что нотация тут
-- доступна и ошибки нет. Казалось бы так быть не должно,
-- я же изолировал её. Но она была определена выше в
-- неймспейсе My3 без модификатора local.
-- Неймспейс такое не изолирует.
#guard_msgs in
example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩
end My4

-- А вот действие опций распостраняется только на
-- текущую секцию (или неймспейс) данного файла.

namespace My5
  -- Слабые неявные аргументы.
  -- Это вот это вот внутри двух фигурных скобок.

  def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
    ∀ (a : α), r a a

  def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
    ∀ {{a b : α}}, r a b → r b a

  def transitive {α : Type u} (r : α → α → Prop) : Prop :=
    ∀ {{a b c : α}}, r a b → r b c → r a c

  def Euclidean {α : Type u} (r : α → α → Prop) : Prop :=
    ∀ {{a b c : α}}, r a b → r a c → r b c

  theorem th1 {α : Type u} {r : α → α → Prop}
              (reflr : reflexive r) (euclr : Euclidean r)
              : symmetric r :=
    fun {a b : α} =>
    fun (h : r a b) =>
    show r b a from euclr h (reflr _)

  theorem th2 {α : Type u} {r : α → α → Prop}
              (symmr : symmetric r) (euclr : Euclidean r)
              : transitive r :=
    fun {a b c : α} =>
    fun (rab : r a b) (rbc : r b c) =>
    euclr (symmr rab) rbc

  theorem th3 {α : Type u} {r : α → α → Prop}
              (reflr : reflexive r) (euclr : Euclidean r)
              : transitive r :=
    th2 (th1 reflr euclr) euclr

  -- Если бы мы использовали обычные неявные аргументы, то нам пришлось бы в
  -- th3 использовать @euclr, чтобы их "отменить" и передавать их явно.
  -- Иначе навставлялось бы слишком много неявных аргументов.
  --
  -- theorem th3 {α : Type u} {r : α → α → Prop}
  --             (reflr : reflexive r) (euclr : Euclidean r)
  --             : transitive r :=
  -- th2 (th1 reflr @euclr) @euclr

  variable (r : α → α → Prop)
  variable (euclr : Euclidean r)

  #check euclr

  -- Есть ещё третий тип неявных аргументов [arg].
  -- Он нужен для тайпклассов. Об этом позже будет.
end My5

namespace My6
  -- Нотации и их приоритет

  -- NOTE: Нотации вылазят за неймспейсы и секции.
  --       Поэтому закоментил.

  -- infixl:64 " + " => HAdd.hAdd -- лево-ассоциативная нотация
  -- infix:50  " = " => Eq        -- не ассоциативная нотация
  -- infixr:80 " ^ " => HPow.hPow -- право-ассоциативная нотация
  --         ^ ^ Тут пробелы не обязательны,
  --             это только для претти-принтинга

  -- prefix:100 "-"  => Neg.neg
  -- prefix:max "⁻¹" => Inv.inv

  -- Число после двоеточия означает как сильно оператор
  -- связывается со своими аргументами.

  -- На самом деле эти все нотационные команды выше
  -- (infixl, infixr, infix, prefix) транслируются в более общую
  -- команду notation. Т.е. вот эквивалетные определения нотаций выше:
  -- notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs -- infixl
  -- notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs        -- infix
  -- notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs -- infixr

  -- notation:100 "-" arg:100 => Neg.neg arg
  -- notation:1024 arg:1024 "⁻¹" => Inv.inv arg

  -- В нотации notation:65 lhs:65 " + " rhs:66
  -- `a + b + c` парсится как `(a + b) + c`
  -- но
  -- `a + b + c` НЕ парсится как `a + (b + c)`

  -- Закоментил, тк будет ругаться на то, что у нас несколько
  -- нотаций для сложения и равенства.
  --
  -- namespace My7
  --   variable (a b c : Nat)
  --   example : a + b + c = (a + b) + c := by rw [Nat.add_assoc]
  --   example : a + b + c = a + (b + c) := by rw [Nat.add_assoc]
  -- end My7
end My6

-- Приведение типов.
namespace My8
-- Можно, например, рассматривать натуральные числа как целые
-- там, где это нужно. Обычно линь справляется с приведением типов сам.
-- Но можно и явно это делать при помощи оператора ↑.

  variable (m n : Nat)
  variable (i j : Int)

  #check i + m       -- i + ↑m : Int
  #check i + m + j   -- i + (↑m + j) : Int
  #check i + ↑m + ↑n -- i + ↑m + ↑n : Int

end My8

namespace My9
  #check Eq
  #check @Eq

  #check Eq.symm
  #check @Eq.symm

  #print Eq
  #print Eq.symm
end My9

namespace My10
  -- Settings options:
  -- set_option <name> <value>

  -- Можно управлять претти-принтингом

  #check 2 + 2 = 4

  set_option pp.notation false -- Вкл/выкл отображение нотаций
  #check 2 + 2 = 4

  set_option pp.explicit true -- Показывать неявные аргументы
  #check 2 + 2 = 4

  set_option pp.universes true -- Отображать вселенные как параметры
  #check 2 + 2 = 4

  -- Влияют только на текущий скоуп или неймспейс.
end My10

namespace My11
  -- Можно вкл/выкл всё одной командой.

  #check 2 + 2 = 4

  set_option pp.all true
  #check 2 + 2 = 4

  set_option pp.all false
  #check 2 + 2 = 4

end My11

namespace My12
  #check @And.intro
  #check @And.casesOn
end My12

namespace My13
  universe u v w

  def compose₀ {α : Type u} {β : Type v} {γ : Type w}
      (g : β → γ) (f : α → β) (x : α) : γ :=
    g (f x)
end My13

namespace My14
  -- Вселенные можно передавать аргументами, а не определять снаружи.
  def compose₁.{u, v, w}
      {α : Type u} {β : Type v} {γ : Type w}
      (g : β → γ) (f : α → β) (x : α) : γ :=
    g (f x )
end My14

namespace My15
  -- Все не связанные идентификаторы будут добавлены
  -- как неявные аргументы автоматически.

  def compose₂ (g : β → γ) (f : α → β) (x : α) : γ :=
    g (f x)

  -- Линь вывел более общий Sort, вместо Type.
  #check @compose₂

end My15

namespace My16
  -- Такое автодобавление неявных аргументов можно отменить.
  -- Если оно путает.
  set_option autoImplicit false

  #guard_msgs in
  def compose₃ (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
  -- + error: Unknown identifier `β`
  -- + ---
  -- + error: Unknown identifier `γ`
  -- ...

end My16

namespace My17
  -- Неявные лямбды.

  set_option linter.unusedVariables false

  namespace Ex2
    def id1 : {α : Type} → α → α := fun x => x
    def listId : List ({α : Type} → α → α) := (fun x => x) :: []

    -- In this example, implicit lambda introduction
    -- has been disabled because we use `@` before {kw}`fun`
    def id2 : {α : Type} → α → α := @fun α (x : α) => id1 x
    def id3 : {α : Type} → α → α := @fun α x => id1 x
    def id4 : {α : Type} → α → α := fun x => id1 x

    -- In this example, implicit lambda introduction has been disabled
    -- because we used the binder annotation `{...}`
    def id5 : {α : Type} → α → α := fun {α} x => id1 x
  end Ex2
end My17

-- Сахар для функций.
namespace My18
  #check (· + 1) -- fun x ↦ x + 1 : Nat → Nat
  #check (2 - ·) -- fun x ↦ 2 - x : Nat → Nat

  #eval [1, 2, 3, 4, 5].foldl (· * ·) 1

  def f (x y z : Nat) := x + y + z
  #check (f · 1 ·)

  #eval [(1, 2), (3, 4), (5, 6)].map (·.1)

  #check (Prod.mk · (· + 1)) -- fun x ↦ (x, fun x ↦ x + 1)

end My18

namespace My19
  -- Вот так можно передавать именованные параметры.
  def sum (xs : List Nat) :=
    xs.foldl (init := 0) (·+·)

  #eval sum [1, 2, 3, 4]

  example {a b : Nat} {p : Nat → Nat → Nat → Prop}
          (h₁ : p a b b) (h₂ : b = a) :
          p a a b :=
    Eq.subst (motive := fun x => p a x b) h₂ h₁

  def f (x : Nat) (y : Nat := 1) (w : Nat := 2) (z : Nat) :=
    x + y + w - z

  example (x z : Nat) : f (z := z) x = x + 1 + 2 - z := rfl
  example (x z : Nat) : f x (z := z) = x + 1 + 2 - z := rfl
  example (x y : Nat) : f x y = fun z => x + y + 2 - z := rfl
  example : f = (fun x z => x + 1 + 2 - z) := rfl
  example (x : Nat) : f x = fun z => x + 1 + 2 - z := rfl
  example (y : Nat) : f (y := 5) = fun x z => x + 5 + 2 - z := rfl

  def g {α} [Add α] (a : α) (b? : Option α := none) (c : α) :=
    match b? with
    | none   => a + c
    | some b => a + b + c

  variable {α} [Add α]

  example : g = fun (a c : α) => a + c := rfl
  example (x : α) : g (c := x) = fun (a : α) => a + x := rfl
  example (x : α) : g (b? := some x) = fun (a c : α) => a + x + c := rfl

  example (x : α) : g x = fun (c : α) => x + c := rfl
  example (x y : α) : g x y = fun (c : α) => x + y + c := rfl
end My19

namespace My20
  -- Две точки (ellipses) удобно использовать в паттер-матчинге.

  inductive Term where
    | var (name : String)
    | num (val : Nat)
    | app (fn : Term) (arg : Term)
    | lambda (name : String) (type : Term) (body : Term)

  -- Вот тут нам не интересны остальные аргументы этого конструктора,
  -- мы вытаскиваем только название лямбды.
  def getBinderName : Term → Option String
    | Term.lambda (name := n) .. => some n
    | _ => none

  -- А здесь вытаскиваем только тип лямбды.
  def getBinderType : Term → Option Term
    | Term.lambda (type := t) .. => some t
    | _ => none

  -- Ещё с помощью двух точек можно попросить Lean
  -- вывести явные аргументы автоматически.
  example (f : Nat → Nat) (a b c : Nat)
          : f (a + b + c) = f (a + (b + c)) :=
    congrArg f (Nat.add_assoc ..)

end My20
