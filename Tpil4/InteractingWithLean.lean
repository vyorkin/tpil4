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
  -- attribute [local instance] instLe объявляет instLe инстансом тайпкласса LE,
  -- но только внутри данной секции. После end этот инстанс перестаёт действовать.
  -- Это важно, когда нужно временно дать Lean понять, как интерпретировать ≤,
  -- не засоряя глобальное пространство инстансов.

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

  -- Разница между {a b : α} и {{a b : α}}:
  --
  -- {a b : α} — обычный неявный аргумент: Lean вставляет его автоматически
  -- при каждом применении функции, даже когда это не нужно. Elaborator
  -- пытается угадать значение через унификацию типов прямо на месте вызова.
  --
  -- {{a b : α}} — слабый (semi-implicit / weak) неявный аргумент: Lean
  -- не вставляет его автоматически, пока в контексте нет следующего
  -- явного аргумента, который мог бы зафиксировать его значение.
  -- Фактически, слабый неявный аргумент унифицируется только тогда,
  -- когда elaborator встречает следующий аргумент в позиции применения.
  --
  -- Для свойств вроде symmetric/transitive/Euclidean это критично:
  -- они принимают r a b, r b a и т.п., и если a, b, c сделать обычными
  -- неявными, Lean будет пытаться вставить их в th3 каждый раз при
  -- упоминании euclr — и вставит лишние дыры, которые не унифицируются.
  -- Со слабыми {{ }} этого не происходит: Lean ждёт, пока увидит
  -- конкретный аргумент типа (r a b), и только тогда выводит a и b.

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
  -- Конкретнее: если Euclidean определена через {a b c : α}, то при каждом
  -- упоминании euclr elaborator немедленно пытается заполнить a, b, c
  -- через унификацию с тем, что есть в контексте. В th3 контекст неполный —
  -- мы ещё не знаем конкретных a b c — и Lean вставляет "дыры" с метапеременными.
  -- В результате `th1 reflr euclr` не типизируется без явного указания аргументов.
  -- @euclr отключает автовставку всех неявных аргументов для данного применения,
  -- после чего можно передавать их вручную.
  --
  -- С {{ }} этой проблемы нет: Lean просто не трогает a b c до тех пор,
  -- пока не увидит конкретный пропозициональный аргумент (r a b), из которого
  -- выведет нужные типы сам.
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

  -- Как работают приоритеты нотаций:
  --
  -- Число после notation: — это приоритет самой нотации (насколько "сильно"
  -- она связывает выражение целиком). Числа в lhs:N и rhs:N — это минимальные
  -- приоритеты, которые обязаны иметь подвыражения слева и справа.
  --
  -- Для notation:65 lhs:65 " + " rhs:66 (infixl):
  --   - сама нотация имеет приоритет 65
  --   - левый операнд должен иметь приоритет ≥ 65
  --   - правый операнд должен иметь приоритет ≥ 66
  --
  -- Почему это делает её лево-ассоциативной:
  --   a + b + c парсится как (a + b) + c, потому что:
  --   - результат первого (+) имеет приоритет 65
  --   - для следующего (+) lhs:65 требует ≥ 65, и 65 ≥ 65 — условие выполнено,
  --     поэтому (a + b) может быть левым операндом следующего +
  --   - но rhs:66 требует ≥ 66, а вложенный + даёт только 65 — не проходит,
  --     поэтому a + (b + c) не может быть правым аргументом первого +
  --
  -- Для infixr (напр. ^) rhs:80 < notation:80, то есть rhs допускает
  -- такой же приоритет справа, а lhs:81 > 80 — не допускает. Это обратная
  -- картина: вложение справа разрешено, вложение слева — нет.
  --
  -- Для infix (=) оба операнда имеют приоритет на 1 выше, чем нотация,
  -- поэтому ни с одной стороны другой = не вложится — нотация не ассоциативна.

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

-- Как работает ↑ под капотом:
--
-- Оператор ↑ — это синтаксический сахар, за которым стоит тайпкласс Coe.
-- Когда Lean видит ↑e или когда нужно привести тип автоматически,
-- он ищет инстанс Coe α β (или CoeTC, CoeDep — иерархия коэрций).
-- Если такой инстанс найден, Lean вставляет вызов Coe.coe e.
--
-- Для Nat → Int существует инстанс:
--   instance : Coe Nat Int := ⟨Int.ofNat⟩
--
-- Поэтому ↑m разворачивается в Int.ofNat m.
--
-- Lean умеет цепочечно применять коэрции: если есть Coe α β и Coe β γ,
-- то Coe α γ выводится автоматически через CoeTC. Это позволяет не
-- определять каждую пару типов отдельно.
--
-- В выражении i + m Lean смотрит на тип i : Int, понимает, что
-- нужен Int → Int → Int, и ищет способ привести m : Nat к Int.
-- Находит инстанс Coe Nat Int и вставляет ↑m неявно.

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

  -- Как работает autoImplicit:
  --
  -- Когда autoImplicit включён (значение по умолчанию), elaborator Lean
  -- смотрит на тело и сигнатуру определения, собирает все идентификаторы,
  -- которые не объявлены нигде выше, и автоматически добавляет их как
  -- неявные аргументы в начало сигнатуры. Так что:
  --
  --   def compose₂ (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
  --
  -- автоматически становится чем-то вроде:
  --
  --   def compose₂.{u₁ u₂ u₃} {α : Sort u₁} {β : Sort u₂} {γ : Sort u₃}
  --       (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
  --
  -- Lean использует Sort вместо Type, потому что не знает заранее, являются
  -- ли типы данными (Type) или пропозициями (Prop). Sort охватывает оба случая.
  -- Это видно в выводе #check @compose₂ ниже.

  def compose₂ (g : β → γ) (f : α → β) (x : α) : γ :=
    g (f x)

  -- Линь вывел более общий Sort, вместо Type.
  #check @compose₂

end My15

namespace My16
  -- Такое автодобавление неявных аргументов можно отменить.
  -- Если оно путает.
  set_option autoImplicit false

  -- При autoImplicit false Lean перестаёт автоматически вставлять
  -- неявные параметры для неизвестных идентификаторов. Любая переменная
  -- в сигнатуре должна быть явно объявлена — либо в параметрах функции,
  -- либо через variable. Это помогает поймать опечатки и сделать
  -- код более явным и предсказуемым.

  #guard_msgs in
  def compose₃ (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
  -- + error: Unknown identifier `β`
  -- + ---
  -- + error: Unknown identifier `γ`
  -- ...

end My16

namespace My17
  -- Неявные лямбды.

  -- Implicit lambda — это механизм, при котором Lean автоматически
  -- оборачивает лямбда-выражение в дополнительные неявные аргументы,
  -- чтобы совместить тип выражения с ожидаемым типом.
  --
  -- Пример: если ожидается тип {α : Type} → α → α, а мы пишем
  -- fun x => x, Lean сам добавляет снаружи fun {α} => fun x => x.
  -- Это происходит автоматически, когда elaborator видит, что
  -- ожидаемый тип начинается с неявного пи-типа ({...} → ...).
  --
  -- Как отключить implicit lambda введение:
  -- 1. Использовать @ перед fun: @fun α (x : α) => ...
  --    @ снимает автоматическое введение неявных аргументов для этой лямбды.
  -- 2. Написать первый параметр в фигурных скобках явно: fun {α} x => ...
  --    В этом случае Lean понимает, что мы сами управляем неявными параметрами.

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
  -- (· + 1) — это анонимный конструктор функции через точку-дырку (placeholder).
  -- Lean разворачивает его в fun x => x + 1.
  -- Под капотом происходит следующее: каждая · — это свежая переменная,
  -- которую Lean связывает слева направо в лямбду. Тип выводится из контекста
  -- (если он известен) или из первого использования.
  --
  -- (· + 1) : Nat → Nat — потому что 1 : Nat, значит + ожидает Nat слева,
  -- и Lean выводит тип аргумента как Nat.
  --
  -- (f · 1 ·) — две дырки, два аргумента: fun a b => f a 1 b
  -- Позиции дырок соответствуют позициям аргументов в результирующей функции.
  --
  -- (·.1) — доступ к первому проекции пары: fun p => p.1
  -- (Prod.mk · (· + 1)) — две вложенные дырки: fun x => (x, fun y => y + 1)
  -- Внешняя · — аргумент Prod.mk, внутренняя · — аргумент лямбды внутри.

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

  -- Как работает (..) в паттерн-матчинге:
  --
  -- Term.lambda имеет три поля: name, type, body.
  -- Обычный паттерн: Term.lambda n t b — нужно дать имя всем трём.
  -- Если нас интересует только одно поле, можно использовать именованный
  -- доступ: (name := n), а остальные поля заменить на .. (двойные точки).
  --
  -- .. означает "заполни все оставшиеся поля конструктора анонимными
  -- паттернами" (аналог _ для каждого из них). Lean автоматически
  -- подставляет _ на место каждого незаданного поля.
  --
  -- Это удобно, когда конструктор имеет много полей — не нужно
  -- писать кучу _, а читается так: "мне важно только это поле, остальное не важно".
  --
  -- Кроме того, (..) можно использовать в применении функций для автоматического
  -- вывода явных аргументов из контекста:

  -- Ещё с помощью двух точек можно попросить Lean
  -- вывести явные аргументы автоматически.
  example (f : Nat → Nat) (a b c : Nat)
          : f (a + b + c) = f (a + (b + c)) :=
    congrArg f (Nat.add_assoc ..)

  -- congrArg f h : если h : a = b, то congrArg f h : f a = f b
  -- То есть congrArg позволяет подставить равенство под функцию f.
  -- Здесь нам нужно доказать f (a + b + c) = f (a + (b + c)),
  -- и достаточно показать, что аргументы равны: a + b + c = a + (b + c).
  -- Это даёт Nat.add_assoc a b c.
  --
  -- Вместо того чтобы писать Nat.add_assoc a b c явно, мы пишем
  -- Nat.add_assoc .. — и Lean сам выводит a, b, c из контекста,
  -- а именно из типа, который ожидается в данном месте.
  -- Elaborator смотрит, что congrArg f нужен аргумент типа
  -- a + b + c = a + (b + c), и подставляет a, b, c в Nat.add_assoc.
  -- Точки .. — это "дай мне столько явных аргументов, сколько нужно,
  -- и выведи их из ожидаемого типа".

end My20
