-- в lean 4 каждый терм имеет тип. `def` вводит глобальное определение.
-- аннотация `: Nat` — это не просто подсказка компилятору, а обязательная часть
-- системы типов: lean проверяет, что правая часть действительно имеет тип Nat.
def m : Nat := 1
def n : Nat := 0

def b1 : Bool := true
def b2 : Bool := false

-- `#check` — команда, которая печатает тип выражения в режиме проверки.
-- она не вычисляет значение, а только проверяет типы. это статический анализ.
-- результат выводится как info-сообщение в редакторе.
#check m
#check n
-- `n + 0` — это выражение, lean выводит его тип как Nat, потому что (+) на Nat → Nat → Nat.
#check n + 0
#check m * (n + 0)
#check b1
-- `&&` — логическое "и" на Bool. возвращает Bool.
#check b1 && b2
-- `||` — логическое "или" на Bool.
#check b1 || b2
#check true

-- Single line comment

-- `#eval` — команда вычисления. в отличие от `#check`, она действительно
-- запускает программу и выводит результат. работает для типов, у которых
-- есть инстанс класса Repr (или Inhabited + Eval).
#eval 5 * 4
#eval m + 2
#eval b1 && b2

/- Multiline
Comment -/

-- типы функций записываются через →. `Nat → Nat` — тип функции, принимающей
-- Nat и возвращающей Nat. стрелка правоассоциативна, поэтому
-- `Nat → Nat → Nat` читается как `Nat → (Nat → Nat)` — функция, возвращающая функцию.
#check Nat → Nat
-- `Nat × Nat` — тип декартова произведения, пара натуральных чисел.
-- это синтаксический сахар для `Prod Nat Nat`.
#check Nat × Nat
-- `Prod Nat Nat` — то же самое, но запись через явное применение конструктора типа.
-- lean позволяет обе формы, они полностью эквивалентны.
#check Prod Nat Nat

-- `(Nat → Nat) → Nat` — тип функции высшего порядка: принимает функцию
-- из Nat в Nat и возвращает Nat. скобки здесь обязательны.
#check (Nat → Nat) → Nat
-- `Nat → (Nat → Nat)` — функция, возвращающая функцию. это каррирование.
-- в lean все многоаргументные функции реализованы через каррирование:
-- `f : Nat → Nat → Nat` — это функция, которая принимает один Nat и
-- возвращает функцию `Nat → Nat`. частичное применение бесплатно.
#check Nat → (Nat → Nat)

#check Nat.succ
#check (0, 1)
#check Nat.add
-- `Nat.succ 2` — частичное применение: Nat.succ принимает один аргумент.
-- тип `Nat.succ` — `Nat → Nat`, поэтому `Nat.succ 2 : Nat`.
#check Nat.succ 2
#eval Nat.succ 2
-- `Nat.add 3` — частичное применение двухаргументной функции.
-- тип `Nat.add` — `Nat → Nat → Nat`, значит `Nat.add 3 : Nat → Nat`.
-- это не ошибка — это новая функция, прибавляющая 3.
#check Nat.add 3
#check Nat.add 2 3
#eval Nat.add 2 3
-- `.1` и `.2` — проекции кортежа (поля структуры Prod).
-- `(5, 9).1` возвращает первый элемент пары.
#check (5, 9).1
#eval (5, 9).1
#eval (5, 9).2

-- `#check Nat` выводит `Nat : Type`. это означает, что сам Nat — это тип,
-- и тип типа Nat называется Type (или Type 0).
#check Nat
#check Bool
-- `Nat → Bool` — не значение, а тип. lean позволяет писать #check для типов.
#check Nat → Bool
#check Nat × Bool
-- `Nat × Nat → Nat` — тип функции из пары в Nat.
-- отличие от `Nat → Nat → Nat`: первая принимает пару (один аргумент типа Nat × Nat),
-- вторая — два отдельных аргумента через каррирование.
#check Nat × Nat → Nat

-- типы сами могут быть значениями, которым можно давать имена через `def`.
-- α, β, γ здесь — переменные уровня типов, их тип — `Type`.
def α : Type := Nat
def β : Type := Bool
def γ : Type := Nat → Nat

-- конструкторы типов — функции из типов в типы. `List : Type → Type` принимает
-- тип элементов и возвращает тип списков. `Prod : Type → Type → Type` — аналогично для пар.
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α
#check β
#check γ

-- `F α` = `List Nat`, `G α β` = `Prod Nat Bool` — применение конструктора типа.
#check F α
#check G α β
#check G α Nat

-- `Prod α β` и `α × β` — абсолютно одно и то же в lean 4.
-- `×` — инфиксная нотация для Prod, определённая через macro.
#check Prod α β
#check α × β

-- иерархия вселенных в lean 4:
-- `Type` = `Type 0` — вселенная обычных типов (Nat, Bool, List Nat, ...).
-- `Type 1` — вселенная типов, элементами которой являются обитатели Type 0.
--   например, `Type 0 : Type 1`, сам `Type : Type 1`.
-- `Type 2` — вселенная типов, включающая Type 1, и так далее.
-- это нужно для избегания парадокса Расселла: нельзя сказать `Type : Type`,
-- поэтому каждый Type живёт в следующей вселенной.
#check Type
#check Type 1
#check Type 2
#check Type 3

-- `Prop` — вселенная пропозиций (логических утверждений).
-- `Prop = Sort 0`. пропозиции в lean — это типы, доказательство = обитатель типа.
-- `Sort 0 = Prop`, `Sort 1 = Type 0`, `Sort 2 = Type 1`, ...
-- `Sort u` — обобщение, которое работает одновременно для Prop и Type.
#check Prop
#check Sort 0
#check Sort 1

-- `List Nat : Type 0`, `List Type : Type 1` — уровень вселенной результата
-- определяется уровнем аргумента. List полиморфен по вселенной.
#check List Nat
#check List Type
#check List (Type 4)

-- `Prod Nat Bool : Type 0`, `Prod (Type 2) (Type 3) : Type 4` —
-- тип произведения живёт в максимуме вселенных своих аргументов + 1 (для Type).
-- точнее, `Prod : Type u → Type v → Type (max u v)`.
#check Prod Nat Bool
#check Prod (Type 2) (Type 3)
#check Type 4 × Type 32
#check Type 14 × Type 9

-- `universe uu` объявляет переменную уровня вселенной. это нужно для
-- universe polymorphism — написания кода, который работает для любого уровня.
-- без этого пришлось бы писать отдельные версии для Type, Type 1, Type 2 и т.д.
universe uu
-- `P` — функция из типа уровня uu в тип уровня uu. возвращает `Prod α α`.
-- благодаря universe uu, `P` работает для `P Nat : Type`, `P (Type) : Type 1`, ...
def P (α : Type uu) : Type uu := Prod α α
#check P

-- альтернативный синтаксис: уровень вселенной можно объявить inline через `.{un}`.
-- это эквивалентно `universe un` + использование в сигнатуре.
def Q.{un} (α : Type un) : Type un := α × α
#check Q

-- лямбда-выражения: `fun x => expr` или `λ x => expr` (λ — синоним fun).
-- это анонимные функции. тип аргумента здесь аннотирован явно `: Nat`.
#check fun (x : Nat) => x + 5
#check λ (x : Nat) => x + 5

-- lean может вывести тип аргумента из контекста: `x + 5` требует Nat,
-- поэтому аннотация необязательна. вывод типов работает в обе стороны.
#check fun x => x + 5
#check λ x => x + 5

-- применение лямбды к аргументу: `(λ x : Nat => 5 + x) 10` вычисляет `5 + 10 = 15`.
#eval (λ x : Nat => 5 + x) 10

-- многоаргументные функции через вложенные лямбды.
-- `fun x : Nat => fun y : Bool => ...` — это функция x : Nat → (y : Bool → Nat).
-- тип результата: `Nat → Bool → Nat`.
#check fun x : Nat =>
  fun y : Bool =>
    if !y then x + 1 else x + 2

-- lean позволяет записать несколько аргументов в одной лямбде — синтаксический сахар.
-- полностью эквивалентно вложенным лямбдам выше.
#check fun (x : Nat) (y : Bool) =>
  if !y then x + 1 else x + 2

-- lean умеет вывести типы обоих аргументов из тела: `!y` требует Bool,
-- `x + 1` требует Nat. аннотации типов необязательны, если вывод однозначен.
#check λ x y =>
  if !y then x + 1 else x + 2


def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

-- `_` вместо имени аргумента означает "аргумент игнорируется".
-- это не переменная, а заглушка. тип всё равно проверяется.
#check fun x : Nat => x
#check λ _ : Nat => true

-- применение двух функций: g (f x) — сначала f преобразует Nat → String,
-- потом g преобразует String → Bool. lean выводит тип x как Nat из типа f.
#check fun x : Nat => g (f x)
#check fun x => g (f x)

-- функция compose в явном виде: принимает g : β → γ, f : α → β, x : α,
-- возвращает g (f x) : γ. это обобщённая композиция функций.
#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
-- полиморфная версия с произвольными типами α β γ : Type.
-- это лямбда-функция над типами — принимает типы как аргументы.
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)

-- три способа определить одну и ту же функцию.
-- `def double0 (x : Nat) : Nat := x + x` — стандартная запись с именованными аргументами.
-- `def double1 : Nat → Nat := λ x => x + x` — через присваивание лямбды переменной.
-- `def double2 := λ (x : Nat) => x + x` — lean выводит тип из лямбды.
-- все три эквивалентны; lean раскрывает `def f (x : A) := e` в `def f := fun x : A => e`.
def double0 (x : Nat) : Nat := x + x
def double1 : Nat → Nat := λ x => x + x
def double2 := λ (x : Nat) => x + x
#eval double0 3
#eval double1 3
#eval double2 3

def pi := 3.141592

-- два аргумента можно объединить в одной группе скобок, если они одного типа.
-- `(x y : Nat)` — сокращение для `(x : Nat) (y : Nat)`.
def add0 (x y : Nat) := x + y
def add1 (x : Nat) (y : Nat) := x + y
#eval add0 2 3
#eval add1 2 3

def max(x y : Nat) :=
  if x > y
  then x
  else y

-- `let y := expr; body` — локальное связывание в term-mode.
-- вводит y как синоним выражения `2 + 2`. подстановка происходит при вычислении.
-- точка с запятой отделяет определение от тела. в отличие от `def`, let — часть терма,
-- а не глобального окружения. тип let-переменной выводится автоматически.
#check let y := 2 + 2; y * y
#eval let y := 2 + 2; y * y

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2

-- цепочка let-связываний: каждое последующее может использовать предыдущее.
-- `let y := 2 + 2; let z := y + y; z * z` — y = 4, z = 8, результат = 64.
#check let y := 2 + 2; let z := y + y; z * z
#eval let y := 2 + 2; let z := y + y; z * z


-- многострочная запись let: точка с запятой заменяется переносом строки.
-- это синтаксически эквивалентно однострочной форме.
def t (x : Nat) : Nat :=
   let y := x + x
   y * y


-- явная полиморфная композиция: α β γ — типы, переданные как обычные аргументы.
-- при вызове `compose0 Nat String Bool g f x` нужно явно передавать типы.
def compose0 (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

-- `variable` объявляет переменные, которые автоматически добавляются в сигнатуры
-- функций, если они там используются. это сокращает повторение.
-- здесь α β γ : Type — глобальные переменные секции. lean добавит их как
-- неявные или явные аргументы в `compose1`, потому что g и f ссылаются на них.
variable (α β γ : Type)
-- благодаря `variable`, compose1 автоматически получает α β γ как аргументы.
-- `#check compose1` покажет `compose1 : (β → γ) → (α → β) → α → γ`.
def compose1 (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)


-- `section` ограничивает область видимости переменных. переменные, объявленные
-- через `variable` внутри section, не видны за её пределами.
-- после `end foo` переменные g, f, h, x исчезают из scope.
section foo
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  -- compose2 использует все переменные из section автоматически.
  -- lean выведет: `compose2 : (β → γ) → (α → β) → (α → α) → α → γ`
  -- (h добавляется, потому что объявлена в variable, даже если не используется — нет,
  -- lean добавляет только те переменные, которые реально нужны телу)
  def compose2 := g (f x)
end foo

-- `namespace` создаёт пространство имён. все определения внутри получают префикс.
-- `Foo.aa`, `Foo.ff` — полные имена. внутри namespace можно обращаться без префикса.
namespace Foo
  def aa : Nat := 5
  def ff (x : Nat) : Nat := x + 7

  -- внутри namespace `ff aa` — это `Foo.ff Foo.aa`.
  #check ff aa
  #eval ff aa
end Foo

-- за пределами namespace нужен полный квалификатор.
#check Foo.aa
#check Foo.ff

-- стандартная библиотека lean тоже использует namespace.
-- List.nil, List.cons, List.map — функции из namespace List.
#check List.nil
#check List.cons
#check List.map

-- namespace можно переоткрыть и дополнить новыми определениями.
-- это не переопределение, а расширение. Foo.aa и Foo.bb живут вместе.
namespace Foo
  def bb : Nat := 3
end Foo

-- namespace можно вкладывать друг в друга.
-- полное имя cc: `Bar.Baz.Qux.cc`.
namespace Bar
  namespace Baz
    namespace Qux
      def cc : Nat := 5
    end Qux
  end Baz
end Bar

#check Bar.Baz.Qux.cc

-- `@` делает все неявные аргументы явными.
-- `List.cons : {α : Type u_1} → α → List α → List α` — с @
-- все {} становятся (), нужно передавать тип явно: `@List.cons Nat 1 []`.
#check @List.cons

-- sigma types — обобщение декартова произведения для зависимых типов.
-- `(a : α) × β a` — это тип пар, где тип второго компонента зависит от первого.
-- в отличие от `α × β`, здесь β — функция `α → Type`, а не просто тип.
-- sigma type — это `Σ a : α, β a`. иногда называют "зависимой парой" (dependent pair).
-- в Prop-вселенной аналог — это ∃ x : α, P x (экзистенциальный квантор).
namespace SigmaTypes
  universe u0 u1

  -- `Sigma.mk a b` — конструктор sigma-типа. создаёт пару (a, b)
  -- где тип b — `β a` (зависит от конкретного значения a).
  -- результат имеет тип `(a : α) × β a`.
  def f (α : Type u0) (β : α → Type u1) (a : α) (b : β a) :
    (a : α) × β a := Sigma.mk a b

  -- анонимный конструктор `⟨a, b⟩` — сокращение для Sigma.mk a b.
  -- lean определяет нужный конструктор из ожидаемого типа.
  def g (α : Type u0) (β : α → Type u1) (a : α) (b : β a) :
    (a : α) × β a := ⟨a, b⟩

  -- пример использования: α = Type, β = fun t => t (тождественная функция на типах).
  -- тогда beta Nat = Nat. вызов f Type (fun α => α) Nat x создаёт пару (Nat, x).
  -- `.2` достаёт второй компонент. тип второго компонента: (fun α => α) Nat = Nat.
  def h1 (x : Nat) : Nat :=
    (f Type (fun α => α) Nat x).2

  -- (a : Type) × (Nat → Nat) Nat

  #eval h1 5
end SigmaTypes

-- пример использования namespace + universe для создания обёртки над List.
namespace Lst
  universe u

  -- T — просто псевдоним для List. тип уровня u → тип уровня u.
  def T (α : Type u) : Type u := List α

  -- `{α : Type u}` — неявный аргумент. lean выводит α из типа `a` и `as` автоматически.
  -- при вызове `cons 5 []` lean поймёт, что α = Nat, и не нужно передавать α явно.
  -- фигурные скобки {} означают: аргумент выводится унификацией, не передаётся вручную.
  def cons {α : Type u} (a : α) (as : T α) : T α :=
    List.cons a as

  -- неявный аргумент без явных аргументов. тип результата зависит от α,
  -- но α выводится из контекста использования (например, из аннотации переменной).
  def nil {α : Type u} : T α :=
    List.nil

  def append {α : Type u} (as bs : T α) :=
    List.append as bs
end Lst

-- `Lst.cons 0 Lst.nil` — lean выводит α = Nat из литерала 0.
-- нет необходимости писать `@Lst.cons Nat 0 Lst.nil`.
#check Lst.cons 0 Lst.nil

def as : Lst.T Nat := Lst.nil
def bs : Lst.T Nat := Lst.cons 5 as

#check Lst.append as bs

-- universe polymorphism: `{α : Type uuu}` — неявный аргумент-тип.
-- ident работает для Nat, Bool, String и любого другого типа любого уровня.
-- это параметрический полиморфизм — одна реализация для всех типов.
universe uuu
def ident {α : Type uuu} (x : α) := x

-- `#check ident` — покажет `ident : {α : Type uuu} → α → α`.
-- α в фигурных скобках — неявный, передаётся автоматически.
#check ident
-- `ident 1` — lean выводит α = Nat из литерала 1. вызов без явной передачи типа.
#check ident 1
#check ident true
#check ident "hooy"

-- анонимная секция (`section` без имени). переменные внутри видны в определениях,
-- но исчезают после `end`. это позволяет не повторять `{α : Type u}` в каждой функции.
section
  universe u
  variable {α : Type u}
  variable (x : α)
  -- `identity` получает α (неявно) и x (явно) из variable.
  -- lean сам добавит их в сигнатуру: `identity : {α : Type u} → α → α`.
  def identity := x
end

-- после end секции identity всё ещё доступна, но переменные α и x — нет.
#check identity
-- применение: lean выводит α = Bool из `true`.
#check identity true

-- `id` — встроенная функция идентичности в стандартной библиотеке lean.
-- определена как `id {α : Sort u} (a : α) := a`. работает для Prop тоже.
#check id
-- `(id : Nat -> Nat)` — явная аннотация типа для специализации полиморфного id.
-- lean подставит α = Nat в сигнатуру. :: аналог Haskell `id :: Nat -> Nat`.
#check (id : Nat -> Nat)
#check (id : Bool -> Bool)

-- числовые литералы полиморфны в lean. `2` по умолчанию имеет тип Nat,
-- но можно явно аннотировать как Int, Float и т.д.
#check 2
-- `(2 : Int)` — то же значение, но явно указан тип Int. lean вставит coercion.
#check (2 : Int)

-- `@id Nat` — явная передача неявного аргумента с помощью @.
-- результат: `id : Nat → Nat`, то есть id специализированная для Nat.
#check @id Nat
