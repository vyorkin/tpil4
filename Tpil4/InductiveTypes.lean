-- 7. Inductive Types

-- В lean 4 любой конкретный тип (кроме вселенных - универсумов типов) и
-- любой конструктор типа (кроме зависимых стрелочных типов) является
-- индуктивным типом.

-- Угарно, что можно построить довольно большой фундамент математики,
-- опираясь только на универсумы типов, зависимые стрелочные типы и
-- индуктивные типы; всё остальное выводится из них.
--
-- Напомним что это за три вещи:
--   - универсумы типов: Sort 0 = Prop, Sort 1 = Type, Sort 2 = Type 1, ...
--     каждый тип сам является значением некоторого "типа типов"
--   - зависимые стрелки: (x : α) → β x — тип результата может зависеть от аргумента
--   - индуктивные типы: всё, что ниже

-- Типичный индуктивный тип выглядит так:

-- inductive Foo where
--   | constructor₁ : ... → Foo
--   | constructor₂ : ... → Foo
--   ...
--   | constructorₙ : ... → Foo

namespace My1

-- Weekday — простейший пример: перечислимый тип (enumerated type).
-- У конструкторов нет аргументов — они просто метки, аналог enum в других языках.
-- Типы вроде Bool, Unit и им подобные тоже устроены именно так.
inductive Weekday where
  | sunday : Weekday
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday

end My1

namespace My2
--  Можно не писать тип после каждого конструктора.
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday

-- Вместе с индуктивным типом автоматически определяется
-- принцип элиминации rec. Эту функцию также называют рекурсором,
-- и именно она делает тип индуктивным: онa позволяет определить функцию на MyType,
-- присваивая значения, соответствующие каждому конструктору.
-- Интуитивно, индуктивный тип исчерпывающе порождается своими конструкторами и
-- не имеет элементов, кроме тех, которые они создают.
--
-- Другими словами: если ты можешь сказать что делать с каждым конструктором —
-- ты полностью описал функцию. Это и есть принцип рекурсии / элиминации.

open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

#eval numberOfDay Weekday.sunday
#eval numberOfDay Weekday.monday
#eval numberOfDay Weekday.tuesday

-- Когда мы работаем с логикой, lean 4 компилирует match во что-то, что
-- использует rec. Это позволяет убедиться, что терм правильно определён с
-- точки зрения теории типов. При компиляции match превращается примерно в то же,
-- что в других ЯП.
--
-- match — синтаксический сахар поверх rec/casesOn. Lean проверяет:
--   (1) паттерны покрывают все конструкторы (exhaustiveness)
--   (2) ни один паттерн недостижим (no redundancy, если включено)
-- Всё это гарантирует что функция тотальна — определена для каждого входа.

set_option pp.all true
#print numberOfDay
#print numberOfDay.match_1
#print Weekday.casesOn -- << Вызов Weekday.rec вот тут

#check @Weekday.rec

-- Weekday.rec.{u} :
--   {motive : (t : Weekday) → Sort u} →
--
--   (sunday    : motive Weekday.sunday)    →
--   (monday    : motive Weekday.monday)    →
--   (tuesday   : motive Weekday.tuesday)   →
--   (wednesday : motive Weekday.wednesday) →
--   (thursday  : motive Weekday.thursday)  →
--   (friday    : motive Weekday.friday)    →
--   (saturday  : motive Weekday.saturday)  →
--
--   (t : Weekday) → motive t

-- .rec — это принцип элиминации (elimination principle) индуктивного типа.
-- Он автоматически генерируется Lean для каждого inductive.
-- match — лишь синтаксический сахар, который Lean сразу компилирует в вызов .rec.
--
-- Чтобы что-то сделать с любым значением индуктивного типа T,
-- достаточно объяснить, что делать с каждым конструктором T отдельно.
-- .rec получает по одному аргументу-ответу на каждый конструктор,
-- и для конкретного значения выбирает нужный.
--
-- Что такое motive?
--
-- motive : T → Sort u
--
-- Это функция из самого типа T во вселенную типов.
-- Она отвечает на вопрос: "что именно мы хотим получить для каждого значения T?"
--
-- Два типичных случая:
--
-- 1. Независимый / вычисление (computation): motive = fun _ => R
--    Тип результата один и тот же для всех конструкторов — просто R.
--    Пример: numberOfDay — всегда Nat, motive = fun _ => Nat.
--    Здесь .rec — просто switch-case по конструктору.
--
-- 2. Зависимый (proof / dependent): motive = fun x => P x
--    Тип возвращаемого значения зависит от конкретного значения x : T.
--
--    Пример: доказываем ∀ d : Weekday, next (previous d) = d.
--    motive = fun d => next (previous d) = d   -- это Prop, зависящий от d
--
--    Раскрываем motive на каждом конкретном конструкторе — получаем разные Prop-типы:
--      motive sunday    = (next (previous sunday) = sunday)    -- тип того, что надо вернуть для ветки sunday
--      motive monday    = (next (previous monday) = monday)    -- другой Prop — для ветки monday
--      ...
--    Именно это и называется "разные типы результата" — для каждого конструктора
--    rec ожидает аргумент разного типа (разное доказательство). Само d : Weekday
--    всегда одного типа, меняется только тип доказательства, которое нужно предъявить.
--
-- Почему не просто тип, а функция?
--
-- Если бы motive было просто типом R (не функцией), то .rec мог бы возвращать
-- только одно и то же R для всех значений. Это не позволяет выражать
-- зависимые типы — ситуацию, когда ответ для monday и для sunday имеют
-- разные типы. Поэтому motive обязан быть функцией Weekday → Sort u.
--
-- Конкретная раскрутка numberOfDay через .rec:
--
-- def numberOfDay (d : Weekday) : Nat := match d with | sunday => 1 | ...
--
-- Это компилируется примерно в:
--
--   Weekday.rec
--     (motive := fun _ => Nat)  -- тип результата — всегда Nat
--     1   -- для sunday
--     2   -- для monday
--     3   -- для tuesday
--     4   -- для wednesday
--     5   -- для thursday
--     6   -- для friday
--     7   -- для saturday
--     d   -- конкретное значение
--
-- Lean смотрит на конструктор d, берёт соответствующий аргумент и возвращает его.
--
-- rec vs casesOn vs recOn:
--
-- Все три — одна и та же операция, только аргументы идут в разном порядке:
--
--   Weekday.rec     motive sun mon ... sat d -- конкретное значение d в конце
--   Weekday.casesOn motive d sun mon ... sat -- d после motive (удобнее читать)
--   Weekday.recOn   motive d sun mon ... sat -- то же что casesOn (для Nat добавляет ih)
--
-- casesOn — стандартное имя для неиндуктивных типов (без рекурсивных конструкторов).
-- recOn   — для рекурсивных типов (Nat, List), где появляется индукционная гипотеза.
--
-- Prop и ограничения элиминации:
--
-- Если T живёт в Prop, то motive тоже обязан быть в Prop.
-- Нельзя элиминировать доказательство в вычислимые данные (Type).
-- Причина: proof irrelevance — все доказательства одного утверждения считаются равными,
-- поэтому "извлекать данные" из них бессмысленно и запрещено системой.
-- Исключение: singleton elimination (подробнее в My10 и разделе 7.8).

end My2

namespace My3
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
deriving Repr

-- Если не задерайвить Repr, то он всё равно задерайвится в
-- момент использования, например, #eval.
--
-- deriving Repr — команда кодогенерации: Lean автоматически выводит экземпляр
-- класса типов Repr для Weekday. Repr это интерфейс с одним методом:
--   reprPrec : α → Nat → Std.Format
-- который форматирует значение для вывода. #eval вызывает его под капотом.
-- Без deriving Repr #eval не знает как отобразить значение типа Weekday —
-- нужно либо задерайвить, либо написать instance вручную.

open Weekday

#eval tuesday

end My3

namespace My4

inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
deriving Repr

-- Ты можешь присобачивать функции/определения и теоремы к
-- своему индуктивному типу, определяя их в неймспейсе с таким же названием.
--
-- Это важный паттерн: если у тебя есть `inductive Foo`, а потом `namespace Foo`,
-- то всё внутри этого namespace будет доступно как Foo.имя (методы типа).
-- open Foo убирает необходимость писать префикс Foo. внутри блока.

namespace Weekday

def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (next tuesday)
#eval next (previous tuesday)

example : next (previous tuesday) = tuesday :=
  rfl

-- А вот как можно доказывать всякие утверждения об идуктивных типах.
-- Ниже вариант в тактик-мод.

-- В term-mode: семь веток match, каждая доказывается rfl (по вычислению).
-- Да, rfl делает редукции.
-- Lean разворачивает это равнество следующей цепочкой редукций:
-- next (previous sunday) → next saturday → sunday = sunday.
theorem next_previous₀ (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl

-- В tactic-mode: cases d порождает 7 подцелей (по одной на каждый конструктор),
-- а <;> применяет следующую тактику (rfl) ко всем подцелям одновременно.
-- Итого: вместо семи rfl — одна строка.
theorem next_previous₁ (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl

end Weekday

end My4

namespace My5

inductive Bool where
  | false : Bool
  | true  : Bool

-- Introduction и elimination rules для такого типа это просто его конструкторы.
--
-- Точнее: introduction rules — это конструкторы Bool.false и Bool.true.
-- Они вводят (создают) значения типа Bool.
--
-- Elimination rule — это Bool.rec (он же match):
--   Bool.rec : {motive : Bool → Sort u} → motive false → motive true → (b : Bool) → motive b
-- Он позволяет "использовать" значение типа Bool — определить что делать в
-- каждом из двух случаев.

end My5

namespace My5_BoolOps

-- Книга предлагает реализовать булевы операции как упражнение.
-- Ключевой паттерн: match по первому аргументу, тождества — cases <;> rfl.

def myAnd (a b : Bool) : Bool :=
  match a with
  | true  => b
  | false => false

def myOr (a b : Bool) : Bool :=
  match a with
  | true  => true
  | false => b

def myNot (a : Bool) : Bool :=
  match a with
  | true  => false
  | false => true

-- Перебор всех 2×2 или 2 случаев — cases <;> rfl
theorem myAnd_comm (a b : Bool) : myAnd a b = myAnd b a := by cases a <;> cases b <;> rfl
theorem myOr_comm  (a b : Bool) : myOr  a b = myOr  b a := by cases a <;> cases b <;> rfl

theorem myNot_myNot (a : Bool) : myNot (myNot a) = a := by cases a <;> rfl

end My5_BoolOps

namespace My6

-- Обычно конструкторы индуктивных типов всё таки принимают
-- какие-то аргументы, ну вот как в типе-сумме или типе-произведении.
--
-- Prod α β — тип-произведение (декартово произведение): пара из α и β.
-- Единственный конструктор mk принимает оба компонента.
-- Аналог кортежа (tuple) или struct с двумя полями.
inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β
-- ^ Ниже будет показано как определить тип-произведение более идиоматично,
--   используя keyword "structure"

-- Sum α β — тип-сумма (дизъюнктное объединение): либо α, либо β.
-- Два конструктора: inl вводит левую ветку, inr — правую.
-- Аналог tagged union или Result/Either.
inductive Sum (α : Type u) (β : Type v) where
--                                        ^ where писать не обязательно
  | inl : α → Sum α β
  | inr : α → Sum α β

def fst {α : Type u} {β : Type v} {p : Prod α β} : α :=
  match p with
  | Prod.mk a _ => a

def snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
  match p with
  | Prod.mk _ b => b

#check Prod.casesOn

-- Prod.casesOn.{w, u, v}
--   {α : Type u}
--   {β : Type v}
--
--   {motive : Prod α β → Sort w}
--
--   (p : Prod α β)
--   (mk : (a : α) → (b : β) → motive (Prod.mk a b))
--
--   : motive p

-- Думай об этой функции, как об elimination rule.
--
-- Ф-ция mk берёт оба параметра единственного конструктора,
-- создаёт тип-произведение и возвращает `motive p`.
--
-- `motive p` это то, что надо вернуть и это зависимая функция,
-- которая принимает некоторое значение типa-произведения (p : Prod α β) и
-- возвращает некоторый тип.
--
-- Она вполне может выглядеть так, как в примере ниже,
-- т.е. как const может игнорировать свой аргумент.

-- Конструирует тебе чётное или нечётное число, в зависимости от
-- того что слева у этой пары:
def prod_example (p : Prod Bool Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p
    (fun b n => cond b (2 * n) (2 * n + 1))

-- Тут зависимая функция (motive := fun _ => Nat) используется,
-- чтобы сообщить тип конструируемого объекта.
-- Да, это функция, потому что тип может зависить от значения Prod Bool Nat.
--
-- А cond это типа: if b the (2 * n) else (2 * n + 1)
-- Это обычный "ternary operator", только для Bool из стандартной библиотеки:
-- cond : Bool → α → α → α
-- cond true  x y = x
-- cond false x y = y

#eval prod_example (Prod.mk true 3)
#eval prod_example (Prod.mk false 3)

-- Sum.casesOn.{w, u, v}
--   {α : Type u}
--   {β : Type v}
--
--   {motive : Sum α β → Sort w}
--
--   (t : Sum α β)
--
--   (inl : (a : α) → motive (Sum.inl a))
--   (inr : (a : α) → motive (Sum.inr a))
--
--   : motive t

-- Для каждого конструктора исходного типа будет своя introduction-функция.
--
-- Обрати внимание: Sum.casesOn принимает два разных обработчика — по одному на
-- каждый конструктор. Это и есть принцип элиминации для типа-суммы: чтобы
-- что-то сделать со значением Sum α β, нужно объяснить оба случая.

def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := fun _ => Nat) s
    (fun n => 2 * n)
    (fun n => 2 * n + 1)

#eval sum_example (Sum.inl 3) -- 6
#eval sum_example (Sum.inr 3) -- 7

end My6

namespace My7

-- Вот так ещё можно определить тип-произведение сразу вместе с проекциями.
--
-- structure — синтаксический сахар для inductive с ровно одним конструктором.
-- Lean автоматически генерирует:
--   - конструктор (здесь Prod.mk)
--   - проекции Prod.fst и Prod.snd (по одной на каждое поле)
--   - лемму eta: ∀ p : Prod α β, Prod.mk p.fst p.snd = p
--     eta говорит: если взять любую пару p, извлечь её компоненты и собрать обратно —
--     получится ровно то же самое p. другими словами, "разобрать и собрать = ничего не делать".
--     это структурный закон тождества для произведения.
--
--     есть две стороны одной медали:
--       - бета-правила (генерируются автоматически):
--           Prod.fst (Prod.mk a b) = a   -- взяли первый — получили первый
--           Prod.snd (Prod.mk a b) = b   -- взяли второй — получили второй
--       - eta-правило (именно эта лемма):
--           Prod.mk p.fst p.snd = p      -- собрали из частей — получили исходное
--
--     вместе бета + eta означают, что конструктор и проекции взаимно обратны:
--     никакой информации не теряется при разборке и сборке.
--
--     практически нужна в доказательствах, когда надо показать равенство двух пар:
--     достаточно доказать, что их fst равны и snd равны (через ext или rcases).
--     без eta Lean не знал бы, что пара определяется только своими компонентами.
--
-- Проекции — это просто функции, Lean разворачивает Prod.fst ⟨a, b⟩ → a по rfl.

structure Prod (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β

-- Если не задать имя конструктора, то линь назовёт его mk.
-- Вот как в примере ниже:

structure Color where
  red : Nat
  green : Nat
  blue : Nat
deriving Repr

def yellow := Color.mk 255 255 0

#eval Color.red yellow -- 255

end My7

namespace My8

-- Semigroup — пример структуры с доказательством внутри.
-- carrier это носитель (underlying set), mul — бинарная операция, mul_assoc — аксиома ассоциативности.
-- structure позволяет хранить данные вместе с их свойствами в одном типе.
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α

-- Inhabited α означает "тип α населён" — то есть существует хотя бы один элемент.
-- Конструктор mk принимает этот элемент как свидетель.
-- Это способ выразить "непустоту" типа: если у тебя есть Inhabited α, у тебя есть α.
inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α

-- product of two inhabited types is inhabited

-- Не уверен, что это то, что просил показать автор.
-- Возможно он хотел, чтобы я использовал утверждения и
-- представил это как theorem prod_inh.

-- Если у нас есть свидетель a : α и свидетель b : β,
-- мы можем собрать пару (a, b) — свидетель населённости α × β.
def prod_inh (α : Type u) (β : Type v)
  : (a : Inhabited α) → (b : Inhabited β) → (Inhabited (α × β)) :=
  λ (Inhabited.mk a) (Inhabited.mk b) => Inhabited.mk (a, b)

-- type of functions to an inhabited type is inhabited

-- Если для каждого a : α мы можем получить Inhabited β (т.е. f a даёт b : β),
-- то мы можем построить функцию α → β — это свидетель населённости α → β.
-- Мы "извлекаем" b из Inhabited.mk b через match.
def funs_inh (α : Type u) (β : Type v)
  : (α → Inhabited β) → Inhabited (α → β) :=
  λ f => Inhabited.mk (λ a => match f a with | Inhabited.mk b => b)

end My8

namespace My9

-- compose — это монадический bind (>>=) для Option, написанный явно.
-- Читается так: применяем f к a, если получили none — возвращаем none,
-- если получили some b — применяем g к b.
-- В Haskell/Lean с do-нотацией это выглядело бы:
--   do b ← f a; g b
-- Но здесь мы видим как это устроено под капотом.
def compose (f : α → Option β) (g : β → Option γ) : α → Option γ :=
  fun a =>
    match f a with
    | none => none
    | some b => g b

-- example₀ x = compose (x ↦ some (x*2))      (y ↦ if y > 3 then none else some (y+2))
-- example₀ 1: f(1) = some 2, g(2) = some 4   (2 ≤ 3, значит some (2+2) = some 4)
-- example₀ 3: f(3) = some 6, g(6) = none     (6 > 3, значит none)
def example₀ :=
  compose
    (λ (x : Nat) => Option.some (x * 2))
    (λ (y : Nat) => cond (y > 3) none (some (y + 2)))

#eval example₀ 1 -- some 4
#eval example₀ 3 -- none

end My9

namespace My10

-- Индуктивные типы могут жить в любой
-- вселенной, даже в самой нижней – Prop.
-- Кстати, именно так определены логические коннекторы.

inductive False : Prop

inductive True : Prop where
  | intro : True

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b

-- Сравни с:
-- inductive Option (α : Type u) where ...
--                       ^^ раньше ты указывал тут вселенную типов
--                          какого-то индекса
-- Теперь ты пишешь вот как выше:
-- Inductive And (a b : Prop)
--                       ^^ вселенная Prop

-- Так вот, типы в Prop можно элиминировать только в другие типы из Prop.
-- Это определяет какие типы вообще возможно получить при
-- использовании рекурсора. В какую-то другую произвольную вселенную
-- с индексом u (Type u) ты перейти элиминицией не сможешь.
--
-- Это ограничение называется proof irrelevance: все доказательства одного
-- утверждения считаются равными (неразличимыми). Если бы ты мог извлечь
-- из доказательства вычислимые данные, это нарушило бы proof irrelevance —
-- два доказательства могли бы отличаться "содержимым" и давать разные результаты.
-- Поэтому Lean просто не даёт использовать Prop-значения в вычислениях.

-- Даже квантор существования это тип, который определяется индуктивно.
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p

-- Следующие типы изоморфны, разница только во вселенных:
--
--   Prop         Type u
-- ------------------------
--  False     ≅   Empty
--   True     ≅   Unit
--   And      ≅   Prod
--    Or      ≅   Sum
-- ∃ x : α p  ≅   Σ x, α, β

-- Да exists x, P x изоморфен зависимой функции:
-- λ (x : Nat) => (x + 0 = x : P)
-- "Дай мне х и я верну для тебя утверждение о нём".

-- Есть ещё одна забавная штука -- "подтип".
-- По сути это все такие элементы x : α из Type u, для
-- которых выполняется p x. Ни один элемент такого "подтипа" не может
-- быть сконструирован без того, чтобы предъявить "доказательство" того,
-- что он обладает указанным свойством (p x).
inductive Subtype₀ {α : Type u} (p : α → Prop) where
  | mk : (x : α) → p x → Subtype₀ p

-- В лине этот тип определён с помощью structure keyword:

structure Subtype₁ {α : Type u} (p : α → Prop) where
  val : α
  property : p val

-- Существует такая нотация для простоты:
-- {x : α // p x}
--
-- Она эквивалентна:
-- Subtype (λ x : α ↦ p x)
--
-- Пример: {n : Nat // n > 0} — тип натуральных чисел, строго больших нуля.
-- Создать элемент такого типа можно только предъявив n и доказательство n > 0.
-- Проекции: .val достаёт сам элемент, .property — доказательство о нём.

-- С этого момента мы больше не будем явно писать mk при
-- определении индуктивных типов-произведений.

end My10

namespace My11

-- Наименьший рекурсивный тип из возможных.
-- zero — базовый случай, succ — рекурсивный конструктор.
-- succ : Nat → Nat  означает: дай мне уже существующее натуральное число,
-- и я построю следующее. Так 3 = succ (succ (succ zero)).
-- Натуральные числа — это в точности унарная запись (палочки).
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
  deriving Repr

#check Nat.rec

-- Я заменю motive на f.

-- Nat.rec :
--   {f : Nat → Sort u} →
--
--   /- case-1 -/  f zero                       →
--   /- case-2 -/  ((n : Nat) → f n → f n.succ) →
--
--   (n : Nat) →
--   f n

-- Подробно про Nat.rec:
--
-- Nat — первый рекурсивный тип, поэтому его .rec существенно сложнее Weekday.rec.
-- Разница в том, что конструктор succ принимает уже существующий Nat — рекурсивно.
-- Поэтому в шаге rec появляется дополнительный аргумент: уже вычисленное значение
-- для предыдущего числа. Это и есть индукционная гипотеза.
--
-- Nat.rec :
--   {f : Nat → Sort u} →           -- f: тип результата зависит от числа
--   f zero →                       -- (1) что делать с нулём (в какой тип его отображать)
--   ((n : Nat) → f n → f n.succ) → -- (2) что делать с n+1, зная f n (тип предыдущего числа)
--   (n : Nat) → f n                -- для любого n возвращает f n
--
-- Почему в case-2 три аргумента, а не один?
--
-- (n : Nat) → f n → f n.succ
--  ^^^^^^^^   ^^^   ^^^^^^^^^
--    (а)       (б)     (в)
--
-- (а) n — само предыдущее число (позволяет упомянуть его в выражении)
-- (б) f n — уже готовый результат для n (это и есть "индукционная гипотеза")
--     при доказательстве это "мы уже знаем P(n)"
--     при вычислении это "мы уже посчитали результат для n"
-- (в) f n.succ — что нужно вернуть для n+1
--
-- Пример (add через Nat.rec):
--
-- def add (m n : Nat) : Nat := match n with
--   | zero   => m
--   | succ n' => succ (add m n')
--
-- Через Nat.rec это выглядит так:
--
--   Nat.rec
--     (motive := fun _ => Nat)      -- результат всегда Nat (недепедентный)
--     m                             -- (1) add m 0 = m
--     (fun n' ih => succ ih)        -- (2) add m (n'+1) = succ (add m n')
--                                   --     где ih = add m n' (уже вычислено)
--     n                             -- конкретное n
--
-- Раскрутка add 2 1 шаг за шагом:
--   add 2 1
--   = add 2 (succ zero)
--   = succ (add 2 zero)    -- шаг rec: n'=zero, ih=add 2 zero
--   = succ 2               -- base: add 2 zero = 2
--   = 3
--
-- ── Пример: доказательство через Nat.rec (зависимый случай) ────────────
--
-- theorem zero_add (n : Nat) : 0 + n = n :=
--   Nat.rec
--     (motive := fun n => 0 + n = n)     -- для каждого n свой тип
--     (rfl : 0 + 0 = 0)                  -- (1) base case
--     (fun n ih =>                       -- (2) шаг:
--       -- ih : 0 + n = n                --   уже знаем для n
--       -- цель: 0 + (n+1) = n+1
--       calc 0 + (n + 1) = (0 + n) + 1 := rfl
--                        _ = n + 1      := by rw [ih])
--     n
--
-- Здесь motive = fun n => 0 + n = n, поэтому:
--   motive 0 = (0 + 0 = 0)     — тип base case
--   motive n.succ = (0 + n.succ = n.succ) — тип шага
-- Типы разные для разных n — это зависимая элиминация в действии.
--
-- ── Итоговое резюме ────────────────────────────────────────────────────
--
-- .rec (и match) — единственный способ "заглянуть внутрь" значения инд. типа.
-- Lean строго контролирует что для всех конструкторов есть ответ (тотальность).
-- В рекурсивных конструкторах появляется ih — готовый ответ для "меньшего" значения.
-- Это делает рекурсию хорошо основанной: не нужна аксиома, всё выводится из .rec.
--
-- Все тактики induction, cases, match — это лишь удобный синтаксис
-- для построения терма через .rec / .casesOn.

#check Nat.recOn

-- recOn это та же rec с переставленным порядком аргументов:
-- конкретное число n идёт раньше case-аргументов.
-- Это удобнее читать как "recOn n base step" — сначала объект, потом обработчики.
--
-- Nat.recOn.{u} :
--   {f : Nat → Sort u} →
--
--   (n : Nat) →          -- <-- n теперь здесь, а не в конце
--
--   (zero : f zero) →
--   (succ : ((n : Nat) → f n → f n.succ)) →
--
--   f n

-- Если зафиксируем m, то можно определить сложение рекурсивно по n.
-- Рекурсия идёт по второму аргументу: m + 0 = m, m + (n+1) = (m+n)+1.
def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero => m
  | Nat.succ n' => Nat.succ (add m n')

open Nat

#eval add (succ (succ zero)) (succ zero)
--         succ (succ (succ (zero)))

-- Чтобы эти 2 теоремки ниже доказывались по определению,
-- мы должны сделать Nat инстансом Add. Про классы типов будет чуть позже.
--
-- instance : Add Nat — объявляет экземпляр класса типов Add для нашего Nat.
-- После этого Lean знает как интерпретировать a + b для a b : Nat.
-- Это позволяет использовать + вместо add и писать m + zero вместо add m zero.
instance : Add Nat where
  add := add

-- add_zero: m + 0 = m — разворачивается по первому случаю match, rfl.
-- add_succ: m + (n+1) = (m+n)+1 — разворачивается по второму случаю match, rfl.
-- Они доказываются rfl, потому что обе стороны вычисляются в одно и то же.
theorem add_zero (m : Nat) : m + zero = m := rfl
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

end My11

namespace My12

open Nat

-- Но 0 + n = n нужно доказывать по индукции.
-- Почему? Потому что add определяется рекурсией по второму аргументу (n).
-- 0 + n: здесь 0 слева (первый аргумент), рекурсия идёт по n.
-- Lean не может просто "раскрыть" 0 + n по определению при произвольном n —
-- он не знает, чему равно n. Нужно рассмотреть n = 0 и n = succ n' отдельно.

-- Nat.recOn.{u} :
--   {motive : Nat → Sort u} →
--
--   (n : Nat) →
--
--   (zero : motive zero) →
--   (succ : ((n : Nat) → motive n → motive n.succ)) →
--
--   motive n

theorem zero_add₀ (n : Nat) : 0 + n = n :=
  Nat.recOn
    (motive := fun n => 0 + n = n) -- {motive : Nat → Prop}
    n -- (n : Nat)
    (show 0 + 0 = 0 from rfl) -- (zero : motive 0)
    (fun (n : Nat) (ih : 0 + n = n) =>
      show 0 + (n + 1) = n + 1 from
      calc 0 + (n + 1)
        _ = (0 + n) + 1 := rfl
        _ =      n  + 1 := by rw [ih]
    ) -- (succ : ((n : Nat) → motive n → motive (n + 1)))

theorem zero_add₁ (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := λ n => 0 + n = n)
  n
  rfl -- (motive 0)
  (λ (n : Nat) (ih : 0 + n = n) => by simp [ih]) -- n ih → motive (n + 1)

-- Рекурсия работает по второму аргументу, делаем индукцию по k.
theorem add_assoc₀ (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := λ k => m + n + k = m + (n + k)) k
    (show m + n + 0 = m + (n + 0) from rfl)
    (λ k (ih : m + n + k = m + (n + k)) =>
      show m + n + (k + 1) = m + (n + (k + 1)) from
      calc m + n + (k + 1)
        _ = (m + n + k) + 1 := rfl
        _ = (m + (n + k) + 1) := by rw [ih]
        _ = m + (n + (k + 1)) := rfl)

-- Можно и проще.
theorem add_assoc₁ (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := λ k => m + n + k = m + (n + k)) k
    rfl
    (λ k ih => by simp [add_succ (m + n) k, ih]; rfl)

-- add_comm₀ — незаконченная версия: в шаге индукции нужна лемма
-- succ n + m = succ (n + m), которую мы ещё не доказали. Оставлена как sorry.
-- Правильная стратегия: сначала доказать succ_add, затем использовать его.
-- Смотри add_comm₁ ниже — там это исправлено.
theorem add_comm₀ (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := λ x ↦ m + x = x + m) n
    (show m + 0 = 0 + m by rw [Nat.add_zero, Nat.zero_add])
    (λ (n : Nat) (ih : m + n = n + m) ↦
      show m + (succ n) = (succ n) + m from
      calc
        m + (succ n) = succ (m + n) := rfl
        _ = succ (n + m) := by rw [ih]
        _ = (succ n) + m := sorry) -- Need: succ (n + m) = (succ n) + m

-- succ_add₀ — вспомогательная лемма: (n+1) + m = (n + m) + 1.
-- Рекурсия по m. Это симметричный аналог add_succ, только слева.
-- Нужна для шага в add_comm: последний шаг calc требует именно её.
theorem succ_add₀ (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := λ x => succ n + x = succ (n + x)) m
    (show (succ n) + 0 = succ (n + 0) from rfl) -- motive 0
    (λ (m : Nat) (ih : succ n + m = succ (n + m)) =>
      show succ n + succ m = succ (n + succ m) from
      calc
        (succ n) + (succ m) = succ (succ n + m) := rfl
        _ = succ (succ (n + m)) := by rw [ih]
        _ = succ (n + (succ m)) := rfl) -- motive (n + 1)

theorem add_comm₁ (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := λ x ↦ m + x = x + m) n
    (show m + 0 = 0 + m by rw [Nat.add_zero, Nat.zero_add])
    (λ (n : Nat) (ih : m + n = n + m) ↦
      show m + (succ n) = (succ n) + m from
      calc
        m + (succ n) = succ (m + n) := rfl
        _ = succ (n + m) := by rw [ih]
        _ = (succ n) + m := by rw [succ_add₀]) -- Теперь мы можем.

-- Ну и упрощённый вариант конструирования
-- `motive 0` и `motive (n + 1)` с помощью тактик.

-- theorem succ_add₁ (n m : Nat) : succ n + m = succ (n + m) :=
--   Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
--     rfl
--     (fun m ih => by simpa [add_succ (succ n)])

-- theorem add_comm₂ (m n : Nat) : m + n = n + m :=
--   Nat.recOn (motive := fun x => m + x = x + m) n
--     (by simp [Nat.add_zero, Nat.zero_add])
--     (fun m ih => by simp_all [Nat.succ_add, Nat.add_succ])

end My12

namespace My13

-- 7.5. Other Recursive Data Types
--
-- Список — классический пример рекурсивного типа с двумя конструкторами:
--   nil  — пустой список (база)
--   cons — непустой список: голова (h : α) и хвост (t : List α)
-- cons рекурсивен: принимает уже существующий список в качестве аргумента.
-- Список [1, 2, 3] = cons 1 (cons 2 (cons 3 nil)).
inductive List (α : Type u) where
  | nil : List α
  | cons (h : α) (t : List α) : List α
  deriving Repr

namespace List
def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) :
  append nil as = as := rfl

-- 1-st reducton: as = as := rfl

theorem cons_append (a : α) (as bs : List α) :
  append (cons a as) bs = cons a (append as bs) := rfl

-- 1-st reduction:
-- cons a (append as bs) = cons a (append as bs) := rfl

-- Нас просят доказать не в тактик-мод (apply induction etc),
-- а именно так, как мазохист бы сделал -- с помощью List.recOn.
--
-- List.recOn структура:
--   (motive := λ l => <что доказываем о l>)
--   as                 — список, по которому индукция
--   <base case>        — motive nil
--   <λ a as ih => ...> — шаг: голова a, хвост as, гипотеза ih : motive as

#check List.recOn

theorem append_nil₀ (as : List α) : append as nil = as :=
  List.recOn (motive := λ l => append l nil = l) as
    (show append nil nil = nil from rfl) -- motive nil
    (fun (a : α) (as : List α) (ih : append as nil = as) =>
      show append (cons a as) nil = cons a as from
      calc
        append (cons a as) nil = cons a (append as nil) := by rw [cons_append]
        _ = cons a as := by rw [ih]) -- motive (cons a as)

theorem append_nil₁ (as : List α) : append as nil = as :=
  List.recOn (motive := λ l => append l nil = l) as
    rfl -- motive nil
    (λ (a : α) (as : List α) (ih : append as nil = as) =>
      by simp only [cons_append, ih]) -- motive (cons a as)

theorem append_assoc₁ (as bs cs : List α) :
  append (append as bs) cs = append as (append bs cs) :=
  List.recOn
    (motive := λ l => append (append l bs) cs = append l (append bs cs)) as
    rfl -- motive nil
    (λ (a : α) -- motive cons ...
       (as : List α)
       (ih : append (append as bs) cs = append as (append bs cs)) =>
        -- append (append l bs) cs = append l (append bs cs)) (cons a as)
        by simp [cons_append, ih])

--

def length {α : Type u} (as : List α) : Nat :=
  match as with
  | nil => 0
  | cons _ as => 1 + length as

theorem length_nil {α : Type u} : @length α nil = 0 := rfl

theorem length_cons {α : Type u} (a : α) (as : List α) :
  length (cons a as) = 1 + length as := rfl

theorem length_correct (as bs : List α) :
  length (append as bs) = length as + length bs :=
    List.recOn
      (motive := fun l => length (append l bs) = length l + length bs) as
      (show length (append nil bs) = length nil + length bs by
        rw [nil_append, length_nil, Nat.zero_add])
      (fun
        (a : α)
        (as : List α)
        (ih : length (append as bs) = length as + length bs) =>
          show length (append (cons a as) bs) = length (cons a as) + length bs by
            rw [cons_append]
            rw [length_cons, length_cons]
            rw [ih]
            rw [Nat.add_assoc])

end List

end My13

namespace My14

-- BinaryTree — бинарное дерево: либо лист (пустой), либо узел с двумя поддеревьями.
-- node принимает ровно два поддерева (левое и правое).
inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree

-- Countably branching tree — счётно ветвящееся дерево.
-- Каждый узел может иметь сколько угодно (счётно много) поддеревьев.
-- sup принимает функцию Nat → CBTree — это бесконечная последовательность поддеревьев,
-- пронумерованная натуральными числами. Это не список — это настоящая бесконечность.
inductive CBTree where
  | leaf : CBTree
  | sup : (Nat → CBTree) → CBTree

namespace CBTree

-- succ t — узел, у которого все бесконечно много ветвей ведут в одно и то же t.
-- По сути это "повторить t счётно много раз".
def succ (t : CBTree) : CBTree :=
  sup (fun _ => t)

-- toCBTree n — цепочка длины n: leaf, succ leaf, succ (succ leaf), ...
-- Это вложение Nat в CBTree: каждому натуральному числу соответствует своё дерево.
def toCBTree : Nat → CBTree
  | 0 => leaf
  | n + 1 => succ (toCBTree n)

-- omega — предел последовательности toCBTree 0, toCBTree 1, toCBTree 2, ...
-- Это бесконечно ветвящееся дерево, чьи ветви исчерпывают все конечные глубины.
-- Аналог предельного ординала ω в теории ординалов.
def omega : CBTree :=
  sup toCBTree

end CBTree

end My14

namespace My15

-- Тактика cases в tactic-mode — аналог match в term-mode.
-- cases n создаёт по одной подцели на каждый конструктор Nat (zero и succ n).
-- Используй с with, когда хочешь именовать аргументы конструктора.
example (p : Nat → Prop)
        (hz : p 0)
        (hs : ∀ n, p (Nat.succ n)) :
        ∀ n, p n := by
  intro n
  cases n
  · exact hz
  · apply hs

open Nat

-- absurd : α → ¬α → β
-- absurd rfl h: rfl : n = n, но h : n ≠ 0. В случае n = zero:
--   rfl : 0 = 0, h : 0 ≠ 0. absurd rfl h закрывает цель (contradiction).
-- В случае n = succ m: succ (pred (succ m)) = succ m → rfl по вычислению.
example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero =>
    apply absurd rfl h
  | succ m =>
    rfl

-- С помощью cases можно и функции определять,
-- которые зависят от какие-то индуктивных аргументов.

def f (n : Nat) : Nat := by
  cases n
  · exact 3
  · exact 7

example : f 0 = 3 := rfl

example : f   5 = 7 := rfl
example : f  51 = 7 := rfl
example : f 151 = 7 := rfl

end My15

namespace My16
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

def f {n : Nat} (t : Tuple α n) : Nat := by
  cases n -- Кейсим по длине тапла
  · exact 3
  · exact 7 -- Для любого кортежa не нулевой длины

def myTuple : Tuple Nat 3 := ⟨[0, 1, 2], rfl⟩

example : f myTuple = 7 := rfl

-- Тактики для работы с индуктивными типами.
--
-- Быстрое сравнение трёх главных тактик:
--
--   cases   — разбирает значение на конструкторы, без рекурсивной гипотезы.
--             Используй когда не нужна индукция, просто разбор случаев.
--
--   induction — разбирает + даёт ih (индукционную гипотезу) для рекурсивных аргументов.
--               Используй когда доказательство использует ih.
--
--   injection — разворачивает равенство конструкторов (succ a = succ b → a = b)
--               и обнаруживает противоречия (succ a = zero → False).

-- 1. cases

inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly₀ (x : Foo) : Nat := by
  cases x with
  | bar2 c d e => exact e
  | bar1 a b   => exact b

-- Либо тоже самое, но используя тактику.
def silly₁ (x : Foo) : Nat := by
  cases x
  -- Тактика case поймёт какую подцель нужно доказывать
  -- в каждом из случаев по используемому конструктору.
  case bar2 c d e => exact e
  case bar1 a b   => exact b

open Nat

-- Тактика cases умеет работать и с произвольными выражениями.
-- При cases на выражении (не переменной) Lean сначала обобщает его через generalize.
example (p : Nat → Prop)
        (hz : p 0)
        (hs : ∀ n, p (succ n))
        (m k : Nat) :
        p (m + 3 * k) := by
  cases m + 3 * k -- generalize m + 3 * k = n; cases n
  · exact hz
  · apply hs

-- Можно o `cases m + 3 * k` думать как о
-- команде доказать отдельно следующие 2 факта:
-- 1. m + 3 * k = 0
-- 2. m + 3 * k = succ n

-- Использование cases m + 3 * k эквивалентно этим 2 строчкам:
-- generalize m + 3 * k = n
-- cases n

-- Когда выражение, которое хочется раскидать по кейсам не вcтречается
-- в цели, cases создаёт нам в контексте гипотезу по этому выражению.
-- Точнее: cases <expr> добавляет h : expr = <конструктор> в контекст каждой ветки,
-- что позволяет использовать это равенство в доказательстве.
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p)
        (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n
  · case inl hlt => exact h₁ hlt
  · case inr hge => exact h₂ hge

-- ^ Это эквивалетно следующему:
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  have h : m < n ∨ m ≥ n := Nat.lt_or_ge m n
  cases h
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge

#check Nat.sub_self

-- Это по сути то же самое:
--
-- 1.
-- open Classical
-- em (m = n)
--
-- 2.
-- Decidable.em (m = n)
--
-- Classical.em : ∀ (p : Prop), p ∨ ¬p — закон исключённого третьего (аксиома).
-- Decidable.em: то же самое, но без аксиомы классической логики — работает только
-- для decidable propositions (т.е. для которых существует алгоритм проверки).
-- Равенство натуральных чисел DecidableEq Nat, поэтому Decidable.em применимо.

-- Ещё пример:
example (m n : Nat) : m - n = 0 ∨ m ≠ n := by
  cases Decidable.em (m = n) with
  | inl heq =>
    rw [heq]
    apply Or.inl
    exact Nat.sub_self n
  | inr hne =>
    exact Or.inr hne

end My16

-- 2. induction

namespace My17

-- induction n — порождает две подцели: zero и succ n, при этом в succ-ветке
-- автоматически добавляется ih : <утверждение для n> (индукционная гипотеза).
-- Разница с cases: cases не даёт ih.
--
-- Два синтаксиса: с with (именованные ветки) и с точечной нотацией (· exact ...).
theorem zero_add₀ (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]

-- Альтернативный синтаксис: сначала induction, потом case для именования.
theorem zero_add₁ (n : Nat) : 0 + n = n := by
  induction n
  · case zero => rfl
  · case succ n ih => rw [Nat.add_succ, ih]

-- The induction tactic supports user-defined
-- induction principles with multiple targets.

-- заметка: этот материал оставлен непройденным сознательно.
-- todo: вернуться сюда, когда потребуется более глубокое понимание.

-- Кастомизируемая индукция для операции остатка от деления.
-- Nat.mod.inductionOn — нестандартный принцип индукции специально для %.
-- Он разбивает задачу не на zero/succ, а на два случая:
--   ind: шаг когда y > 0 и y ≤ x (можно вычесть y из x)
--   base: случай когда вычитание невозможно (x < y или y = 0)
-- Это "well-founded" рекурсия по убыванию (x - y < x).
#check Nat.mod.inductionOn

-- {motive : Nat → Nat → Sort u} →
-- (x y : Nat) →
-- ((x y : Nat) → 0 < y ∧ y ≤ x → motive (x - y) y → motive x y) →
-- ((x y : Nat) → ¬(0 < y ∧ y ≤ x) → motive x y) →
-- motive x y

example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih =>
    sorry
  | base x y h₁ =>
    sorry

end My17

-- 3. injection

namespace My18

open Nat

-- Элементы индуктивного типа свободно порождаются,
-- то есть конструкторы инъективны и имеют непересекающиеся
-- области значений. Тактика injection разработана специально для того,
-- чтобы использовать этот факт (инъективности).
--
-- Инъективность: succ a = succ b → a = b.
-- injection h разбивает равенство h : succ a = succ b на a = b,
-- добавляя его в контекст как новую гипотезу.
-- Можно делать injection несколько раз, каждый раз "снимая" один слой succ.

example (m n k : Nat) (h : succ (succ m) = succ (succ n)) : n + k = m + k := by
  injection h with h'
  injection h' with h''
  rw [h'']

-- Тактика injection так же умеет обнаруживать противоречия в контексте:
-- succ m = 0 — это False (разные конструкторы не равны), injection это замечает.
example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  injection h

-- То же самое более явно c помощью тактики contradiction:
-- contradiction ищет в контексте любое явное противоречие:
--   - гипотезу вида False
--   - h : a = b где a и b — разные конструкторы
--   - h : p и h' : ¬p одновременно
example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  contradiction

example (h : 7 = 4) : False := by
  contradiction

end My18

namespace My19

-- 7.6 Продолжение тактик: match внутри тактик, деструктуризация intro и funext
--
-- Lean позволяет смешивать term-mode и tactic-mode. В частности:
--   - match можно писать прямо внутри блока by
--   - intro поддерживает деструктуризацию паттернов (анонимная деструктуризация)
--   - funext может принимать паттерны для аргументов-пар

-- match можно использовать прямо внутри тактик-мод доказательства:
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  match h with
  | Or.inl hp => exact Or.inr hp
  | Or.inr hq => exact Or.inl hq

-- intro поддерживает анонимное деструктурирование — вместо двух шагов:
-- (intro h1 h2; obtain ⟨_, hq, _⟩ := h1; obtain ⟨hp, _⟩ := h2)
-- можно написать одной строкой. _ означает "поле нас не интересует".
example (s q r p : Prop) : s ∧ q ∧ r → p ∧ r → q ∧ p := by
  intro ⟨_, hq, _⟩ ⟨hp, _⟩
  exact ⟨hq, hp⟩

-- funext поддерживает деструктуризацию пар прямо в подписи:
-- funext (a, b) (c, d) — вместо funext p q; obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q.
-- funext — это принцип функциональной экстенсиональности: f = g ↔ ∀ x, f x = g x.
example :
    (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2)
    =
    (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (c, d)
  show a + d = d + a
  rw [Nat.add_comm]

-- <;> применяет тактику ко всем подцелям одновременно.
-- Вместо перечисления всех веток — одна строка:
-- omega — тактика для линейной арифметики; использует гипотезы из контекста.
--
-- В случае `induction n <;> omega`:
--   - induction n создаёт две подцели: zero и succ n (с ih)
--   - <;> omega применяет omega к обеим
--   - в ветке zero: m + 0 = 0 + m — omega решает (это линейная арифметика)
--   - в ветке succ: контекст содержит ih : m + n = n + m, omega использует его
-- omega — полная процедура решения для линейной арифметики над ℤ/ℕ.
example (m n : Nat) : m + n = n + m := by
  induction n <;> omega

end My19

namespace My20

-- 7.7 Индуктивные семейства (Inductive Families)

-- Обычный индуктивный тип живёт в Sort u.
-- Индуктивное *семейство* — это функция ... → Sort u,
-- где "..." — последовательность индексов.
-- Каждый конструктор строит элемент конкретного члена семейства.
--
-- Разница между параметром и индексом:
--   параметр (α в List α) — фиксирован для всего типа, не меняется от конструктора к конструктору.
--   индекс  (n в Vect α n) — может быть разным для разных конструкторов.
--
-- В синтаксе: параметры идут до двоеточия (`inductive Foo (α : Type)`),
-- индексы — после двоеточия (`inductive Foo : Nat → Type`).

-- Классический пример: вектор фиксированной длины.
-- Nat-индекс в типе отслеживает длину статически.
inductive Vect (α : Type u) : Nat → Type u where
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)

-- cons берёт Vect α n → Vect α (n+1): длина растёт в типе.
-- Передать Vect α 2 туда, где нужен Vect α 3 — ошибка компиляции.
--
-- Это называется "зависимые типы в действии": инвариант (длина) часть типа.
-- Функция append для Vect будет иметь тип:
--   Vect α m → Vect α n → Vect α (m + n)
-- Lean статически проверит, что длины складываются правильно.
-- List этого гарантировать не может — длина там только в рантайме.

-- Равенство само является индуктивным семейством!
-- Eq a : α → Prop  параметрическое по второму аргументу.
namespace Hidden

inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a

-- Единственный конструктор refl строит только Eq a a.
-- Построить Eq a x возможно, только если x вычисляется в a.

-- Тип элиминатора Eq.rec:
-- @Eq.rec :
--   {α : Sort u} → {a : α} →
--   {motive : (x : α) → a = x → Sort v} →
--   motive a rfl →           -- результат для случая x = a
--   {b : α} → (h : a = b) → -- гипотеза равенства
--   motive b h               -- результат для произвольного b

-- Из refl и Eq.rec выводятся все базовые аксиомы равенства!
-- Симметрия, транзитивность, конгруэнтность — всё это теоремы, а не аксиомы.
-- Единственная аксиома — rfl (reflexivity).

-- Подстановка через Eq.rec:
-- motive := fun x _ => p x  — мы хотим получить p b из p a
theorem subst_rec {α : Type u} {a b : α} {p : α → Prop}
    (h₁ : Eq a b) (h₂ : p a) : p b :=
  Eq.rec (motive := fun x _ => p x) h₂ h₁

end Hidden

-- Подстановка через match (со стандартным Eq = (· = ·)):
-- При match h : a = b с паттерном rfl, Lean унифицирует a и b,
-- и p b становится тем же, что и p a — h₂ подходит напрямую.
--
-- Механика: после match h with | rfl => ... система знает что a ≡ b
-- (definitionally equal), поэтому тип p b "схлопывается" в p a.
-- h₂ : p a удовлетворяет цели p b без каких-либо преобразований.
theorem mySubst {α : Type u} {a b : α} {p : α → Prop}
    (h₁ : a = b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂

-- Симметричность: a = b → b = a
-- После match h with | rfl: a и b унифицированы, цель b = a становится a = a, rfl.
theorem mySymm {α : Type u} {a b : α} (h : a = b) : b = a :=
  match h with
  | rfl => rfl

-- Транзитивность: a = b → b = c → a = c
-- match h₁, h₂ with | rfl, rfl: a≡b, b≡c, цель a = c становится a = a, rfl.
theorem myTrans {α : Type u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c :=
  match h₁, h₂ with
  | rfl, rfl => rfl

-- Конгруэнтность: a = b → f a = f b
-- После rfl: a≡b, цель f a = f b становится f a = f a, rfl.
theorem myCongr {α : Type u} {β : Type v} {a b : α} (f : α → β) (h : a = b) : f a = f b :=
  match h with
  | rfl => rfl

end My20

-- 7.8 Аксиоматические детали (Axiomatic Details)

-- строгая позитивность (strict positivity):
-- Если определяемый тип T встречается в аргументах конструктора,
-- он должен стоять только в covariant позиции — как "результат" стрелки,
-- но не как аргумент функции (т.е. не слева от →).
--
-- Правильно:
--   inductive T where | mk : T → T              -- T справа от →
--   inductive T where | mk : (Nat → T) → T      -- T только как результат
--
-- Запрещено (нарушение строгой позитивности):
--   inductive Bad where | mk : (Bad → Nat) → Bad  -- Bad слева от →
--
-- Нарушение позволило бы закодировать самореференцию и получить противоречие.
--
-- Почему конкретно? Если бы Bad → Nat → Bad было разрешено, можно было бы
-- построить нетипизированную лямбду и закодировать Y-комбинатор, что даёт
-- незаканчивающееся вычисление — противоречие в системе с нормализацией.

-- ограничения вселенных:
-- Если C : Sort u и каждый аргумент конструктора имеет тип Sort v,
-- то u ≥ v. Тип не может жить в меньшей вселенной, чем его данные.
--
-- Например: нельзя определить inductive Foo : Prop where | mk : Type → Foo,
-- потому что Type = Sort 1 > Sort 0 = Prop. Данные из большей вселенной
-- не могут "поместиться" в меньшую.

-- prop и элиминация:
-- типы в Prop могут элиминироваться только в другие Prop.
-- нельзя "извлечь данные" из доказательства для вычислений (proof irrelevance:
-- все доказательства одного утверждения считаются равными, детали стёрты).

-- исключение — singleton elimination (одиночная элиминация):
-- Если индуктивный Prop-тип имеет ровно один конструктор,
-- и каждый аргумент конструктора либо в Prop, либо является индексом —
-- допускается элиминация в произвольный Sort.
-- Причина: такой тип не несёт "новых данных" — только сам факт обитаемости.
--
-- Пример: Eq a b (один конструктор refl, аргументов-данных нет).
-- Поэтому Eq.rec позволяет приводить типы: из h : a = b и h₂ : p a
-- получаем p b даже если p : α → Type u (не Prop).
-- Информация не прибавляется — только переинтерпретируется.
-- (То же самое используют гетерогенное равенство и well-founded рекурсия.)

namespace My21

-- 7.9 Взаимные и вложенные индуктивные типы

-- взаимные (mutual): два и более типов определяются одновременно
-- и ссылаются друг на друга. Lean компилирует их в обычные индуктивные типы.

mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end

-- Чётное — это 0 или (succ нечётного). Нечётное — succ чётного.
-- Even и Odd определены через взаимную рекурсию: каждый ссылается на другой.
-- Lean компилирует это в единый индуктивный тип с двумя "ветками" под капотом.
example : Even 0 := Even.even_zero
-- Even 2 = Even.even_succ 1 (Odd.odd_succ 0 Even.even_zero)
-- Читается: 2 = succ 1, а 1 нечётно (1 = succ 0, 0 чётно).
example : Even 2 := Even.even_succ 1 (Odd.odd_succ 0 Even.even_zero)
-- Odd 1 = Odd.odd_succ 0 Even.even_zero
-- Читается: 1 = succ 0, 0 чётно, значит 1 нечётно.
example : Odd  1 := Odd.odd_succ   0 Even.even_zero

-- Дерево с произвольным числом поддеревьев:
mutual
  inductive Tree (α : Type u) where
    | node : α → TreeList α → Tree α

  inductive TreeList (α : Type u) where
    | nil  : TreeList α
    | cons : Tree α → TreeList α → TreeList α
end

-- Неудобно: TreeList α вместо List (Tree α) — теряем всю стандартную библиотеку.

-- вложенные (nested): Tree встречается внутри List — технически нарушение
-- строгой позитивности, но Lean принимает это и автоматически строит
-- изоморфизм TreeList α ≅ List (Tree α) в ядре системы.
inductive Tree' (α : Type u) where
  | mk : α → List (Tree' α) → Tree' α

-- Теперь поддеревья — List (Tree' α): вся стандартная библиотека List доступна.

end My21

-- Упражнения из книги

-- 1. Дополнительные операции на натуральных числах
namespace Ex1

-- Умножение — рекурсия по второму аргументу
def mul (m : Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => mul m n + m   -- m * (n+1) = m*n + m

-- Предшественник (pred 0 = 0 по определению)
def pred : Nat → Nat
  | 0     => 0
  | n + 1 => n

-- Усечённое вычитание (n - m = 0 если m ≥ n)
def sub (n : Nat) : Nat → Nat
  | 0     => n
  | m + 1 => pred (sub n m)

-- Степень
def pow (m : Nat) : Nat → Nat
  | 0     => 1
  | n + 1 => mul (pow m n) m   -- m^(n+1) = m^n * m

-- Базовые леммы по определению:
theorem mul_zero (m : Nat)     : mul m 0       = 0           := rfl
theorem mul_succ (m n : Nat)   : mul m (n + 1) = mul m n + m := rfl
theorem pow_zero (m : Nat)     : pow m 0       = 1           := rfl
theorem pow_succ (m n : Nat)   : pow m (n + 1) = mul (pow m n) m := rfl

-- Более сложные свойства доказываются индукцией.
-- Для mul_comm нужны вспомогательные леммы:
--
-- Стратегия: mul_comm не доказывается прямой индукцией, потому что в шаге
-- возникают подцели вроде `mul 0 m = 0` и `mul (m+1) n = mul m n + n`,
-- которые сами по себе требуют индукции. Сначала доказываем их отдельно
-- (zero_mul, succ_mul), а потом mul_comm становится тривиальным с simp.

-- mul 0 n = 0  (по индукции по n)
theorem zero_mul (n : Nat) : mul 0 n = 0 := by
  induction n with
  | zero      => rfl
  | succ n ih => simp [mul, ih]

-- mul (m+1) n = mul m n + n  (по индукции по n)
-- В шаге: mul (m+1) (n+1) = mul (m+1) n + (m+1) [по def]
--                          = (mul m n + n) + (m+1) [по ih]
--                          = mul m (n+1) + (n+1) [нужна арифметика]
-- omega закрывает арифметическую часть перестановки слагаемых.
theorem succ_mul (m n : Nat) : mul (m + 1) n = mul m n + n := by
  induction n with
  | zero      => rfl
  | succ n ih => simp [mul, ih]; omega

theorem mul_comm (m n : Nat) : mul m n = mul n m := by
  induction n with
  | zero      => simp [mul, zero_mul]
  | succ n ih => simp [mul, succ_mul, ih]

end Ex1

-- 2. Операции на списках
namespace Ex2

-- length уже определялся в My13; reverse — классический пример рекурсии на списках.
-- reverse [1,2,3] = reverse [2,3] ++ [1] = (reverse [3] ++ [2]) ++ [1]
--                = (([] ++ [3]) ++ [2]) ++ [1] = [3,2,1]
def reverse {α : Type u} : List α → List α
  | []      => []
  | x :: xs => reverse xs ++ [x]

-- reverse_append_singleton — ключевая вспомогательная лемма для reverse_reverse.
-- Без неё в шаге индукции reverse_reverse возникает цель:
--   reverse (reverse xs ++ [x]) = x :: reverse (reverse xs)
-- Эту цель нельзя решить напрямую — нужно сначала "вытащить" x из аргумента reverse.
-- Лемма говорит: если добавить элемент в конец, он окажется в начале после reverse.
theorem reverse_append_singleton {α : Type u} (x : α) (xs : List α) :
    reverse (xs ++ [x]) = x :: reverse xs := by
  induction xs with
  | nil      => rfl
  | cons y ys ih => simp [List.cons_append, reverse, ih]

-- Длина не меняется при reverse: индукция по xs.
-- В шаге: (reverse (x :: xs)).length = (reverse xs ++ [x]).length
--                                     = reverse xs length + 1 = xs.length + 1
theorem length_reverse {α : Type u} (xs : List α) :
    (reverse xs).length = xs.length := by
  induction xs with
  | nil      => rfl
  | cons x xs ih => simp [reverse, List.length_append, ih]

-- reverse (reverse xs) = xs
-- В шаге: reverse (reverse (x :: xs)) = reverse (reverse xs ++ [x])
--       = x :: reverse (reverse xs) [по reverse_append_singleton]
--       = x :: xs [по ih]
theorem reverse_reverse {α : Type u} (xs : List α) :
    reverse (reverse xs) = xs := by
  induction xs with
  | nil      => rfl
  | cons x xs ih => simp [reverse, reverse_append_singleton, ih]

end Ex2

-- 3. Тип арифметических выражений и вычислитель
namespace Ex3

-- Term — AST (abstract syntax tree) арифметических выражений.
-- Это стандартный паттерн для интерпретаторов:
--   1. определить тип выражений (Term)
--   2. написать функцию eval (интерпретатор)
-- Term рекурсивен: plus и times содержат вложенные Term.
inductive Term where
  | const (n : Nat)           -- числовая константа
  | var   (n : Nat)           -- переменная с номером n
  | plus  (s t : Term)        -- сложение двух подвыражений
  | times (s t : Term)        -- умножение двух подвыражений

open Term

-- env : Nat → Nat задаёт значения переменным по номеру.
-- Это "окружение" (environment) или "контекст" переменных.
-- Переменная с номером n получает значение env n.
-- Такое представление удобнее Map, потому что нет зависимости от конкретной структуры данных.
def eval (env : Nat → Nat) : Term → Nat
  | const n   => n
  | var n     => env n
  | plus s t  => eval env s + eval env t
  | times s t => eval env s * eval env t

-- Пример: (x₀ + 2) * 3, где x₀ = 5 → (5 + 2) * 3 = 21
-- env = fun n => if n = 0 then 5 else 0  — x₀ = 5, все остальные переменные = 0
def exampleTerm : Term := times (plus (var 0) (const 2)) (const 3)
#eval eval (fun n => if n = 0 then 5 else 0) exampleTerm  -- 21

end Ex3

-- 4. Тип пропозициональных формул
namespace Ex4

-- PropFormula — AST пропозициональной логики.
-- Те же паттерны что в Ex3 (Term), только операции логические а не арифметические.
-- Переменные пронумерованы натуральными числами
inductive PropFormula where
  | var    (n : Nat)
  | top                             -- ⊤ (tautology, всегда true)
  | bot                             -- ⊥ (contradiction, всегда false)
  | neg    (p : PropFormula)
  | conj   (p q : PropFormula)      -- p ∧ q
  | disj   (p q : PropFormula)      -- p ∨ q
  | impl   (p q : PropFormula)      -- p → q

open PropFormula

-- Вычислитель: env задаёт булевы значения переменным
def eval (env : Nat → Bool) : PropFormula → Bool
  | var n    => env n
  | top      => true
  | bot      => false
  | neg p    => !eval env p
  | conj p q => eval env p && eval env q
  | disj p q => eval env p || eval env q
  | impl p q => !eval env p || eval env q  -- p → q ≡ ¬p ∨ q (материальная импликация)
  -- Импликация в классической логике ложна только если p истинно, а q ложно.
  -- !p || q: если p = false, то !p = true и весь OR = true. Если p = true, то q решает.

-- Сложность: число логических связок.
-- Атомарные формулы (var, top, bot) имеют сложность 0.
-- Составные формулы: сложность = 1 (за связку) + сложность подформул.
def complexity : PropFormula → Nat
  | var _    => 0
  | top      => 0
  | bot      => 0
  | neg p    => 1 + complexity p
  | conj p q => 1 + complexity p + complexity q
  | disj p q => 1 + complexity p + complexity q
  | impl p q => 1 + complexity p + complexity q

-- Подстановка: заменить переменную n формулой φ во всей формуле.
-- Это рекурсивный обход дерева: на каждом узле либо делаем замену (если var m = var n),
-- либо рекурсивно спускаемся в подформулы. Структура формулы сохраняется.
def subst (n : Nat) (φ : PropFormula) : PropFormula → PropFormula
  | var m    => if m = n then φ else var m
  | top      => top
  | bot      => bot
  | neg p    => neg (subst n φ p)
  | conj p q => conj (subst n φ p) (subst n φ q)
  | disj p q => disj (subst n φ p) (subst n φ q)
  | impl p q => impl (subst n φ p) (subst n φ q)

-- Пример: (x₀ ∧ x₁) → x₀, где x₀ = true, x₁ = false → true
-- env = fun n => n == 0: x₀ = true, x₁ = false, остальные = false
-- eval: impl (conj true false) true = !（true && false) || true = !false || true = true
def exampleFormula : PropFormula := impl (conj (var 0) (var 1)) (var 0)
#eval eval (fun n => n == 0) exampleFormula  -- true

end Ex4
