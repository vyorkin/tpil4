-- 7. Inductive Types

-- В lean 4 любой конкретный тип (кроме вселенных - универсумов типов) и
-- любой конструктор типа (кроме зависимых стрелочных типов) является
-- индуктивным типом.

-- Угарно, что можно построить довольно большой фундамен математики,
-- опираясь только на универсумы типов, зависимые стрелочные типы и
-- индуктивные типы; всё остальное выводится из них.

-- Типичный индуктивный тип выглядит так:

-- inductive Foo where
--   | constructor₁ : ... → Foo
--   | constructor₂ : ... → Foo
--   ...
--   | constructorₙ : ... → Foo

namespace My1

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
-- точки теории типов. При компиляции match превращается примерно в то же,
-- что в других ЯП.

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

-- {motive : (t : Weekday) → Sort u} →
--  ^^ Здесь motive t это зависимая (от t) функция из вселенной Sort u.
--     Для каждого t (дня недели) может быть свой тип `motive t`

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

theorem next_previous₀ (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl

theorem next_previous₁ (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl

end Weekday

end My4

namespace My5

inductive Bool where
  | false : Bool
  | true  : Bool

-- Introduction и elimination rules для такого типа это просто его конструкторы.

end My5

namespace My6

-- Обычно конструкторы индуктивных типов всё таки принимают
-- какие-то аргументы, ну вот как в типе-сумме или типе-произведении.

inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β
-- ^ Ниже будет показано как определить тип-произведение более идиоматично,
--   используя keyword "structure"

inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : α → Sum α β

-- where писать не обязательно

def fst {α : Type u} {β : Type v} {p : Prod α β} : α :=
  match p with
  | Prod.mk a _ => a

def snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
  match p with
  | Prod.mk _ b => b

-- Конструирует тебе чётное или нечётное число, в зависимости от
-- того что слева у этой пары:

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

def prod_example (p : Prod Bool Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p
    (fun b n => cond b (2 * n) (2 * n + 1))

-- Тут зависимая функция (motive := fun _ => Nat) используется,
-- чтобы сообщить тип конструируемого объекта.
-- Да, это функция, потому что тип может зависить от значения Prod Bool Nat.
-- А cond это типа: if b the (2 * n) else (2 * n + 1)

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

def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := fun _ => Nat) s
    (fun n => 2 * n)
    (fun n => 2 * n + 1)

#eval sum_example (Sum.inl 3) -- 6
#eval sum_example (Sum.inr 3) -- 7

end My6

namespace My7

-- Вот так ещё можно определить тип-произведение сразу вместе с проекциями.

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

structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α

inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α

-- product of two inhabited types is inhabited

-- Не уверен, что это то, что просил показать автор.
-- Возможно он хотел, чтобы я использовал утверждения и
-- представил это как theorem prod_inh.

def prod_inh (α : Type u) (β : Type v)
  : (a : Inhabited α) → (b : Inhabited β) → (Inhabited (α × β)) :=
  λ (Inhabited.mk a) (Inhabited.mk b) => Inhabited.mk (a, b)

-- type of functions to an inhabited type is inhabited

def funs_inh (α : Type u) (β : Type v)
  : (α → Inhabited β) → Inhabited (α → β) :=
  λ f => Inhabited.mk (λ a => match f a with | Inhabited.mk b => b)

end My8

namespace My9

def compose (f : α → Option β) (g : β → Option γ) : α → Option γ :=
  fun a =>
    match f a with
    | none => none
    | some b => g b

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

-- Да, мы больше не будем явно писать mk при
-- определении индуктивных типов-произведений.

end My10

namespace My11

-- Наименьший рекурсивный тип из возможных.
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

-- Здесь {f : Nat → Sort u} это зависимая функция (из вселенной Sort u).
-- По сути ф-ция Nat.rec может возвращать для каждого натурального
-- числа (n : Nat) какой-то свой тип.

#check Nat.recOn

-- Функция recOn это та же rec, только аргументы местами переставлены:
--
-- Nat.recOn.{u} :
--   {f : Nat → Sort u} →
--
--   (n : Nat) →
--
--   (zero : f zero) →
--   (succ : ((n : Nat) → f n → f n.succ)) →
--
--   f n

-- Если зафиксируем m, то можно определить сложение рекурсивно по n.
def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero => m
  | Nat.succ n' => Nat.succ (add m n')

open Nat

#eval add (succ (succ zero)) (succ zero)
--         succ (succ (succ (zero)))

-- Чтобы эти 2 теоремки ниже доказывались по определению,
-- мы должны сделать Nat инстансом Add. Про классы типов будет чуть позже.

instance : Add Nat where
  add := add

theorem add_zero (m : Nat) : m + zero = m := rfl
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

end My11

namespace My12

open Nat

-- Но 0 + n = n нужно доказывать по индукции.

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

theorem add_comm₀ (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := λ x ↦ m + x = x + m) n
    (show m + 0 = 0 + m by rw [Nat.add_zero, Nat.zero_add])
    (λ (n : Nat) (ih : m + n = n + m) ↦
      show m + (succ n) = (succ n) + m from
      calc
        m + (succ n) = succ (m + n) := rfl
        _ = succ (n + m) := by rw [ih]
        _ = (succ n) + m := sorry) -- Need: succ (n + m) = (succ n) + m

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

inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree

-- Countably branching tree
inductive CBTree where
  | leaf : CBTree
  | sup : (Nat → CBTree) → CBTree

namespace CBTree
def succ (t : CBTree) : CBTree :=
  sup (fun _ => t)

def toCBTree : Nat → CBTree
  | 0 => leaf
  | n + 1 => succ (toCBTree n)

def omega : CBTree :=
  sup toCBTree

end CBTree

end My14

namespace My15

example (p : Nat → Prop)
        (hz : p 0)
        (hs : ∀ n, p (Nat.succ n)) :
        ∀ n, p n := by
  intro n
  cases n
  · exact hz
  · apply hs

open Nat

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

theorem zero_add₀ (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]

theorem zero_add₁ (n : Nat) : 0 + n = n := by
  induction n
  · case zero => rfl
  · case succ n ih => rw [Nat.add_succ, ih]

-- The induction tactic supports user-defined
-- induction principles with multiple targets.

-- NOTE: Я оставляю этот материал не пройденным сознательно.
-- TODO: Вернуться сюда, когда мне потребуется более глубокое понимание.

-- Кастомизируемая индукция для операции остатка от деления.
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

example (m n k : Nat) (h : succ (succ m) = succ (succ n)) : n + k = m + k := by
  injection h with h'
  injection h' with h''
  rw [h'']

-- Тактика injection так же умеет обнаруживать противоречия в контексте:
example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  injection h

-- То же самое более явно c помощью тактики contradiction:
example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  contradiction

example (h : 7 = 4) : False := by
  contradiction

end My18

-- TODO: Inductive Families etc

-- TODO: Exercises

-- 1.
-- Define an inductive data type consisting of
-- terms built up from the following constructors:
--
-- const n, a constant denoting the natural number n
-- var n, a variable, numbered n
-- plus s t, denoting the sum of s and t
-- times s t, denoting the product of s and t

-- 2.
-- Recursively define a function that evaluates any
-- such term with respect to an assignment of values to the variables.
-- Similarly, define the type of propositional formulas,
-- as well as functions on the type of such formulas:
-- an evaluation function, functions that measure the
-- complexity of a formula, and a function that
-- substitutes another formula for a given variable.
