-- 10. Type Classes

namespace My1

class Add (α : Type) where
  add : α → α → α

#check @Add.add

instance : Add Nat where
  add := Nat.add

instance : Add Int where
  add := Int.add

instance : Add Float where
  add := Float.add

def double [Add α] (x : α) : α :=
  Add.add x x

#check @double -- {α : Type} → [Add α] → α → α

#eval double 10
#eval double (10 : Int)
#eval double (10 : Float)
#eval double (239.0 + 2)

-- Инстансы могут зависет от других инстансов.

-- instance [Add α] : Add (Array α) where
--   add x y := Array.zipWith (fun a b => a + b) x y

-- Т.е. классы типов можно использовать для перегрузки нотаций:

-- #eval Add.add #[1, 2] #[3, 4]
-- #[4, 6]

-- #eval #[1, 2] + #[3, 4]
-- #[4, 6]

-- Inhabited это как Default в Rust.
class Inhabited (α : Type u) where
  default : α

#check Inhabited.default

-- Это полезный тайпкласс. Иногда нам нужен факт обитаемости.
-- Например, для типа непустых списков, ну или для ∃ x : α, x = x
-- требуется, чтобы тип α был обитаем по крайней мере одним x.

instance : Inhabited Bool where default := true
instance : Inhabited Nat where default := 0
instance : Inhabited Unit where default := ()
instance : Inhabited Prop where default := True

-- Можно вытащить default из неймспейса наружу, это удобно.
export Inhabited (default)

#eval (default : Nat)  -- 0
#eval (default : Bool) -- true

end My1

-- Chaining instances

namespace My2
instance [Inhabited α] [Inhabited β] : Inhabited (α × β) where
  default := (default, default)

#eval (default : Nat × Bool) -- (0, false)

instance [Inhabited β] : Inhabited (α → β) where
  default := λ _ => default

instance : Inhabited (List α) where
  default := List.nil

instance [Inhabited α] : Inhabited (Sum α β) where
  default := Sum.inl default

 -- inferInstance.{u} {α : Sort u} [i : α] : α
 --                                   ^
 --                         instance of typeclass α
#check inferInstance

#check (inferInstance : Inhabited Nat)

def foo : Inhabited (Nat × Nat) := inferInstance

theorem ex : foo.default = (default, default) := rfl

end My2

-- ToString

namespace My3

structure Person where
  name : String
  age  : Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

def vasya := { name := "skufidon Vasya", age := 40 : Person }

#eval toString vasya
#eval (vasya, "is learning lean4")

structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

-- Если хочешь, чтобы твой тип мог парситься из числовых литералов,
-- то его нужно сделать инстансом класса типов OfNat.
#eval (2 : Nat)
-- Когда ты пишешь `2 : α`, линь "под капотом" попробует синтезировать
-- инстанс `OfNat α 2` и сгенерирует терм вида `OfNat.ofNat 2 : α`.
--
-- Тепреь глянь на него внимательно:
-- `OfNat.ofNat 2 : α`
--          ^   ^
--        Здесь 2 это не тоже самое, что и просто `2`.
--        Именно тут это `nat_lit 2`. И "это другое".
--
-- Макрос `nat_lit n` конструирует вот эти "сырые числовые литералы".
-- "Сырые" в том смысле, что они соотвествуют `Expr.lit (.natVal n)`,
-- и для них линь не пытается (ещё раз) сделать `OfNat.ofNat 2 : α`.
-- Ну ты понял, да? Ведь обычно (как только что было упомянуто выше),
-- когда ты пишешь числовой литерал `#check 2`, парсер превращает
-- просто число `2` в применение `OfNat.ofNat` к этому твоему числу `2` и
-- приводит это к целевому типу, даже если это тот же Nat
-- (в таком случае приведение типа это id: Nat → Nat).
-- Иметь возможность написать "сырой числовой литерал" необходимо
-- в том числе и потому, что иногда нам нужно строить утверждения и
-- рассуждать непосредственно об этих "сырых числовых литералах".
-- Особенно, если мы доказываем какие-то свойства про саму функцию `ofNat`.

-- Т.е. более корректно было бы сказать, что линь, когда видит `2 : α`
-- пробует синтезировать инстанс `OfNat α (nat_lit 2)` и сгенерирует терм
-- вида `OfNat.ofNat (nat_lit 2) : α`

instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational)
#eval (2 : Nat)

#check nat_lit 2

-- Давай ради прикола ещё один пример для OfNat напишем.
-- Пусть у нас будет тип, который представляет собой целочисленный
-- интервал от а до a + 5: [a, a + 5].

structure Range5 where
  a : Int
  b : Int

instance : OfNat Range5 n where
  ofNat := { a := n, b := n + 5 }

instance : Add Range5 where
  add x y := Range5.mk (x.a + y.a) (x.b + y.b)

-- instance : ToString Rational where
--   toString r := s!"{r.num}/{r.den}"

instance : ToString Range5 where
  toString r := s!"[{r.a}, {r.b}]"

#check (2 : Range5)
#eval toString (2 : Range5) -- "[2, 7]"

class Monoid (α : Type u) where
  unit : α
  op : α → α → α

-- Инстанс OfNat α _ параметризирован числом (литералом).
--                 ^ - речь про этот вот второй параметр (на месте подчёркивания).
-- Поэтому можно определять отдельные инстансы для конкретных чисел.
-- Второй аргумент обычно бывает переменной, как в примере выше,
-- или просто натуральным числом.

-- instance [s : Monoid α] : OfNat α n where
instance [s : Monoid α] : OfNat α (nat_lit 1) where
  ofNat := s.unit

def getUnit [Monoid α] : α := 1

end My3

-- 10.4 Output Parameters
-- 10.5 Default Instances
-- 10.6 Local Instances
-- 10.7 Scoped Instances

namespace My4
end My4

namespace My5
end My5

namespace My6
end My6

namespace My7
end My7

-- 10.8 Decidable Propositions

-- Имеет смысл сначала прочитать:
-- https://en.wikipedia.org/wiki/Decidability_(logic)

-- Вычислительная разрешимость (Decidability) это не аксиома.
-- Если ты хочешь раскидывать какие-то утверждения по кейсам (p ∨ ¬p),
-- то в конструктивной логике (ну короче всегда) ты должен ввести гипотезу
-- о разрешимости p, проще говоря, сделать p инстансом Decidable.
-- Или ещё проще: Decidable p → ... your goal ...

-- Чтобы вообще было справедливо использовать исключенное третье (em),
-- и рассуждать в духе "или p истина или p ложь", p должно быть Decidable.

-- Decidable - класс типов "разрешимых" высказываний, он определён в стандартной библиотеке.
-- Грубо говоря, элемент типа Prop называется разрешимым, если можно (алгоритмически, конструктивно)
-- определить, истинно оно или ложно.
-- Вот тут понятнее и подробнее можно почитать:
-- https://ru.wikipedia.org/wiki/%D0%97%D0%B0%D0%B4%D0%B0%D1%87%D0%B0_%D1%80%D0%B0%D0%B7%D1%80%D0%B5%D1%88%D0%B8%D0%BC%D0%BE%D1%81%D1%82%D0%B8
-- Это различие имеет смысл только в конструктивной логике.
-- В классической логике любое высказывание считается разрешимым.
-- Однако, если воспользоваться классической логикой, (например, при определении функции),
-- то такая функция уже не будет вычислимой. С алгоритмической точки зрения
-- класс типов [Decidable] позволяет вывести процедуру, которая эффективно определяет,
-- истинно ли данное высказывание. Таким образом, этот класс типов поддерживает
-- вычислимые определения, когда это возможно, и при этом обеспечивает плавный переход к
-- использованию классических определений и рассуждений.

namespace My8

class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h :  p) : Decidable p

-- Ну вот, чтобы вообще можно было рассматривать выражения типа
-- if p then e₁ else e₂, то (p : Prop) должно быть разрешимо.
-- Это значит должен существовать вычислительный способ
-- установить истинность или ложность p.

-- ite - if then else
-- if (Decidable c) then t else f
def ite
    {α : Sort u}
    (c : Prop) [h : Decidable c]
    (t f : α) : α :=
  h.casesOn
    (motive := fun _c => α) -- Decidable c -- condition
    (fun _hnc => f) -- ветка true
    (fun _hc  => t) -- ветка false

-- В dite (dependent if then else) аргументы это функции,
-- а в ite аргументы это значения.

def dite
    {α : Sort u}
    (c : Prop) [h : Decidable c]
    (t :     c → α)
    (f : Not c → α) : α :=
  Decidable.casesOn (motive := fun _c => α) h f t

--  if h : c then t else e
--      это сахар для
-- dite c (fun h : c => t h) (fun h : ¬c => e h)

-- instDecidableAnd
--   {p q : Prop}
---  [dp : Decidable p]
--   [dq : Decidable q]
--   : Decidable (p ∧ q)
#check instDecidableAnd

#check instDecidableOr
#check instDecidableNot

def step (a b x : Nat) : Nat :=
  if x < a ∨ x > b then 0 else 1

set_option pp.explicit true
#print step

-- Короче мозг не еби - вся дизъюнкция либо истинна либо ложна -
-- это и есть разрешимое утверждение, разрешимость которого выводится
-- элаборатором, применением соответствующих инстансов класса типов Decidable:
-- instDecidableOr, instLTNat, instOfNatNat.

-- def step : Nat → Nat → Nat → Nat := fun a b x ↦
--   @ite
--     Nat
--     (Or
--       (@LT.lt Nat instLTNat x a)
--       (@GT.gt Nat instLTNat x b))
--     (@instDecidableOr
--       (@LT.lt Nat instLTNat x a)
--       (@GT.gt Nat instLTNat x b)
--       (x.decLt a)
--       (b.decLt x))
--     (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
--     (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))

end My8

namespace My9
-- В классической логике любое утверждение p является разрешимым.
-- Если хочется это использовать, то можено открыть неймспейс Classical.

open Classical

-- После этого класс Decidable имеет инстанс для любого утверждения p.
-- Таким образом, все теоремы в библиотеке, которые зависят от
-- предположений о разрешимости, становятся автоматически доступными,
-- когда мы работаем в классической логике.

-- В разделе Axioms and Computation будет показано, что использование закона
-- исключённого третьего (em) для определения функций может сделать их
-- непригодными для вычислений. Поэтому стандартная библиотека присваивает
-- низкий приоритет экземпляру propDecidable.

-- This guarantees that Lean will favor other instances and
-- fall back on propDecidable only after other attempts
-- to infer decidability have failed.

noncomputable scoped
instance (priority := low) propDecidable (p : Prop) : Decidable p :=
  choice <| match em p with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩

-- Класс типов Decidable также предоставляет небольшую
-- автоматизацию в виде тактики decide, которая использует инстанс Decidable,
-- чтобы решать простые цели. И есть ещё функция decide, которая использует
-- инстанс Decidable для вычисления соответствующего значения типа Bool.

-- Тактика decide пытается доказать основную цель (типa p),
-- синтезируя инстанс Decidable p, а затем сводя этот
-- инстанс к вычислению "истинности" p (редукцией до
-- конструкторов Decidable: isTrue | isFalse).
--
-- Если при вычислении получается значение (isTrue (h : p) : Decidable p),
-- то h является доказательством p, которое завершает цель (закрывает её).

-- Цель не должна содержать локальных переменных или метапеременных.
-- Если в цели есть локальные переменные, можно сначала попробовать
-- использовать тактику revert с этими переменными, чтобы переместить их в цель.

-- На натуральных числах равенство это разрешимое утверждение:
-- instance : DecidableEq Nat := Nat.decEq

-- Хочешь понять как работает тактика decide?
-- Загляни вот сюда, внутрь Nat.decEq.
#check Nat.decEq 5 5 = isTrue rfl
-- Ещё примеры:
#check (if 3 = 4 then "yes" else "no") = "no"
#check show 12 = 12 by decide

-- Пиздец это какая мощная тактика:
example : 10 < 5 ∨ 1 > 0 := by decide
example : ¬(True ∧ False) := by decide
example : 10 * 20 = 200 := by decide

theorem ex : True ∧ 2 = 1 + 1 := by decide

-- offtopic, but: Вот так можно посмотреть
-- от каких аксиом зависит конкретная теорема:
#print axioms ex

end My9

-- TODO: Вернуться позже и доботать
--  10.9. Managing Type Class Inference
-- 10.10. Coercions using Type Classes
