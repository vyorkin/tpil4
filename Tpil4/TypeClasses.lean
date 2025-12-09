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

-- Инстансы класса типов OfNat представимы и
-- попарсиваемы в виде числовых литералов.

instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational)
#eval (2 : Nat)

#check nat_lit 2

class Monoid (α : Type u) where
  unit : α
  op : α → α → α

-- Инстанс OfNat α _ параметризирован числом (литералом).
--                 ^ - речь про этот параметр.
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

-- Рассмотрим ещё один пример класса типов, определённого в стандартной библиотеке,
-- а именно класс типов Decidable — "разрешимых" высказываний.
-- Грубо говоря, элемент типа Prop называется разрешимым, если можно
-- определить, истинно оно или ложно. Это различие имеет смысл только в конструктивной
-- логике. В классической логике любое высказывание считается разрешимым.

-- Однако если воспользоваться классическим принципом, например, при определении функции
-- по кейсам, то такая функция уже не будет вычислимой. С алгоритмической точки зрения
-- класс типов [Decidable] позволяет вывести процедуру, которая эффективно определяет,
-- истинно ли данное высказывание. Таким образом, этот класс типов поддерживает
-- вычислимые определения, когда это возможно, и при этом обеспечивает плавный переход к
-- использованию классических определений и рассуждений.

namespace My8

class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h :  p) : Decidable p

-- ite - if then else
-- if (Decidable c) then t else f
def ite
    {α : Sort u}
    (c : Prop) [h : Decidable c]
    (t f : α) : α :=
  h.casesOn
    (motive := fun _c => α) -- Decidable c -- condition
    (fun _hnc => f) -- ветка true
    (fun _hc => t)  -- ветка false

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

-- Класс типов Decidable также предоставляет небольшую автоматизацию для
-- доказательства теорем. В стандартной библиотеке есть
-- тактика decide, которая использует экземпляр Decidable, чтобы решать
-- простые цели, а также функция decide, которая использует
-- экземпляр Decidable для вычисления соответствующего значения типа Bool.

-- Тактика decide пытается доказать основную цель (типa p),
-- синтезируя инстанс Decidable p, а затем сводя этот
-- инстанс к вычислению "истинности" p (редукцией до
-- конструкторов Decidable: isTrue | isFalse). Если при вычислении
-- получается значение (isTrue  (h :  p) : Decidable p),
-- то h является доказательством p, которое завершает цель (закрывает её).

-- Цель не должна содержать локальных переменных или метапеременных.
-- Если в цели есть локальные переменные, можно сначала попробовать
-- использовать тактику revert с этими переменными, чтобы переместить
-- их в цель, или воспользоваться опцией +revert, описанной ниже.

example : 10 < 5 ∨ 1 > 0 := by decide
example : ¬(True ∧ False) := by decide
example : 10 * 20 = 200 := by decide

theorem ex : True ∧ 2 = 1 + 1 := by decide

-- Вот так можно посмотреть от каких аксиом зависит конкретная теорема:
#print axioms ex

end My9

-- TODO: Вернуться позже и доботать
--  10.9. Managing Type Class Inference
-- 10.10. Coercions using Type Classes🔗
