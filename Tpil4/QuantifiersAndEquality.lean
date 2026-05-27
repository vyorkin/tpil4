-- глава 4: кванторы и равенство
-- "theorem proving in lean 4", chapter 4: quantifiers and equality
--
-- основные темы:
--   ∀ как зависимая функция (Π-тип)
--   Eq и его свойства: refl, symm, trans
--   подстановка через Eq.subst и оператор ▸
--   конгруэнтность: congrArg, congrFun, congr
--   calc-блоки: синтаксис цепочек равенств и неравенств
--   ∃ как зависимая пара (Σ-тип на уровне Prop)
--   разрушение экзистенциальных высказываний
--   инструменты языка доказательств: have, show, ‹...›

namespace UniversalQuantifier
  -- ∀ x : α, p x — это тип зависимой функции (x : α) → p x
  -- в теории типов это "Π-тип" (pi-type, зависимое произведение)
  --
  -- доказательство ∀ x : α, p x — это функция, которая по любому x : α
  -- возвращает доказательство p x
  -- лямбда-абстракция λ x => ... строит именно такую функцию
  --
  -- важный момент: переменная под квантором может называться как угодно —
  -- ∀ x : α, p x и ∀ y : α, p y и ∀ z : α, p z — один и тот же тип
  -- это хорошо видно в первых двух примерах ниже: в первом y, во втором z,
  -- оба дают одно и то же

  example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
      -- h : ∀ x, p x ∧ q x  — функция, дающая пару для каждого x
      -- применяем h к y: h y : p y ∧ q y
      -- берём левую компоненту .left : p y
      λ h : ∀ x : α, p x ∧ q x =>
      λ y : α =>
      show p y from (h y).left

  example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
      -- то же самое, другая запись: And.left вместо .left
      -- переменная под внешним ∀ названа z — и это нормально,
      -- тип всё равно (x : α) → p x
      λ h : ∀ x : α, p x ∧ q x =>
      λ z : α =>
      show p z from And.left (h z)

  namespace Transitivity
    variable (α : Type) (r : α → α → Prop)
    -- trans_r — явные аргументы: ∀ x y z, r x y → r y z → r x z
    -- чтобы применить trans_r, нужно передать x, y, z явно,
    -- даже если они очевидны из контекста
    variable (trans_r : ∀ x y z, r x y → r y z → r x z)

    variable (a b c : α)
    variable (h_ab : r a b) (h_bc : r b c)

    -- #check trans_r            : ∀ (x y z : α), r x y → r y z → r x z
    -- #check trans_r a b c      : r a b → r b c → r a c  (три аргумента поданы)
    -- #check trans_r a b c h_ab : r b c → r a c          (четыре аргумента)
    -- #check trans_r a b c h_ab h_bc : r a c              (полное применение)
    #check trans_r
    #check trans_r a b c
    #check trans_r a b c h_ab
    #check trans_r a b c h_ab h_bc
  end Transitivity

  namespace TransitivityImplicitArgs
    variable (α : Type) (r : α → α → Prop)
    -- trans_r с неявными аргументами {x y z}: они выводятся из типов h₁ и h₂
    -- {x y z} означает, что Lean сам подставит нужные значения по унификации:
    -- если h₁ : r a b, то из типа h₁ Lean вывел x = a, y = b;
    -- если h₂ : r b c, то из типа h₂ Lean вывел y = b, z = c
    -- именно поэтому достаточно просто написать trans_r h_ab h_bc
    -- без явного указания точек a, b, c
    variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

    variable (a b c : α)
    variable (h_ab : r a b) (h_bc : r b c)

    -- #check trans_r        : r ?x ?y → r ?y ?z → r ?x ?z
    -- #check trans_r h_ab   : r b c → r a c   (x=a, y=b выведены из h_ab)
    -- #check trans_r h_ab h_bc : r a c         (z=c выведен из h_bc)
    #check trans_r
    #check trans_r h_ab
    #check trans_r h_ab h_bc
  end TransitivityImplicitArgs

  namespace Reasoning
    variable (α : Type) (r : α → α → Prop)
    variable (refl_r : ∀ x, r x x)
    variable (symm_r : ∀ {x y}, r x y → r y x)
    variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

    -- доказываем r a d из: r a b, r c b, r c d
    -- стратегия:
    --   1. symm_r h_cb : r b c   (перевернули r c b)
    --   2. trans_r h_ab (symm_r h_cb) : r a c
    --   3. trans_r (шаг 2) h_cd : r a d
    -- неявные аргументы {x y z} выводятся автоматически на каждом шаге
    example (a b c d : α)
      (h_ab : r a b) (h_cb : r c b) (h_cd : r c d) : r a d :=
      trans_r (trans_r h_ab (symm_r h_cb)) h_cd
  end Reasoning

end UniversalQuantifier

namespace Equality
  -- Равенство это отношение эквивалентности,
  -- т.е. оно рефлексивно, симметрично и транзитивно.
  #check Eq.refl
  #check Eq.symm
  #check Eq.trans

  universe u
  #check @Eq.refl.{u}
  #check @Eq.symm.{u}
  #check @Eq.trans.{u}

  variable (α : Type) (a b c d : α)
  variable (h_ab : a = b) (h_cb : c = b) (h_cd : c = d)

  -- строим цепочку: a = b, c = b → b = c, b = c → c = d, итого a = d
  example : a = d :=
    Eq.trans (Eq.trans h_ab (Eq.symm h_cb)) h_cd

  -- projection notation
  -- то же самое, но через "точечный" синтаксис
  -- h_ab.trans — сахар для Eq.trans h_ab
  -- h_cb.symm  — сахар для Eq.symm h_cb
  example : a = d := (h_ab.trans h_cb.symm).trans h_cd

  namespace PowerOfReflexivity
    -- Eq.refl a : a = a — рефлексивность
    --
    -- ключевое свойство: Lean проверяет равенство по определению (definitional equality)
    -- два термa дефиниционно равны, если они редуцируются к одному нормальному виду
    -- бета-редукция: (λ x => f x) a ~~> f a  (подставляем a вместо x)
    --
    -- поэтому (λ x => f x) a и f a — это один и тот же терм по бета-редукции,
    -- и Eq.refl (f a) имеет тип (λ x => f x) a = f a
    -- нам не нужно ничего доказывать: Lean видит равенство сам
    variable (α β : Type)

    example (f : α → β) (a : α) : (λ x => f x) a = f a := Eq.refl (f a)
    -- _ означает "выведи сам" — Lean знает что нужен f a
    example (f : α → β) (a : α) : (λ x => f x) a = f a := Eq.refl _
    -- rfl — сокращение для Eq.refl _
    example (f : α → β) (a : α) : (λ x => f x) a = f a := rfl

    -- аналогично для проекции пары: (a, b).1 редуцируется к a по дельта-редукции
    example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
    example (a : α) (b : β) : (a, b).1 = a := rfl

    -- 2 + 3 вычисляется в 5 на этапе проверки типов (натуральные числа в Lean
    -- определены индуктивно, сложение — рекурсивно, результат вычисляется)
    example : 2 + 3 = 5 := Eq.refl _
    example : 2 + 3 = 5 := rfl

  end PowerOfReflexivity

  namespace Substitution
    variable (α : Type)

    -- Eq.subst : a = b → p a → p b
    -- если a = b и мы знаем p a, то получаем p b
    -- логика: подставляем b вместо a в предикат p
    -- это аналог правила substitution в математике:
    -- "если a = b, можно заменить a на b в любом контексте"
    --
    -- технически: Eq.subst использует J-элиминатор (рекурсор для Eq),
    -- который говорит: достаточно рассмотреть случай h1 : a = a (rfl),
    -- тогда p a и p b совпадают, и доказательство просто переносится
    example (α : Type) (a b : α) (p : α → Prop)
      (h1 : a = b) (h2 : p a) : p b := Eq.subst h1 h2

    -- оператор ▸ (треугольник, вводится \t или \triang) — синтаксический сахар
    -- h1 ▸ h2  означает Eq.subst h1 h2
    -- это "переписывание" (rewrite) в терм-режиме:
    -- h1 : a = b,  h2 : p a  →  результат : p b
    -- ▸ читается как "подставь" или "перепиши"
    example (α : Type) (a b : α) (p : α → Prop)
      (h1 : a = b) (h2 : p a) : p b := h1 ▸ h2

  end Substitution

  namespace Congr
    variable (α : Type)
    variable (a b : α)
    variable (f g : α → Nat)

    variable (h₁ : a = b)
    variable (h₂ : f = g)

    -- Позволяет заменить аргумент ф-ции.
    -- congrArg f h₁ : f a = f b
    -- правило: если a = b, то f a = f b для любой функции f
    -- это "подстановка под функцию": меняем аргумент, функция та же
    example : f a = f b := congrArg f h₁
    -- Позволяет сделать замену функции на другую ей равную.
    -- congrFun h₂ a : f a = g a
    -- правило: если f = g, то f a = g a для любого аргумента a
    -- это "подстановка функции": меняем функцию, аргумент тот же
    example : f a = g a := congrFun h₂ a

    -- congr h₂ h₁ : f a = g b
    -- правило: если f = g и a = b, то f a = g b
    -- это "двойная" конгруэнтность: меняем и функцию, и аргумент одновременно
    -- congr — наиболее мощный из трёх, включает оба предыдущих как частные случаи
    example : f a = g b := congr h₂ h₁
  end Congr

  -- базовые леммы арифметики натуральных чисел из библиотеки Lean
  -- они полезны при построении доказательств через calc и rw
  variable (a b c : Nat)

  example : a + 0 = a := Nat.add_zero a
  example : 0 + a = a := Nat.zero_add a
  example : a * 1 = a := Nat.mul_one a
  example : 1 * a = a := Nat.one_mul a
  example : a + b = b + a := Nat.add_comm a b
  example : (a + b) + c = a + (b + c) := Nat.add_assoc a b c
  example : a * b = b * a := Nat.mul_comm a b
  example : (a * b) * c = a * (b * c) := Nat.mul_assoc a b c

  example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
  example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c

  example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
  example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c

  -- пример более сложного доказательства через have и ▸
  -- раскрываем (x+y)² = x²+yx+xy+y² без calc и без тактик
  --
  -- h₁: (x+y)*(x+y) = (x+y)*x + (x+y)*y   — дистрибутивность справа
  -- h₂: разворачиваем (x+y)*x и (x+y)*y через Nat.add_mul и ▸
  --     Nat.add_mul x y x : (x+y)*x = x*x + y*x
  --     применяем ▸ к h₁: подставляем (x+y)*x → x*x + y*x
  --     затем раскрываем (x+y)*y → x*y + y*y аналогично
  -- итог: транзитивность h₂ с обратной ассоциативностью даёт нужный результат
  example (x y : Nat) :
    (x + y) * (x + y) =
    x * x + y * x + x * y + y * y :=
    have h₁ : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
      Nat.mul_add (x + y) x y
    have h₂ : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
      (Nat.add_mul x y x) ▸ ((Nat.add_mul x y y) ▸ h₁)
    h₂.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

end Equality

namespace CalculationalProofs
  -- calc-блок — синтаксический сахар над цепочкой транзитивных шагов
  -- каждый шаг имеет форму: <lhs> <rel> <rhs> := <доказательство шага>
  -- следующий шаг должен начинаться с той же rhs (или с _)
  -- lean соединяет шаги через Trans: если r₁ a b и r₂ b c, то r₃ a c
  -- для одного отношения это Trans.trans; для Eq и ≤ уже есть инстансы
  --
  -- calc не просто "красота" — он разбивает длинное доказательство на
  -- маленькие шаги, каждый из которых проверяется независимо
  variable (a b c d e : Nat)

  -- T₀: полная запись без "_" — каждый шаг явно называет левую часть
  -- это более многословно, но нагляднее показывает каждый переход
  theorem T₀
    (h₁ : a = b)
    (h₂ : b = c + 1)
    (h₃ : c = d)
    (h₄ : e = 1 + d) :
    a = e :=
  calc
    a = b     := h₁
    b = c + 1 := h₂
    c + 1 = d + 1 := congrArg Nat.succ h₃
    d + 1 = 1 + d := Nat.add_comm d 1
    1 + d = e     := Eq.symm h₄

  -- T₁: запись с "_" (underscore) — более чистый стиль
  -- _ обозначает "правую часть предыдущего шага"
  -- именно так обычно пишут calc-блоки в lean 4
  theorem T₁
    (h₁ : a = b)
    (h₂ : b = c + 1)
    (h₃ : c = d)
    (h₄ : e = 1 + d) :
    a = e :=
  calc
    a = b     := h₁
    _ = c + 1 := h₂
    _ = d + 1 := congrArg Nat.succ h₃
    _ = 1 + d := Nat.add_comm d 1
    _ = e     := Eq.symm h₄

  -- T₂: часть шагов делается тактикой rw
  -- rw (rewrite) переписывает цель, применяя равенства слева направо
  -- rw [h₁, h₂, h₃] последовательно подставляет h₁, затем h₂, затем h₃
  -- это позволяет объединить несколько шагов в один
  theorem T₂
    (h₁ : a = b)
    (h₂ : b = c + 1)
    (h₃ : c = d)
    (h₄ : e = 1 + d) :
    a = e :=
  calc
    a = d + 1 := by rw [h₁, h₂, h₃]
    _ = 1 + d := by rw [Nat.add_comm]
    _ = e     := by rw [h₄]

  -- T₃: вместо calc используется одна тактика rw со всеми леммами сразу
  -- rw применяет подстановки последовательно: сначала h₁, потом h₂, ...
  -- каждая подстановка делается в текущей цели
  theorem T₃
    (h₁ : a = b)
    (h₂ : b = c + 1)
    (h₃ : c = d)
    (h₄ : e = 1 + d) :
    a = e := by
  rw [h₁, h₂, h₃, Nat.add_comm, h₄]

  -- T₄: тактика simp — более мощная, применяет леммы как правила переписывания
  -- в отличие от rw, simp пробует применять леммы многократно, в любом порядке,
  -- под подвыражениями, пока не застрянет
  -- simp может доказывать то, что rw не может (нелинейные паттерны, нормализация)
  theorem T₄
    (h₁ : a = b)
    (h₂ : b = c + 1)
    (h₃ : c = d)
    (h₄ : e = 1 + d) :
    a = e := by
  simp [h₁, h₂, h₃, Nat.add_comm, h₄]

  -- Можно комбинировать разные отношения.
  -- calc умеет работать с разными транзитивными отношениями одновременно:
  -- здесь используются = (равенство) и < (строгий порядок) и ≤ (нестрогий)
  -- lean ищет подходящий инстанс Trans для каждой пары отношений
  -- например: Trans (· = ·) (· < ·) (· < ·) уже есть в библиотеке
  example (h₁ : a = b) (h₂ : b ≤ c) (h₃ : c + 1 < d) : a < d :=
    calc
      a = b := h₁
      b < b + 1 := Nat.lt_succ_self b
      b + 1 ≤ c + 1 := Nat.succ_le_succ h₂
      c + 1 < d := h₃

  -- Можно определять свои транзитивные отношения и
  -- сообщать Lean как с ними работать, реализуя класс типов Trans.

  -- divides x y : "x делит y", то есть существует k такое, что k * x = y
  def divides (x y : Nat) : Prop :=
    ∃ k, k * x = y

  -- divides_trans: транзитивность делимости
  -- если x | y и y | z, то x | z
  -- доказательство: k₁ * x = y, k₂ * y = z, тогда (k₁ * k₂) * x = z
  -- let ⟨k₁, d₁⟩ := h₁  — деструктурируем экзистенциальное h₁ : ∃ k, k * x = y
  -- затем аналогично h₂
  -- результат: ⟨k₁ * k₂, ...⟩ — конструируем новое экзистенциальное
  def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
    let ⟨k₁, d₁⟩ := h₁
    let ⟨k₂, d₂⟩ := h₂
    ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

  -- x | k*x для любого k — базовый факт делимости
  -- свидетель: k, и k * x = k * x верно по rfl
  def divides_mul (x : Nat) (k : Nat) : divides x (k * x) :=
    ⟨k, rfl⟩

  -- регистрируем экземпляр класса типов Trans для нашего отношения divides
  -- Trans r₁ r₂ r₃ означает: если r₁ a b и r₂ b c, то r₃ a c
  -- здесь все три отношения — divides, и trans := divides_trans
  -- именно этот инстанс позволяет calc соединять шаги divides с шагами =
  -- Lean проверяет инстанс автоматически при обработке каждого шага calc
  instance : Trans divides divides divides where
    trans := divides_trans

  -- calc с кастомным отношением divides
  -- шаг "divides x y := h₁" работает потому что divides — это Prop,
  -- и мы подаём доказательство h₁ : divides x y
  -- шаг "y = z := h₂" — обычное равенство
  -- lean использует Trans (divides) (Eq) (divides) из библиотеки для перехода
  example (h₁ : divides x y) (h₂ : y = z) : divides x (2 * z) :=
    calc
      divides x y := h₁
      y = z       := h₂
      divides z (2 * z) := divides_mul ..

  -- infix нотация: x | y вместо divides x y
  -- infix:50 — приоритет оператора (50 — средний)
  infix:50 " | " => divides

  -- тот же calc, но с инфиксной нотацией | для читаемости
  example (h₁ : x | y) (h₂ : y = z) : x | (2 * z) :=
    calc
      x | y       := h₁
      y = z       := h₂
      z | (2 * z) := divides_mul ..

end CalculationalProofs

-- примеры calc для раскрытия (x+y)² вне любого namespace
-- показывают разные стили записи calc в lean 4

-- стиль 1: явные левые части в каждом шаге
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
      by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y :=
      by rw [← Nat.add_assoc]

-- стиль 2: первый шаг с явным термом, остальные через _
-- "calc (x + y) * (x + y)" + "_ = ... := ..." — альтернативный синтаксис lean 4
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y :=
      by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y :=
      by rw [← Nat.add_assoc]

-- Тактика rw позволяет сделать эти "переписывания" в указанном порядке.
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y := by
  rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ← Nat.add_assoc]

-- Тактика simp применяет указанные леммы пока применяются (избегая цикличности).
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y := by
  simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]

namespace ExistentialQuantifier
  -- ∃ x : α, p x — это тип зависимой пары (x : α) × p x на уровне Prop
  -- в теории типов это "Σ-тип" (sigma-type), но для утверждений
  -- доказательство ∃ x, p x — это пара ⟨w, h⟩ где:
  --   w : α  — конкретный "свидетель" (witness), элемент α
  --   h : p w — доказательство того, что предикат p выполнен для w
  --
  -- Exists.intro w h — явный конструктор
  -- ⟨w, h⟩ — анонимный конструктор, lean выводит тип автоматически

  -- Exists.intro 1 h: свидетель — 1, доказательство — h : 1 > 0
  example : ∃ x : Nat, x > 0 :=
    have h : 1 > 0 := Nat.zero_lt_succ 0
    Exists.intro 1 h

  -- свидетель — 0, доказательство — h : 0 < x (уже дано)
  example (x : Nat) (h : 0 < x) : ∃ y, y < x :=
    Exists.intro 0 h

  -- Exists.intro y ⟨hxy, hyz⟩ : ∃ w, x < w ∧ w < z
  -- свидетель — y, доказательство — пара hxy ∧ hyz
  example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
    Exists.intro y ⟨hxy, hyz⟩

  #check @Exists.intro

  -- анонимные конструкторы ⟨...⟩ — тот же смысл, короче запись
  example : ∃ x : Nat, x > 0 :=
    have h : 1 > 0 := Nat.zero_lt_succ 0
    ⟨1, h⟩

  example (x : Nat) (h : 0 < x) : ∃ y, y < x :=
    ⟨0, h⟩

  -- ⟨y, hxy, hyz⟩ — lean автоматически оборачивает в And
  -- это эквивалентно ⟨y, ⟨hxy, hyz⟩⟩, но короче
  example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
    ⟨y, hxy, hyz⟩
    -- ⟨y, ⟨hxy, hyz⟩⟩

  section
  variable (g : Nat → Nat → Nat)

  -- четыре варианта экзистенциального с одной и той же гипотезой hg : g 0 0 = 0
  -- каждый раз свидетель — 0, но предикаты разные
  -- gex1: g x x = x при x = 0 даёт g 0 0 = 0 ✓
  -- gex2: g x 0 = x при x = 0 даёт g 0 0 = 0 ✓ (0 фиксирован второй аргумент)
  -- gex3: g 0 0 = x при x = 0 даёт g 0 0 = 0 ✓ (x в rhs)
  -- gex4: g x x = 0 при x = 0 даёт g 0 0 = 0 ✓ (0 в rhs)
  -- все четыре доказываются одинаково: ⟨0, hg⟩
  -- но внутренние представления разные — это видно через #print
  theorem gex1 (hg : g 0 0 = 0) : ∃ x, g x x = x := ⟨0, hg⟩
  theorem gex2 (hg : g 0 0 = 0) : ∃ x, g x 0 = x := ⟨0, hg⟩
  theorem gex3 (hg : g 0 0 = 0) : ∃ x, g 0 0 = x := ⟨0, hg⟩
  theorem gex4 (hg : g 0 0 = 0) : ∃ x, g x x = 0 := ⟨0, hg⟩

  -- Показывать неявные аргументы.
  -- pp.explicit раскрывает всё: убирает синтаксический сахар,
  -- показывает неявные аргументы явно, Universe-переменные и т.д.
  -- полезно чтобы понять что именно lean вывел под капотом
  set_option pp.explicit true

  #print gex1
  #print gex2
  #print gex3
  #print gex4

  end

  section
  variable (α : Type) (p q : α → Prop)

  -- Exists.elim: деструктурирует ∃ x, p x в обработчик
  -- Exists.elim h f : f получает свидетеля и доказательство предиката
  -- сигнатура: Exists.elim : (∃ x, p x) → (∀ w, p w → r) → r
  -- здесь f = λ w => λ hw : p w ∧ q w => ...
  -- w — конкретный x, для которого существование было доказано
  -- hw — доказательство что именно для этого w выполнено p w ∧ q w
  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    Exists.elim h
      (λ w =>
        λ hw : p w ∧ q w =>
          show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)

  -- match для ∃: деструктурирует экзистенциальную пару
  -- ⟨w, hw⟩ := h разбирает h : ∃ x, p x ∧ q x на свидетеля w и доказательство hw
  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    match h with
    | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩

  -- то же самое с явными аннотациями типов в паттерне
  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    match h with
    | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩

  -- двойное деструктурирование: ⟨w, hpw, hqw⟩ разбирает hw на компоненты And
  -- lean понимает что hw : p w ∧ q w, и дополнительно деструктурирует его
  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    match h with
    | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

  -- let-деструктурирование: синтаксически ещё короче чем match
  -- let ⟨w, hpw, hqw⟩ := h работает как однострочный match
  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    let ⟨w, hpw, hqw⟩ := h
    ⟨w, hqw, hpw⟩

  -- деструктурирование прямо в аргументе лямбды
  -- fun ⟨w, hpw, hqw⟩ => ... это лямбда с pattern-matching аргументом
  -- самая компактная форма записи для этого паттерна
  example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
    fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

  end

  -- IsEven a определяется через экзистенциальный квантор:
  -- a чётно, если есть b такое, что a = 2 * b
  def IsEven (a : Nat) := ∃ b, a = 2 * b

  variable (a b : Nat)

  -- even_plus_even: сумма двух чётных чисел чётна
  -- используем Exists.elim дважды — для h₁ и h₂
  -- w₁ : a = 2 * w₁, w₂ : b = 2 * w₂
  -- свидетель для a + b: w₁ + w₂
  -- доказательство: calc
  --   a + b = 2*w₁ + 2*w₂  (подстановка)
  --         = 2*(w₁ + w₂)   (дистрибутивность)
  theorem even_plus_even (h₁ : IsEven a) (h₂ : IsEven b) : IsEven (a + b) :=
    Exists.elim h₁ (λ w₁ (hw₁ : a = 2 * w₁) =>
      Exists.elim h₂ (λ w₂ (hw₂ : b = 2 * w₂) =>
        Exists.intro (w₁ + w₂)
          (calc a + b
            _ = 2 * w₁ + 2 * w₂ := by rw [hw₁, hw₂]
            _ = 2 * (w₁ + w₂)   := by rw [Nat.mul_add]
            )))

  -- то же через match — короче и нагляднее
  theorem even_plus_even₀ (h₁ : IsEven a) (h₂ : IsEven b) : IsEven (a + b) :=
    match h₁, h₂ with
    | ⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩ =>
      ⟨w₁ + w₂, by rw [hw₁, hw₂, Nat.mul_add]⟩

  -- то же через деструктурирование в аргументах лямбды
  theorem even_plus_even₁ : IsEven a → IsEven b → IsEven (a + b) :=
    λ ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ =>
      ⟨w₁ + w₂, by rw [hw₁, hw₂, Nat.mul_add]⟩

  section
  open Classical

  variable (α : Type)
  variable (p : α → Prop)

  -- пример с классической логикой: ¬∀x, ¬p x → ∃x, p x
  -- это отрицание "все x не удовлетворяют p" влечёт "существует x с p x"
  -- доказывается от противного (byContradiction):
  --   допускаем h₁ : ¬∃x, p x
  --   строим h₂ : ∀x, ¬p x (если существование невозможно, все элементы не имеют p)
  --     для любого x: если p x, то ∃x, p x (h₄), но это противоречит h₁
  --   получаем False: h₂ и h вместе дают ¬∀x, ¬p x и ∀x, ¬p x — противоречие
  -- byContradiction : (¬p → False) → p — классический принцип
  -- в конструктивной логике это недоказуемо: нельзя найти свидетеля без информации
  example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
    byContradiction
      (λ h₁ : ¬ ∃ x, p x =>
        have h₂ : ∀ x, ¬ p x :=
          λ x =>
            λ h₃ : p x =>
              have h₄ : ∃ x, p x := ⟨x, h₃⟩
              show False from h₁ h₄
            show False from h h₂)
  end

  -- Упражнения. Надо решить столько, сколько получится.
  -- Всё решать не обязательно, но желательно.

  section
  open Classical

  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  -- Для некоторых нужна классическая логика
  -- с исключённым третим (и мб со снятием двойного отрицания), а
  -- для некоторых классическиая логика не требуется и достаточно конструктивной.
  -- Ты должен понять сам когда она нужна.

  -- ∃ _ : α, r → r: если что-то существует в α и дано r, то r
  -- деструктурируем: _ — свидетель (игнорируем), hx — доказательство r
  example : (∃ _ : α, r) → r :=
    λ ⟨_, hx⟩ => hx

  -- r → ∃ _ : α, r: если дано r, конструируем существование с произвольным a : α
  -- a используется только как свидетель типа α, сам r не зависит от него
  example (a : α) : r → (∃ _ : α, r) :=
    λ h => ⟨a, h⟩

  -- ∃ x, p x ∧ r ↔ (∃ x, p x) ∧ r: r "вытаскивается" из-под квантора
  -- это возможно потому что r не зависит от x
  -- прямо: из ⟨x, h.left, h.right⟩ получаем ⟨⟨x, h.left⟩, h.right⟩
  -- обратно: из ⟨⟨x, h⟩, r⟩ получаем ⟨x, ⟨h, r⟩⟩
  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
    Iff.intro
      (λ ⟨x, h⟩ => ⟨⟨x, h.left⟩, h.right⟩)
      (λ ⟨⟨x, h⟩, r⟩ => ⟨x, ⟨h, r⟩⟩)

  -- ∃ x, p x ∨ q x ↔ (∃ x, p x) ∨ (∃ x, q x)
  -- прямо: смотрим что внутри Or: если p x — кладём в Or.inl, если q x — в Or.inr
  -- обратно: если ∃ x, p x — берём его свидетеля, кладём в Or.inl; аналогично для q
  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    Iff.intro
      (λ ⟨x, h⟩ =>
        Or.elim h
          (λ h_px => Or.inl ⟨x, h_px⟩)
          (λ h_qx => Or.inr ⟨x, h_qx⟩))
      (λ h =>
        Or.elim h
          (λ ⟨x, h_px⟩  => ⟨x, Or.inl h_px⟩)
          (λ ⟨x, h_qx⟩  => ⟨x, Or.inr h_qx⟩))

  -- ∀ x, p x ↔ ¬∃ x, ¬p x
  -- прямо: если ∀x, p x, то для любого x p x истинно,
  --   значит нет такого x с ¬p x, т.е. ¬∃x, ¬p x
  -- обратно: допускаем что для некоторого x ¬p x (byContradiction);
  --   тогда ∃x, ¬p x, но это противоречит h : ¬∃x, ¬p x
  -- обратное требует классической логики (byContradiction)
  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    Iff.intro
      (λ h => λ ⟨x, h_npx⟩ => h_npx (h x))
      (λ h : ¬∃ x, ¬p x =>
        λ x : α => byContradiction
          (λ h_npx : ¬p x =>
            have h₀ : ∃ x, ¬p x := ⟨x, h_npx⟩
            show False from h h₀))

  -- ∃ x, p x ↔ ¬∀ x, ¬p x
  -- прямо: если ∃x, p x, то для любого h : ∀x, ¬p x, берём наш x и получаем
  --   h x : ¬p x и hx : p x — абсурд (absurd hx (h x))
  -- обратно: если ¬∀x, ¬p x, то предполагаем ¬∃x, p x и строим ∀x, ¬p x
  --   но шаг "для любого x построить ¬p x" требует вытащить конкретный x из воздуха —
  --   при условии ¬∃x, p x это можно, но вот как именно: если p x, то ∃x, p x,
  --   что противоречит h₀; значит ¬p x — это корректное рассуждение,
  --   но здесь оставлен sorry — заполнить это место самостоятельно
  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    Iff.intro
      (λ ⟨x, h_px⟩ =>
        λ h : ∀ (x : α), ¬p x => absurd h_px (h x))
      (λ h : ¬∀ (x : α), ¬p x => byContradiction
        (λ h₀ : ¬∃ x, p x =>
          have h_inv : ∀ (x : α), ¬p x :=
            λ x : α => sorry
            -- для доказательства ¬p x нужно:
            --   взять h_px : p x (предположить)
            --   построить h₄ : ∃ x, p x := ⟨x, h_px⟩
            --   применить h₀ h₄ : False
            --   т.е. λ h_px => h₀ ⟨x, h_px⟩

          -- have x : α := sorry
          -- have h_px : p x := sorry
          -- have h₀_inv : ∃ x, p x := ⟨x, h_px⟩
          -- show False from h₀ h₀_inv
          show False from h h_inv))

  -- ¬∃x, p x ↔ ∀x, ¬p x
  -- прямо: h : ¬∃x, p x; надо ∀x, ¬p x; для x берём h_px : p x,
  --   строим ⟨x, h_px⟩ : ∃x, p x, применяем h — получаем False, а значит ¬p x
  --   то есть: λ x => λ h_px => h ⟨x, h_px⟩
  -- обратно: h : ∀x, ¬p x; надо ¬∃x, p x; берём ⟨x, h_px⟩ : ∃x, p x,
  --   применяем h x : ¬p x к h_px : p x — получаем False
  --   то есть: λ ⟨x, h_px⟩ => h x h_px
  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    Iff.intro
      (λ h : ¬∃ x, p x =>
        λ x => sorry)
        -- заполнить: λ h_px => h ⟨x, h_px⟩
      (λ h => sorry)
        -- заполнить: λ ⟨x, h_px⟩ => h x h_px

  -- ¬∀x, p x ↔ ∃x, ¬p x
  -- это "принцип де Моргана" для кванторов
  -- прямо требует классической логики:
  --   если ¬∀x, p x, допускаем ¬∃x, ¬p x
  --   тогда ∀x, ¬¬p x (из отрицания ∃x, ¬p x)
  --   по двойному отрицанию (classical): ∀x, p x
  --   но это противоречит ¬∀x, p x — абсурд
  --   вот конкретные шаги для заполнения sorry:
  --   byContradiction (λ h₀ : ¬∃x, ¬p x =>
  --     have h₂ : ∀x, p x := λ x => byContradiction (λ h₁ : ¬p x => h₀ ⟨x, h₁⟩)
  --     h h₂)
  -- обратно (конструктивно):
  --   h : ∃x, ¬p x; надо ¬∀x, p x; берём ⟨w, hw⟩ из h,
  --   hw : ¬p w; если дано h_all : ∀x, p x, то h_all w : p w, и hw (h_all w) : False
  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

  -- ∀x, p x → r ↔ (∃x, p x) → r
  -- прямо: h : ∀x, p x → r; дано ⟨x, h_px⟩ : ∃x, p x; тогда h x h_px : r
  -- обратно: h : (∃x, p x) → r; дано x : α и h_px : p x; тогда h ⟨x, h_px⟩ : r
  example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry

  -- ∃x, p x → r ↔ (∀x, p x) → r  (при условии что α непусто, a : α дан)
  -- это нетривиальное утверждение! обратное направление требует классики.
  -- прямо: h : ∃x, p x → r; дано h_all : ∀x, p x
  --   деструктурируем h : ⟨w, hw⟩ где hw : p w → r
  --   hw (h_all w) : r
  -- обратно (классика): h : (∀x, p x) → r
  --   если ∀x, p x — тогда h даёт r, свидетель a : α из переменной
  --   если ¬∀x, p x — тогда ∃x, ¬p x; берём этот x; p x → r доказывается
  --     потому что p x ложно: из p x следует ∀x, p x (ну не совсем, но почти) — sorry
  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry

  -- ∃x, r → p x ↔ r → ∃x, p x  (при условии что α непусто, a : α дан)
  -- прямо: h : ∃x, r → p x; дано ev_r : r
  --   деструктурируем h : ⟨w, hw⟩ где hw : r → p w
  --   ⟨w, hw ev_r⟩ : ∃x, p x
  -- обратно (классика): h : r → ∃x, p x
  --   если r — тогда h ev_r : ∃x, p x; деструктурируем ⟨w, hw⟩; свидетель w, функция λ _ => hw
  --   если ¬r — тогда для любого x функция (λ _ : r => absurd · ‹¬r›) даёт r → p x
  --             и берём a как свидетеля: ⟨a, λ h_r => absurd h_r ‹¬r›⟩
  --   итого: Or.elim (Classical.em r) (λ ev_r => ...) (λ hn_r => ⟨a, λ h_r => absurd h_r hn_r⟩)
  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry

  end

end ExistentialQuantifier

namespace ProofLanguage
  -- have, show, ‹...› — инструменты языка доказательств lean 4
  --
  -- have name : type := proof  — вводит промежуточный факт в контекст
  -- show type from proof — явно указывает цель (для читаемости)
  -- ‹type› (французские кавычки "ёлочки", вводятся \f< и \f>) —
  --   ищет доказательство type в текущем контексте; эквивалентно assumption/‹type›
  variable (f : Nat → Nat)
  variable (h : ∀ x : Nat, f x ≤ f (x + 1))

  -- строим f 0 ≤ f 3 через цепочку have
  -- have : f 0 ≤ f 1 := h 0     — применяем h к 0
  -- have : f 0 ≤ f 2 := ...     — используем предыдущее have через "this"
  -- "this" — специальное имя последнего анонимного have
  example : f 0 ≤ f 3 :=
    have : f 0 ≤ f 1 := h 0
    have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
    show f 0 ≤ f 3 from Nat.le_trans this (h 2)

  -- то же, но "this" заменён на "by assumption"
  -- "by assumption" — тактика, ищет нужное в контексте (аналог ‹...›)
  example : f 0 ≤ f 3 :=
    have : f 0 ≤ f 1 := h 0
    have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
    show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)

  -- пример с ‹...›: французские кавычки (guillemets)
  -- ‹f 1 ≥ f 2› ищет в контексте гипотезу с типом f 1 ≥ f 2 и возвращает её
  -- это отличается от именованного h : type тем, что:
  --   1. ‹type› работает с анонимными гипотезами (лямбда-аргументы без имён)
  --   2. ‹type› работает везде где есть нужный тип в контексте
  --   3. удобно когда имя гипотезы не важно — важен только её тип
  example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
    λ _ : f 0 ≥ f 1 =>
    λ _ : f 1 ≥ f 2 =>
    -- have : f 0 ≥ f 2 := Nat.le_trans (by assumption) (by assumption)
    have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
    have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
    show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›

  -- Можно использовать эта мягкие французские ковычки, чтобы
  -- ссылаться вообще на что угодно из контекста, a не только на анонимные штуки.

  -- Так же их необязательно использовать только для высказываний.
  -- Для других вселенных это тоже работает, но может выглядеть как какая-то дичь.
  -- n : Nat есть в контексте, ‹Nat› находит его и возвращает
  example (n : Nat) : Nat := ‹Nat›

end ProofLanguage

namespace Exercises_1
  variable (α : Type) (p q : α → Prop)

  -- ∀x, p x ∧ q x ↔ (∀x, p x) ∧ (∀x, q x)
  -- прямо: из h : ∀x, p x ∧ q x строим пару функций
  --   λx => (h x).left и λx => (h x).right
  -- обратно: из пары (h_p, h_q) строим λx => ⟨h_p x, h_q x⟩
  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    Iff.intro
      (λ h : ∀ (x : α), p x ∧ q x =>
        ⟨λ x => (h x).left, λ x => (h x).right⟩)
      (λ h : (∀ (x : α), p x) ∧ ∀ (x : α), q x =>
        λ x => ⟨h.left x, h.right x⟩ )

  -- "modus ponens" под квантором:
  -- если для всех x из p x следует q x, и для всех x p x, то для всех x q x
  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    λ h₁ : ∀ (x : α), p x → q x =>
    λ h₂ : ∀ x, p x =>
    λ x => h₁ x (h₂ x)

  -- В этом упражнении постарайся понять почему обратное недоказуемо.
  -- (∀x, p x) ∨ (∀x, q x) → ∀x, p x ∨ q x
  -- прямо: если "все x имеют p" ИЛИ "все x имеют q",
  --   то для любого конкретного x выполнено p x ∨ q x — тривиально
  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
    λ h => Or.elim h
      (λ h₀ : ∀ x, p x => λ x => Or.inl (h₀ x))
      (λ h₁ : ∀ x, q x => λ x => Or.inr (h₁ x))

  -- Потому что из разных иксов ты можешь выбрать какой-то один.
  -- А наборот хуй там плавал.
  -- обратное ∀x, p x ∨ q x → (∀x, p x) ∨ (∀x, q x) НЕ доказуемо в общем случае:
  -- контрпример: α = {0, 1}, p 0 = True, p 1 = False, q 0 = False, q 1 = True
  -- тогда ∀x, p x ∨ q x истинно, но ∀x, p x ложно и ∀x, q x ложно
  -- проблема: для каждого x мы выбираем разную дизъюнкцию, и нет одного x
  -- из которого можно было бы распространить p или q на все остальные
  -- sorry здесь неустранимо без дополнительных допущений об α или p, q
  example : ∀ x, p x ∨ q x → (∀ x, p x) ∨ (∀ x, q x) :=
    λ x h =>
      Or.elim h
        (λ h_px : p x => Or.inl (λ _ => sorry /-h_px-/ ))
        (λ h_qx : q x => sorry)

end Exercises_1

namespace Exercises_2
  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  -- α → ((∀x : α, r) ↔ r)
  -- если дан x : α, то "∀x : α, r ↔ r"
  -- прямо: h : ∀x : α, r; применяем к конкретному x
  -- обратно: ev_r : r; для любого _ : α возвращаем ev_r
  -- x используется только в прямом направлении как свидетель для "h x"
  -- если бы α было пустым типом, прямое направление не работало бы —
  -- именно поэтому x : α нужен в условии
  example : α → ((∀ x : α, r) ↔ r) :=
    λ x =>
      Iff.intro
        (λ h => h x)
        (λ r => λ _ => r)

  open Classical

  -- Одно из направлений требует классической логики.
  -- (∀x, p x ∨ r) ↔ (∀x, p x) ∨ r
  -- обратное (справа налево): тривиально
  --   если ∀x, p x — для любого x берём Or.inl (h₀ x)
  --   если r — для любого x берём Or.inr ev_r
  -- прямое (слева направо): нетривиально и требует классики
  --   h : ∀x, p x ∨ r; надо (∀x, p x) ∨ r
  --   если r истинно (Classical.em r) — сразу Or.inr r
  --   если r ложно — тогда для каждого x в h x : p x ∨ r только p x возможно
  --   значит ∀x, p x — берём Or.inl
  --   без классики мы не знаем заранее истинно ли r, поэтому надо byContradiction
  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
    Iff.intro
      (λ h : ∀ x, p x ∨ r =>
        Or.inl (λ x =>
          -- absurd byContradiction?: r ∧ ¬ r ?
          -- absurd byContradiction?: p x ∧ ¬ p x ?
          byContradiction
            (λ h_npx : ¬ p x =>
              have h_px : p x := Or.elim (h x) id
                (λ ev_r : r => sorry /-нужен абсурд, тут его не будет-/)
              h_npx h_px)))
      (λ h : (∀ x, p x) ∨ r =>
        Or.elim h
          (λ h₀ : (∀ x, p x) =>
            λ x => Or.elim h
              (λ h_px : ∀ x, p x => Or.inl (h_px x))
              (λ ev_r : r => Or.inr ev_r))
          (λ ev_r : r => λ x => Or.inr ev_r))

  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
    Iff.intro
      (λ h : ∀ x, p x ∨ r =>
        Or.inl (λ x =>
          byContradiction (λ h_npx : ¬ p x =>
            -- бля опять начал делать то же самое,
            -- туду: вернуться сюда позже
            sorry
          )))
      (λ h : (∀ x, p x) ∨ r =>
        sorry)

  -- ∀x, r → p x ↔ r → ∀x, p x
  -- прямо: h : ∀x, r → p x; дано ev_r : r; для x берём (h x) ev_r : p x
  -- обратно: h : r → ∀x, p x; дано x и ev_r : r; h ev_r : ∀x, p x; (h ev_r) x : p x
  -- оба направления конструктивны, классика не нужна
  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    Iff.intro
      (λ h => λ ev_r : r => λ x => (h x) ev_r)
      (λ h => λ x => (λ ev_r : r => (h ev_r) x))

end Exercises_2

namespace Exercises_3
  -- Парадокс брадобрея (одна из интерпретаций парадокса Рассела)
  --
  -- постановка: есть тип men (мужчины) и отношение shaves x y
  -- ("x бреет y"). Брадобрей — конкретный элемент barber : men.
  -- условие: брадобрей бреет ровно тех, кто не бреется сам.
  -- формально: ∀x : men, shaves barber x ↔ ¬ shaves x x
  --
  -- парадокс: применяем это условие к самому брадобрею:
  --   shaves barber barber ↔ ¬ shaves barber barber
  -- это противоречие! если он бреет себя — не бреет; если не бреет — бреет.
  -- в логике из этого сразу следует False.
  --
  -- связь с парадоксом Рассела: рассмотрим множество S = {x | x ∉ x}
  -- тогда S ∈ S ↔ S ∉ S — то же самое противоречие
  -- в lean это невозможно на уровне типов благодаря иерархии вселенных,
  -- но на уровне Prop через ∀/∃ парадокс всё равно ведёт к False

  variable (men : Type) (barber : men)
  variable (shaves : men → men → Prop)

  open Classical

  -- h_b:     shaves barber barber → (shaves barber barber → False)
  -- h_b_inv: (shaves barber barber → shaves barber barber) → False
  -- как завершить доказательство:
  --   h_self := h barber : shaves barber barber ↔ ¬ shaves barber barber
  --   применяем Iff.elim и получаем два направления
  --   h_b : shaves barber barber → ¬ shaves barber barber
  --   h_b_inv : ¬ shaves barber barber → shaves barber barber
  --   теперь: если shaves barber barber (назовём p), то h_b p : ¬p, т.е. h_b p p : False
  --           если ¬ shaves barber barber (назовём np), то h_b_inv np : p, тогда np (h_b_inv np) : False
  --   для sorry нужно: h_b (h_b_inv (λ p => h_b p p)) (h_b_inv (λ p => h_b p p)) : False
  --   или компактнее через absurd и Classical.em
  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
    have h_self := h barber
    Iff.elim
      (λ h_b : shaves barber barber → ¬shaves barber barber =>
        λ h_b_inv : ¬shaves barber barber → shaves barber barber =>
          sorry)
          -- заполнить:
          -- have hn : ¬ shaves barber barber := λ p => h_b p p
          -- exact hn (h_b_inv hn)
      h_self

  -- туду: венуться сюда позже

end Exercises_3

namespace Exercises_4
  -- упражнение 4: формализация математических высказываний в lean
  -- все определения здесь — это просто Prop-формулировки, без доказательств
  -- они иллюстрируют как переводить математику в язык зависимых типов

  -- even n: n чётно, если существует k такое, что n = 2 * k
  def even (n : Nat) : Prop :=
    ∃ k, n = 2 * k

  -- prime n: определение простого числа (упрощённое для целей упражнения)
  -- n = 1 (единица считается простой в этом упрощении) или
  -- нет натурального числа, на которое делится n
  -- замечание: стандартное определение простого более сложно
  -- (n > 1 и нет нетривиальных делителей), но здесь оно упрощено
  def prime (n : Nat) : Prop :=
    n = 1 ∨ ¬ ∃ x, x | n

  -- infinitely_many_primes: бесконечность простых чисел
  -- для любого n существует простое m > n
  -- эта теорема доказана Евклидом, в mathlib она есть как Nat.infinite_setOf_prime
  def infinitely_many_primes : Prop :=
    ∀ n : Nat, ∃ m, m > n ∧ prime m

  -- If 2*k+1 is prime and k > 0, then k itself must be a power of 2,
  -- so 2*k+1 is a Fermat number; such primes are called Fermat primes.
  -- https://mathworld.wolfram.com/FermatPrime.html
  --
  -- F_k = pow(2, pow(2, k)) + 1

  -- Fermat_prime n: число Ферма — число вида 2^(2^k) + 1
  -- известные числа Ферма: F₀=3, F₁=5, F₂=17, F₃=257, F₄=65537
  -- все остальные Fn при n ≥ 5 оказались составными
  -- вопрос о бесконечности простых чисел Ферма открыт
  -- замечание: формулировка ниже содержит ошибку — конъюнкция
  -- должна быть внутри квантора, а предикат k < 5 ∨ k > 32 подозрителен
  -- это упрощение для учебных целей, не математически точное определение
  def Fermat_prime (n : Nat) : Prop :=
    n > 1 ∧ ∀ (k : Nat), (k < 5 ∨ k > 32) ∧ n = 2^(2^k) + 1

  -- infinitely_many_Fermat_primes: бесконечность простых чисел Ферма
  -- открытая проблема: неизвестно, бесконечно ли их число или нет
  -- доказательство с sorry здесь не случайно — математика ещё не знает ответа
  def infinitely_many_Fermat_primes : Prop :=
    ∀ n : Nat, ∃ m, m > n ∧ Fermat_prime m

  -- Every even natural number greater than 2 is
  -- the sum of two prime numbers.

  -- goldbach_conjecture: гипотеза Гольдбаха (1742)
  -- каждое чётное число > 2 является суммой двух простых
  -- одна из старейших нерешённых проблем теории чисел
  -- проверена компьютером до n ≈ 4 × 10^18, но не доказана
  -- замечание: формулировка ниже неточна — ∀ p₁ p₂ говорит
  -- "для всех пар" вместо "существует пара"; правильно: ∃ p₁ p₂, prime p₁ ∧ prime p₂ ∧ n = p₁ + p₂
  def goldbach_conjecture : Prop :=
    ∀ n : Nat, n > 2 → ∀ p₁ p₂ : Nat, p₁ ≠ p₂ → n = p₁ + p₂

  -- Goldbach's weak conjecture states that
  -- every odd number greater than 5 is the sum of three primes.

  -- Alternative problem statement:
  ---------------------------------

  -- Every odd number greater than 7 can be expressed
  -- as the sum of three odd primes.

  -- This version excludes 7 = 2+2+3, as 7 requires the even prime 2:

  -- Более слабый вариант гипотезы — тернарная проблема Гольдбаха,
  -- согласно которой любое нечётное число, начиная с 7,
  -- можно представить в виде суммы трёх простых чисел,

  -- Goldbach's_weak_conjecture: слабая гипотеза Гольдбаха
  -- доказана Харальдом Хелфготтом в 2013 году
  -- формулировка: каждое нечётное число > 5 есть сумма трёх простых
  -- замечание: здесь снова ∀ p₁ p₂ p₃ вместо ∃, что логически неверно
  -- для доказательства нужно было бы: ∃ p₁ p₂ p₃, prime p₁ ∧ prime p₂ ∧ prime p₃ ∧ n = p₁ + p₂ + p₃
  def Goldbach's_weak_conjecture : Prop :=
    ∀ n : Nat,
      (¬ even n) ∧ n > 5 →
      ∀ (p₁ p₂ p₃ : Nat), prime p₁ ∧ prime p₂ ∧ prime p₃ →
      n = p₁ + p₂ + p₃

  -- Теорема утверждает, что для любого натурального числа n > 2
  -- уравнение a^n + b^n = c^n не имеет решений в целых
  -- ненулевых числах a, b, c.

  -- Fermat's_last_theorem: великая теорема Ферма
  -- сформулирована Пьером де Ферма в 1637, доказана Эндрю Уайлсом в 1995
  -- доказательство использует эллиптические кривые и модулярные формы —
  -- методы, недоступные во времена Ферма ("поля этой книги мало для него")
  -- в lean формализация доказательства Уайлса пока не завершена полностью
  -- для sorry здесь две причины:
  --   1. доказательство математически очень сложное
  --   2. формулировка ниже технически неточна: →  внутри ¬∃ применяется не так как нужно
  --      правильно: ∀ n > 2, ¬ ∃ (a b c : Nat), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a^n + b^n = c^n
  def Fermat's_last_theorem : Prop :=
    ∀ n : Nat, n > 2 →
      ¬ ∃ (a b c : Nat), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 →
      a^n + b^n = c^n

end Exercises_4
