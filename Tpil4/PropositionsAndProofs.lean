-- глава 3: "propositions and proofs"
-- ============================================================
-- центральная идея: соответствие карри-говарда.
-- в lean 4 утверждения (propositions) — это типы сорта Prop,
-- а доказательства — это термы этих типов.
-- если p : Prop, то "доказать p" означает "построить терм hp : p".
-- theorem и def — одно и то же на уровне ядра: theorem t : p := e
-- означает "определить терм e, имеющий тип p".
-- разница лишь в том, что тела theorem не разворачиваются
-- при проверке соответствия типов (они непрозрачны, opaque),
-- что позволяет избежать замедления при вычислениях.

namespace Basics
  -- раздел показывает, как можно закодировать логику "вручную",
  -- не используя встроенные And/Or/Not, чтобы понять,
  -- что стоит за синтаксическим сахаром.

  #check And
  #check Or
  #check Not

  variable (p q r : Prop)

  #check And p q
  #check Or p q
  #check Not p

  -- Implies — просто псевдоним для стрелки →.
  -- в lean p → q уже является утверждением (типом Prop),
  -- поэтому Implies здесь — только педагогическая обёртка.
  def Implies (p q : Prop) : Prop := p → q

  -- Proof p — тип "доказательств p", то есть сам p.
  -- это обёртка-тождество, показывающая, что "доказательство p"
  -- и "терм типа p" — одно и то же понятие.
  def Proof (p : Prop) := p

  #check Implies (And p q) (Or p q)

  -- axiom: объявляем терм нужного типа без доказательства.
  -- аксиомы расширяют логику; если добавить противоречивую аксиому,
  -- вся система становится несостоятельной (можно доказать False).
  axiom and_commut (p q : Prop) :
    Proof (Implies (And p q) (And q p))

  #check and_commut p q

  -- modus_ponens: из "если p то q" и "p" следует "q".
  -- в системе карри-говарда это просто применение функции:
  -- если f : p → q и hp : p, то f hp : q.
  -- здесь мы кодируем это через Proof/Implies, чтобы было явно видно.
  axiom modus_ponens (p q : Prop) :
    Proof (Implies p q) → Proof p → Proof q

  -- implies_intro: чтобы доказать "если p то q",
  -- достаточно предъявить функцию, переводящую доказательство p
  -- в доказательство q. это правило введения импликации (→I).
  axiom implies_intro (p q : Prop) :
    (Proof p -> Proof q) -> Proof (Implies p q)
end Basics

-- ============================================================
-- принцип "propositions as types" (пропозиции как типы)
-- ============================================================
-- ключевой переход: больше не нужна обёртка Proof.
-- каждое утверждение p : Prop само по себе является типом,
-- а его элементы hp : p — это доказательства.
-- функции p → q — это ровно доказательства импликации "p → q",
-- потому что чтобы доказать "p → q", нужно предъявить
-- процедуру, превращающую любое доказательство p в доказательство q,
-- а это в точности и есть функция типа p → q.

namespace PropositionsAsTypes
  set_option linter.unusedVariables false

  variable {p : Prop}
  variable {q : Prop}

  -- t1: "из p следует (из q следует p)".
  -- доказательство — двойная λ-абстракция: принимаем hp : p,
  -- затем hq : q, и возвращаем hp.
  -- hq получен, но не используется — допустимо, потому что
  -- нам нужно только вернуть доказательство p, которое уже есть.
  theorem t1 : p → q → p :=
    λ (hp : p) => λ (hq : q) => hp

  #print t1

  -- t2: то же самое, но с явным `show p from hp`.
  -- `show T from e` — синтаксический сахар, который:
  --   1) уточняет ожидаемый тип текущей цели до T (помогает читателю),
  --   2) проверяет, что e : T.
  -- по смыслу эквивалентно просто `hp`, но делает намерение явным.
  theorem t2 : p → q → p :=
    fun hp : p =>
    fun hq : q =>
    show p from hp
    -- ^ which is equivalent to:
    -- (hp : p)

  #print t2

  -- t3: то же, что t1 и t2, но в "tabular" стиле —
  -- аргументы вынесены в сигнатуру теоремы, а тело минимально.
  -- lean принимает все три формы: они равны семантически.
  theorem t3 (hp : p) (hq : q) : p := hp
  #print t3

  -- hp объявлен как аксиома: это глобальный терм типа p.
  -- т.е. мы утверждаем, что p истинно без доказательства.
  -- такой приём используется в примерах, но опасен в реальном коде.
  axiom hp : p
  -- t4 строится частичным применением t3 к hp.
  -- t3 : p → q → p; применяем к hp : p; получаем q → p.
  -- это показывает, что теоремы — это функции первого класса.
  theorem t4 : q -> p := t3 hp

  -- unsound: аксиома False делает систему тривиальной.
  -- из False можно вывести что угодно через False.elim.
  -- это показывает: если принять противоречивую аксиому,
  -- можно "доказать" 1 = 0 или любое другое утверждение.
  axiom unsound : False

  -- False.elim : False → α — правило ex falso quodlibet.
  -- при наличии доказательства False система взрывается:
  -- любой тип обитаем, любое утверждение "доказуемо".
  theorem ex : 1 = 0 := False.elim unsound

  -- t5: явно квантифицирует по {p q : Prop} внутри тела.
  -- фигурные скобки означают неявные (implicit) аргументы —
  -- lean выводит их автоматически из контекста.
  theorem t5 : ∀ {p q : Prop}, p → q → p :=
    fun {p q : Prop} (hp : p) (hq : q) => hp

  variable {α β : Prop}
  -- t6: то же для переменных α β — показывает,
  -- что имена переменных-пропозиций не важны.
  theorem t6 : α → β → α := fun (ha : α) (hb : β) => ha

  -- compose: функциональная композиция для импликаций.
  -- h₁ : q → r, h₂ : p → q; получаем p → r.
  -- это в точности соответствует математическому g ∘ f.
  -- в терминах логики: из "p → q" и "q → r" следует "p → r"
  -- (гипотетический силлогизм / transitivity of →).
  variable {r : Prop}
  theorem compose (h₁ : q → r) (h₂ : p → q) : p → r :=
    λ h₃ : p =>
    -- h₁ (h₂ h₃)
    show r from h₁ (h₂ h₃)

  #print compose

end PropositionsAsTypes

namespace PropositionLogic
  variable (p q : Prop)

  #check p → q → p ∧ q
  #check ¬p → p ↔ False
end PropositionLogic

-- ============================================================
-- конъюнкция (And, ∧)
-- ============================================================
-- And p q — индуктивный тип с одним конструктором:
--   And.intro : p → q → p ∧ q
-- проекции:
--   And.left  : p ∧ q → p
--   And.right : p ∧ q → q
-- в системе карри-говарда And соответствует декартову произведению
-- типов: пара (hp, hq) упакована в один терм.

namespace Conjunction
  variable (p q : Prop)

  -- чтобы доказать p ∧ q, надо предъявить оба компонента.
  -- And.intro — единственный конструктор, принимает hp и hq.
  example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

  #check fun (hp : p) (hq : q) => And.intro hp hq

  -- And.left извлекает первый компонент — аналог fst для пар.
  example (h : p ∧ q) : p := And.left h
  -- And.right извлекает второй компонент — аналог snd для пар.
  example (h : p ∧ q) : q := And.right h

  -- доказательство коммутативности конъюнкции:
  -- разбираем h : p ∧ q на компоненты и собираем в обратном порядке.
  example (h : p ∧ q) : q ∧ p :=
    And.intro (And.right h) (And.left h)

end Conjunction

-- ============================================================
-- синтаксические удобства
-- ============================================================
-- lean предоставляет два удобства:
-- 1) анонимные конструкторы ⟨a, b, ...⟩ — lean сам выводит
--    нужный конструктор из типа цели.
-- 2) dot notation: h.left вместо And.left h,
--    h.right вместо And.right h; работает для любых структур.

namespace SyntacticGadgets
  variable (p q : Prop)
  variable (hp : p) (hq : q)
  -- ⟨hp, hq⟩ воспринимается lean как And.intro hp hq,
  -- потому что цель имеет тип p ∧ q (And p q).
  #check (⟨hp, hq⟩ : p ∧ q)

  variable (xs : List Nat)
  -- dot notation работает и для обычных типов данных.
  #check List.length xs
  #check xs.length

  -- ⟨h.right, h.left⟩ — одновременно используем анонимный
  -- конструктор и dot notation для элегантной записи.
  example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

  -- вложенные конъюнкции: q ∧ p ∧ q разбирается как q ∧ (p ∧ q).
  -- первый способ: явное вложение скобок ⟨h.right, ⟨h.left, h.right⟩⟩.
  example (h : p ∧ q) : q ∧ p ∧ q :=
    ⟨h.right, ⟨h.left, h.right⟩⟩

  -- второй способ: lean сам ставит скобки через flatten-конструктор.
  -- ⟨a, b, c⟩ для p ∧ (q ∧ r) разворачивается в ⟨a, ⟨b, c⟩⟩.
  example (h : p ∧ q) : q ∧ p ∧ q :=
    ⟨h.right, h.left, h.right⟩

end SyntacticGadgets

-- ============================================================
-- дизъюнкция (Or, ∨)
-- ============================================================
-- Or p q — индуктивный тип с двумя конструкторами:
--   Or.inl : p → p ∨ q  (доказали p, значит p ∨ q истинно)
--   Or.inr : q → p ∨ q  (доказали q, значит p ∨ q истинно)
-- устранение (elimination):
--   Or.elim : p ∨ q → (p → r) → (q → r) → r
-- чтобы получить r из p ∨ q, нужно разобрать оба случая.
-- Or соответствует копроизведению (сумме) типов.

namespace Disjunction
  variable (p q r : Prop)

  -- Or.intro_left q hp: доказываем p ∨ q, предъявляя hp : p.
  -- второй аргумент q нужен для явного указания "другого" дизъюнкта.
  example (hp : p) : p ∨ q := Or.intro_left q hp
  -- Or.intro_right p hq: доказываем p ∨ q, предъявляя hq : q.
  example (hq : q) : p ∨ q := Or.intro_right p hq

  -- коммутативность ∨: из p ∨ q получаем q ∨ p.
  -- Or.elim разбирает два случая:
  --   если hp : p — вводим через Or.intro_right (правый дизъюнкт q ∨ p)
  --   если hq : q — вводим через Or.intro_left  (левый дизъюнкт q ∨ p)
  example (h : p ∨ q) : q ∨ p :=
    Or.elim h
    (fun hp : p => Or.intro_right _ hp)
    (fun hq : q => Or.intro_left _ hq)

  -- то же, но через Or.inr/Or.inl — более короткие псевдонимы.
  -- Or.inl : p → p ∨ q, Or.inr : q → p ∨ q.
  -- здесь цель q ∨ p, поэтому:
  --   Or.inr hp означает "hp находится в правой позиции" → q ∨ p через inr
  --   Or.inl hq означает "hq находится в левой позиции" → q ∨ p через inl
  example (h : p ∨ q) : q ∨ p :=
    Or.elim h
    (fun hp => Or.inr hp)
    (fun hq => Or.inl hq)

  -- point-free стиль: функции передаются как значения без явных аргументов.
  example (h : p ∨ q) : q ∨ p :=
    Or.elim h Or.inr Or.inl

  -- dot notation на h : p ∨ q — h.elim вместо Or.elim h.
  example (h : p ∨ q) : q ∨ p :=
    h.elim Or.inr Or.inl

end Disjunction

-- ============================================================
-- отрицание и ложь (Not, False)
-- ============================================================
-- в lean ¬p определено как p → False.
-- это не отдельный конструктор, а просто определение:
--   notation:85 "¬" => Not
--   def Not (p : Prop) : Prop := p → False
-- следствие: "доказать ¬p" значит "построить функцию типа p → False",
-- то есть показать, что из p можно вывести противоречие.
--
-- False — пустой индуктивный тип (нет конструкторов).
-- False.elim : False → α — правило ex falso quodlibet:
-- из ложного можно вывести что угодно (любой тип обитаем,
-- если мы добрались до доказательства False).

namespace NegationAndFalsity
  variable (p q r : Prop)

  -- доказательство ¬p из "p → q" и "¬q".
  -- поскольку ¬p это p → False, нам нужна функция p → False.
  -- принимаем hp : p, применяем hpq : p → q, получаем hq : q,
  -- затем применяем hnq : ¬q (то есть q → False) к hq — получаем False.
  example (hpq : p → q) (hnq : ¬q) : ¬p :=
    fun hp : p => -- p -> False
      let hq := (hpq hp : q)
      show False from hnq hq

  -- из hp : p и hnp : ¬p (то есть p → False) получаем False,
  -- а из False через False.elim выводим q (любое утверждение).
  -- это и есть принцип ex falso: противоречие доказывает что угодно.
  example (hp : p) (hnp : ¬p) : q := -- ¬p : p → False
    False.elim (hnp hp)

  -- absurd : α → ¬α → β — удобная комбинаторная форма.
  -- реализована как: absurd ha hna := False.elim (hna ha).
  -- принимает доказательство hp : p и опровержение hnp : ¬p,
  -- применяет hnp к hp, получает False, затем False.elim даёт β.
  example (hp : p) (hnp : ¬p) : q :=
    absurd hp hnp

  -- absurd можно использовать косвенно:
  -- hqp : q → p, hq : q, значит hqp hq : p;
  -- hnp : ¬p; absurd (hqp hq) hnp : r.
  example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
    absurd (hqp hq) hnp

end NegationAndFalsity

-- ============================================================
-- логическая эквивалентность (Iff, ↔)
-- ============================================================
-- Iff p q (записывается p ↔ q) определена как структура с двумя полями:
--   structure Iff (p q : Prop) : Prop where
--     mp  : p → q   -- modus ponens: из p получаем q
--     mpr : q → p   -- modus ponens reverse: из q получаем p
-- по сути это просто And (p → q) (q → p), но с именованными полями.
-- Iff.intro : (p → q) → (q → p) → (p ↔ q) — конструктор.
-- Iff.mp    : (p ↔ q) → p → q — применение в прямом направлении.
-- Iff.mpr   : (p ↔ q) → q → p — применение в обратном направлении.

namespace LogicalEquivalence
  variable (p q r : Prop)

  -- доказательство p ∧ q ↔ q ∧ p:
  -- Iff.intro принимает две функции: прямую и обратную.
  -- обе функции переставляют компоненты пары.
  theorem and_swap : p ∧ q ↔ q ∧ p :=
    Iff.intro
      (fun h : p ∧ q => ⟨h.right, h.left⟩)
      (fun h : q ∧ p => ⟨h.right, h.left⟩)

  variable (h : p ∧ q)
  -- Iff.mp извлекает прямую импликацию из ↔ и применяет её к h.
  example : q ∧ p := Iff.mp (and_swap p q) h

  -- и через анонимный конструктор: ⟨f, g⟩ для Iff — это ⟨mp, mpr⟩.
  theorem and_swap' : p ∧ q ↔ q ∧ p :=
    ⟨fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩⟩

  -- dot notation на iff: h.mp — прямая импликация.
  example (h : p ∧ q) : q ∧ p := (and_swap' p q).mp h

end LogicalEquivalence

-- ============================================================
-- вспомогательные подцели: have и suffices
-- ============================================================
-- have в term-mode — это let-связывание для Prop-значений.
-- синтаксис: have name : T := expr; rest
-- семантика: вводит локальное имя для промежуточного результата,
-- доступного в rest. аналог let name : T := expr в выражениях,
-- но специально для доказательств (по сути — одно и то же).
--
-- suffices name : T from conclusion; proof_of_T
-- смысл "достаточно показать T" (откуда следует цель),
-- а потом доказать T. это инвертированный have:
--   сначала используем T для получения цели,
--   потом доказываем T.
-- это полезно, когда хочется сначала объяснить структуру доказательства,
-- а детали оставить на потом.

namespace AuxiliarySubgoals
  variable (p q : Prop)

  -- have hp : p := h.left  — даём имя доказательству h.left : p.
  -- have hq : q := h.right — даём имя доказательству h.right : q.
  -- затем собираем результат ⟨hq, hp⟩ : q ∧ p.
  example (h : p ∧ q) : q ∧ p :=
    have hp : p := h.left
    have hq : q := h.right
    (⟨hq, hp⟩ : q ∧ p)

  -- suffices hq : q from ⟨hq, hp⟩ означает:
  -- "если мы имеем hq : q, то цель q ∧ p достигается через ⟨hq, hp⟩;
  --  теперь докажем q".
  -- после suffices цель меняется на q, которую доказываем через h.right.
  -- это помогает читаемости: сначала показываем, как используем q,
  -- потом — откуда q берётся.
  example (h : p ∧ q) : q ∧ p :=
    have hp : p := h.left
    suffices hq : q from ⟨hq, hp⟩
    show q from h.right

end AuxiliarySubgoals

-- ============================================================
-- классическая логика: Classical.em и производные
-- ============================================================
-- конструктивная (интуиционистская) логика не допускает закон
-- исключённого третьего (law of excluded middle, LEM) как аксиому,
-- потому что в конструктивной математике "доказать p ∨ ¬p"
-- значит либо предъявить доказательство p, либо доказать ¬p —
-- а это невозможно для произвольного p.
--
-- lean 4 работает в классической логике через модуль Classical,
-- который добавляет аксиому:
--   Classical.em : ∀ (p : Prop), p ∨ ¬p
-- это пропозициональный аналог LEM.
--
-- важно: Classical.em — именно аксиома (axiom), не теорема.
-- она не доказывается в конструктивной системе; её принятие
-- переводит lean в классическую логику (что делает его
-- пригодным для обычной математики).

namespace ClassicalLogic
  open Classical

  variable (p : Prop)

  #check em p

  -- use  em: (p ∨ ¬p)  to create dne: (¬¬p → p)
  -- use dne: (¬¬p → p) to create  em: (p ∨ ¬p)

  -- dne (double negation elimination): из ¬¬p следует p.
  -- в конструктивной логике это недоказуемо — нужна классическая аксиома em.
  -- доказательство: разбираем em p на два случая.
  --   случай "p истинно" (hp : p): возвращаем hp напрямую (id).
  --   случай "p ложно" (hnp : ¬p): hnp : p → False,
  --     h : ¬¬p = ¬p → False;
  --     absurd hnp h : False → p — через ex falso.
  --     но absurd : α → ¬α → β, поэтому:
  --     absurd hnp h означает absurd (hnp : ¬p) (h : ¬¬p) : p.
  theorem dne (p : Prop) (h : ¬¬p) : p :=
    let hh := em p -- p ∨ ¬p
    Or.elim hh
      id
      (λ hnp : ¬p => absurd hnp h)

  -- em' доказывает LEM через dne — взаимная сводимость.
  -- чтобы доказать p ∨ ¬p, применяем dne к ¬¬(p ∨ ¬p).
  -- доказываем ¬¬(p ∨ ¬p):
  --   предполагаем hnpnp : ¬(p ∨ ¬p) (т.е. p ∨ ¬p → False).
  --   из hnpnp строим hnp : ¬p (если бы p, то p ∨ ¬p — противоречие).
  --   из hnpnp строим hnpnp' : ¬¬p (если бы ¬p, то p ∨ ¬p — противоречие).
  --   absurd hnp hnpnp' : False (имеем ¬p и ¬¬p одновременно).
  -- итого: ¬¬(p ∨ ¬p) доказано, применяем dne — получаем p ∨ ¬p.
  theorem em' (p : Prop) : p ∨ ¬p :=
    have h : ¬¬(p ∨ ¬p) :=
      λ hnpnp : ¬(p ∨ ¬p) =>
        have hnp : ¬p := λ hp => hnpnp (Or.inl hp)
        have hnpnp' : ¬¬p := λ hp => hnpnp (Or.inr hp)
        absurd hnp hnpnp'
    dne (p ∨ ¬p) h

  -- byCases — тактический комбинатор (работает в term-mode тоже).
  -- byCases (h1 : p ↦ ...) (h1 : ¬p ↦ ...) разворачивается в
  -- Or.elim (em p) (fun h1 : p => ...) (fun h1 : ¬p => ...).
  -- доказываем p из ¬¬p:
  --   если p — возвращаем h1 : p напрямую.
  --   если ¬p — absurd h1 h : p (имеем ¬p и ¬¬p — противоречие, false → p).
  example (h : ¬¬p) : p :=
    byCases
      (λ h1 : p ↦ h1)
      (λ h1 : ¬p ↦ absurd h1 h)

  -- byContradiction — доказательство от противного.
  -- byContradiction (h1 : ¬p ↦ ...) означает:
  -- "предположим ¬p и выведем противоречие (False)".
  -- реализовано через Classical.byContradiction:
  --   если дана функция ¬p → False, то p доказано через dne.
  -- здесь: принимаем h1 : ¬p, применяем h : ¬¬p к h1 — получаем False.
  example (h : ¬¬p) : p :=
    byContradiction
      (λ h1 : ¬p ↦ h h1)

end ClassicalLogic

-- ============================================================
-- упражнения (конструктивная логика)
-- ============================================================
-- все примеры ниже доказуемы без Classical.em — только интуиционистски.
-- это важно: конструктивная логика слабее классической,
-- поэтому доказательства здесь работают в любой логике.

namespace Exercises
  variable (p q r : Prop)

  -- commutativity of ∨ and ∧

  -- коммутативность ∨: p ∨ q ↔ q ∨ p.
  -- обе стороны симметричны: Or.elim переставляет ветки через inr/inl.
  -- если h : p ∨ q, разбираем:
  --   hp : p → Or.inr hp : q ∨ p (p попадает в правую позицию)
  --   hq : q → Or.inl hq : q ∨ p (q попадает в левую позицию)
  example : p ∨ q ↔ q ∨ p :=
    Iff.intro
      (λ (hpq : p ∨ q) => Or.elim hpq Or.inr Or.inl)
      (λ (hqp : q ∨ p) => Or.elim hqp Or.inr Or.inl)

  -- коммутативность ∧: p ∧ q ↔ q ∧ p.
  -- переставляем компоненты пары в обоих направлениях.
  example : p ∧ q ↔ q ∧ p :=
    Iff.intro
      (λ (hpq : p ∧ q) => ⟨hpq.right, hpq.left⟩)
      (λ (hqp : q ∧ p) => ⟨hqp.right, hqp.left⟩)

  -- associativity of ∧ and ∨

  -- ассоциативность ∧: (p ∧ q) ∧ r ↔ p ∧ (q ∧ r).
  -- ∧ правоассоциативна в lean (p ∧ q ∧ r = p ∧ (q ∧ r)).
  -- прямое направление: h.left.left : p, h.left.right : q, h.right : r.
  -- обратное направление: h.left : p, h.right.left : q, h.right.right : r.
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    Iff.intro
      (λ h => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
      (λ h => ⟨⟨h.left, h.right.left⟩, h.right.right⟩)

  -- ассоциативность ∨: (p ∨ q) ∨ r ↔ p ∨ (q ∨ r).
  -- прямое направление: h : (p ∨ q) ∨ r.
  --   если h : p ∨ q — разбираем pq:
  --     если p — Or.inl p (левая ветка p ∨ (q ∨ r))
  --     если q — Or.inr (Or.inl q) (правая ветка, внутри — левая)
  --   если r — Or.inr (Or.inr r) (правая ветка, внутри — правая)
  -- обратное направление аналогично, но зеркально.
  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    Iff.intro
      (λ h => Or.elim h
        (λ pq => Or.elim pq Or.inl (λ q => Or.inr (Or.inl q)))
        (λ r => Or.inr (Or.inr r)))
      (λ h => Or.elim h
        (λ p => Or.inl (Or.inl p))
        (λ qr => Or.elim qr (λ q => Or.inl (Or.inr q)) Or.inr))

  -- distributivity

  -- дистрибутивность ∧ над ∨: p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r).
  -- прямое направление: h.left : p, h.right : q ∨ r.
  --   если q: собираем Or.inl ⟨h.left, q⟩ : (p ∧ q) ∨ (p ∧ r).
  --   если r: собираем Or.inr ⟨h.left, r⟩ : (p ∧ q) ∨ (p ∧ r).
  -- обратное направление: h : (p ∧ q) ∨ (p ∧ r).
  --   если pq : p ∧ q: собираем ⟨pq.left, Or.inl pq.right⟩.
  --   если pr : p ∧ r: собираем ⟨pr.left, Or.inr pr.right⟩.
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    Iff.intro
      (λ h =>
        Or.elim h.right
          (λ q => Or.inl ⟨h.left, q⟩)
          (λ r => Or.inr ⟨h.left, r⟩))
      (λ h =>
        Or.elim h
          (λ pq => ⟨pq.left, Or.inl pq.right⟩)
          (λ pr => ⟨pr.left, Or.inr pr.right⟩))

    -- other properties

    -- каррирование: (p → q → r) ↔ (p ∧ q → r).
    -- прямое: из функции двух аргументов делаем функцию пары.
    --   h_p_qr : p → q → r; h_pq : p ∧ q.
    --   (h_p_qr h_pq.left) h_pq.right : r.
    -- обратное: из функции пары делаем функцию двух аргументов.
    --   h_pq_r : p ∧ q → r; h_p : p; h_q : q.
    --   h_pq_r ⟨h_p, h_q⟩ : r.
    example : (p → (q → r)) ↔ (p ∧ q → r) :=
      Iff.intro
        (λ h_p_qr => λ h_pq => (h_p_qr h_pq.left) h_pq.right)
        (λ h_pq_r => λ h_p => λ h_q => h_pq_r ⟨h_p, h_q⟩)

    -- (p ∨ q → r) ↔ (p → r) ∧ (q → r).
    -- дистрибутивность → над ∨ справа.
    -- прямое: из обработчика p ∨ q → r получаем пару обработчиков.
    --   h_pq_r (Or.inl p) : r, h_pq_r (Or.inr q) : r.
    -- обратное: из пары обработчиков делаем обработчик p ∨ q.
    --   Or.elim pq pr_qr.left pr_qr.right : r.
    example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
      Iff.intro
        (λ h_pq_r => ⟨λ p => h_pq_r (Or.inl p), λ q => h_pq_r (Or.inr q)⟩)
        (λ pr_qr => λ pq => Or.elim pq pr_qr.left pr_qr.right)

    -- ¬(p ∨ q) ↔ ¬p ∧ ¬q (де Морган, первый закон, интуиционистски).
    -- этот закон доказуем конструктивно в обоих направлениях.
    -- прямое: h_npq : (p ∨ q) → False.
    --   ¬p = λ h_p => h_npq (Or.inl h_p) : False.
    --   ¬q = λ h_q => h_npq (Or.inr h_q) : False.
    -- обратное: h_npnq : ¬p ∧ ¬q; h_pq : p ∨ q.
    --   разбираем h_pq: absurd h_p h_npnq.left или absurd h_q h_npnq.right.
    example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
      Iff.intro
        (λ h_npq =>
          ⟨λ h_p => h_npq (Or.inl h_p),
           λ h_q => h_npq (Or.inr h_q)⟩)
        (λ h_npnq => λ h_pq => Or.elim h_pq
          (λ h_p => absurd h_p h_npnq.left)
          (λ h_q => absurd h_q h_npnq.right))

    -- ¬p ∨ ¬q → ¬(p ∧ q) (де Морган, одно направление, конструктивно).
    -- обратное направление ¬(p ∧ q) → ¬p ∨ ¬q требует классики (em).
    -- здесь: h_npnq : ¬p ∨ ¬q; h_pq : p ∧ q.
    --   если ¬p: absurd h_pq.left h_np : False.
    --   если ¬q: absurd h_pq.right h_nq : False.
    example : ¬p ∨ ¬q → ¬(p ∧ q) :=
      λ h_npnq => λ h_pq => Or.elim h_npnq
        (λ h_np => h_np h_pq.left)
        (λ h_nq => h_nq h_pq.right)

    -- ¬(p ∧ ¬p): p не может быть одновременно истинным и ложным.
    -- деструктурируем пару: ⟨h_p, h_np⟩ : p ∧ ¬p.
    -- absurd h_p h_np : False — применяем h_np : p → False к h_p : p.
    example : ¬(p ∧ ¬p) :=
      λ ⟨h_p, h_np⟩ => absurd h_p h_np

    -- p ∧ ¬q → ¬(p → q).
    -- имея p и ¬q, показываем, что импликация p → q ложна.
    -- ¬(p → q) = (p → q) → False.
    -- принимаем h_pfq : p → q; применяем к h_p : p; получаем h_pfq h_p : q.
    -- но h_nq : q → False; absurd-style: h_nq (h_pfq h_p) : False.
    example : p ∧ ¬q → ¬(p → q) :=
      λ ⟨h_p, h_nq⟩ =>
        λ h_pfq => h_nq (h_pfq h_p)

    -- ¬p → (p → q): из ложного следует что угодно (ex falso).
    -- принимаем h_np : ¬p; h_p : p; absurd h_p h_np : False → q.
    example : ¬p → (p → q) :=
      λ h_np => (λ h_p => absurd h_p h_np)

    -- (¬p ∨ q) → (p → q): "если не-p или q, то p влечёт q".
    -- это конструктивная форма материальной импликации.
    -- принимаем h : ¬p ∨ q; h_p : p.
    --   Or.elim h: если ¬p — absurd h_p (это False, затем q через ex falso,
    --                                     здесь absurd h_p работает как False.elim);
    --              если q  — id возвращает q напрямую.
    -- важно: absurd h_p здесь — это функция ¬p → q, потому что
    -- absurd : α → ¬α → β, частичное применение absurd h_p : ¬p → q.
    example : (¬p ∨ q) → (p → q) :=
      λ h => (λ h_p => Or.elim h (absurd h_p) id)

    -- p ∨ False ↔ p: False ничего не добавляет к дизъюнкции.
    -- прямое: разбираем; если p — id; если False — False.elim h_f.
    -- обратное: Or.inl h_p.
    example : p ∨ False ↔ p :=
      Iff.intro
        (λ h_pfalse => Or.elim h_pfalse id (λ h_f => False.elim h_f))
        (λ h_p => Or.inl h_p)

    -- p ∧ False ↔ False: если имеем False, то конъюнкция тривиальна.
    -- прямое: из пары извлекаем h_f : False и возвращаем его.
    -- обратное: False.elim — функция False → p ∧ False (или любого типа).
    example : p ∧ False ↔ False :=
      Iff.intro
        (λ ⟨_, h_f⟩ => h_f)
        False.elim

    -- (p → q) → (¬q → ¬p): контрапозиция (доказуема конструктивно).
    -- это более слабое утверждение, чем обратная контрапозиция (¬p → ¬q) → (p → q),
    -- которая требует классики (двойное отрицание).
    -- h_pfq : p → q; h_nq : ¬q; h_p : p.
    -- h_pfq h_p : q; absurd (h_pfq h_p) h_nq : False = ¬p применена к h_p.
    example : (p → q) → (¬q → ¬p) :=
      λ h_pfq => (λ h_nq => λ h_p => absurd (h_pfq h_p) h_nq)

end Exercises

-- ============================================================
-- упражнения, требующие классической логики (Classical.em)
-- ============================================================
-- следующие примеры не доказуемы конструктивно.
-- для их доказательства необходима аксиома em.
-- два с sorry оставлены нерешёнными — объяснения ниже.

namespace ExercisesClassical
  open Classical

  variable (p q r : Prop)

  -- (p → q ∨ r) → ((p → q) ∨ (p → r)).
  -- идея: разбираем по em p — истинно ли p?
  --   если p истинно (h_p : p): вычисляем h h_p : q ∨ r.
  --     разбираем: если q — Or.inl (λ _ => h_q) : (p → q) ∨ (p → r).
  --                если r — Or.inr (λ _ => h_r) : (p → q) ∨ (p → r).
  --   если p ложно (h_np : ¬p): тогда (p → q) тривиально (ex falso).
  --     Or.inl (λ h_p => absurd h_p h_np) : (p → q) ∨ (p → r).
  -- без em нельзя разобрать, какой из дизъюнктов выбрать для результата.
  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
    λ h => Or.elim (em p)
      (λ h_p => Or.elim (h h_p)
        (λ h_q => Or.inl (λ _ => h_q))
        (λ h_r => Or.inr (λ _ => h_r)))
      (λ h_np => Or.inl (λ h_p => absurd h_p h_np))

  -- ¬(p ∧ q) → ¬p ∨ ¬q (де Морган, второй закон, классически).
  -- конструктивно недоказуемо: из ¬(p ∧ q) нельзя "достать" конкретный
  -- ¬p или ¬q без знания, который из них ложен.
  -- идея: разбираем em p и em q.
  --   если p и q — противоречие с h : ¬(p ∧ q); False.elim.
  --   если p и ¬q — Or.inr h_nq.
  --   если ¬p — Or.inl h_np (независимо от q).
  example : ¬(p ∧ q) → ¬p ∨ ¬q :=
    λ h => Or.elim (em p)
      (λ h_p => Or.elim (em q)
        (λ h_q =>
          have h_pq : p ∧ q := ⟨h_p, h_q⟩
          False.elim (h h_pq))
        (λ h_nq => Or.inr h_nq))
      (λ h_np => Or.inl h_np)

  -- ¬(p → q) → p ∧ ¬q.
  -- оставлено с sorry: это нетривиально даже классически.
  -- идея: из ¬(p → q) нужно извлечь p и ¬q.
  --   ¬(p → q) означает (p → q) → False.
  --   если предположить ¬p, то (p → q) тривиально — получим False,
  --     значит ¬¬p, то есть классически p.
  --   если предположить q, то λ _ => q : p → q — получим False,
  --     значит ¬q.
  -- технически: p = byContradiction (λ hnp => h (λ hp => absurd hp hnp))
  --             ¬q = λ hq => h (λ _ => hq)
  -- но это требует Classical.byContradiction, и оба sorry можно закрыть.
  example : ¬(p → q) → p ∧ ¬q :=
    λ h => ⟨sorry, sorry⟩

  -- (p → q) → (¬p ∨ q): материальная импликация через em.
  -- если p: h h_p : q → Or.inr h_p.
  -- если ¬p: Or.inl h_np напрямую.
  example : (p → q) → (¬p ∨ q) :=
    λ h => Or.elim (em p)
      (λ h_p => Or.inr (h h_p))
      (λ h_np => Or.inl h_np)

  -- (¬q → ¬p) → (p → q): обратная контрапозиция (классически).
  -- конструктивно недоказуема — требует двойного отрицания.
  -- идея: разбираем em q.
  --   если q — возвращаем h_q напрямую (игнорируем h_p).
  --   если ¬q — h h_nq : ¬p; absurd h_p (h h_nq) : False → q.
  example : (¬q → ¬p) → (p → q) :=
    λ h => Or.elim (em q)
      (λ h_q => λ _ => h_q)
      (λ h_nq => λ h_p => absurd h_p (h h_nq))

  -- p ∨ ¬p: это прямо Classical.em p — закон исключённого третьего.
  example : p ∨ ¬p := em p

  -- (((p → q) → p) → p): закон Пирса (Peirce's law).
  -- это классически истинное утверждение, эквивалентное LEM.
  -- разбираем em (p → q):
  --   если (p → q): h h_pq : p → возвращаем.
  --   если ¬(p → q): оставлено с sorry.
  --     нужно показать p из h : ((p → q) → p) и h_npq : ¬(p → q).
  --     из h_npq : (p → q) → False и byContradiction:
  --       предположим ¬p; тогда (λ _ => False.elim (h_npq (λ hp => absurd hp ...)))
  --       это сложная цепочка — можно закрыть через:
  --       byContradiction (λ hnp => h_npq (λ hp => absurd hp hnp))
  --       это даёт p → q (из ¬p следует что угодно), применяем h.
  example : (((p → q) → p) → p) :=
    λ h => Or.elim (em (p → q))
      (λ h_pq => h h_pq)
      (λ h_npq => sorry)

end ExercisesClassical

-- ============================================================
-- упражнения: только конструктивная логика
-- ============================================================
-- ¬(p ↔ ¬p) должно быть доказуемо без classical.em.
-- идея: если p ↔ ¬p, то из p следует ¬p и из ¬p следует p.
--   предположим h : p ↔ ¬p.
--   h.mp  : p → ¬p
--   h.mpr : ¬p → p
--   если p истинно (hp : p): h.mp hp : ¬p; absurd hp (h.mp hp) : False.
--   если p ложно (hnp : ¬p): h.mpr hnp : p; absurd (h.mpr hnp) hnp : False.
--   но "если p истинно, иначе ..." — это уже разбор случаев,
--   что требует em в общем случае.
--   однако конструктивное доказательство существует:
--     have hnp : ¬p := λ hp => absurd hp (h.mp hp)
--     absurd (h.mpr hnp) hnp
--   сначала строим ¬p конструктивно из h.mp,
--   затем применяем h.mpr к hnp, получая p, и сразу absurd с hnp.
--   это чисто конструктивная цепочка, без em.
-- оставлено с sorry — упражнение для самостоятельного решения.

namespace ExercisesNonClassical
  variable (p : Prop)

  -- TODO: Prove without using classical logic.
  example : ¬(p ↔ ¬ p) := sorry
end ExercisesNonClassical
