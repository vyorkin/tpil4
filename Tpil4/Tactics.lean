-- 5.1. Entering Tactic Mode
--
-- Тактики — это альтернативный способ строить пруф-термы.
-- Вместо того чтобы писать готовый терм, ты описываешь последовательность шагов
-- (тактик), а Lean за тебя собирает итоговый пруф-терм.
-- Блок тактик начинается с ключевого слова `by`.
--
-- apply vs exact:
--   exact e   — закрывает текущую цель полностью; e должен иметь тип,
--               который точно совпадает с целью (или унифицируется с ней).
--               Если после exact остаются незакрытые метапеременные — ошибка.
--   apply e   — применяет e к текущей цели; если тип e — функция (импликация),
--               то Lean порождает подцели для каждого аргумента, который ещё
--               не задан. Т.е. apply "разбирает" цель и оставляет незакрытые ветки.
--
-- Правило выбора: если можешь написать exact — пиши exact, это яснее.
-- apply используй тогда, когда хочешь поэтапно закрывать подцели.

theorem test₀ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  -- apply And.intro создаёт две подцели: левую и правую часть конъюнкции.
  -- · фокусирует следующую тактику на первой из них.
  · exact hp
  · apply And.intro
    · exact hq
    · exact hp

-- Можно использовать apply везде, где сработает exact,
-- но если можешь использовать exact, то лучше используй её.

-- Пруф-терм можно посмотреть вот так:
#print test₀
--
-- test₀ : ∀ (p q : Prop), p → q → p ∧ q ∧ p :=
--   fun p q hp hq ↦ ⟨hp, ⟨hq, hp⟩⟩

-- Вот такой охуенный пруф-терм ты смог сконструировать тактиками!
-- Удивительно, да?

-- Применение составных выражений.
-- apply можно частично насытить аргументами прямо в строке.
-- apply And.intro hp — это как если бы ты передал левую часть сразу,
-- оставив только правую часть как открытую подцель.
-- Это сокращает количество явных тактик exact.
theorem test₁ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  apply And.intro hq hp

-- Пруф-терм получится такой же в точности.
#print test₁

-- Можно применять сразу несколько тактик
-- на одной строке, разделяя точкой с запятой.
-- Точка с запятой здесь — простой разделитель: "сделай это, потом то".
-- Это не комбинатор <;>, который применяет тактику ко всем подцелям.
theorem test₂ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp

-- Заметь как называются кейсы (case left, case right) при применении
-- тактики apply And.intro в примере ниже. Это тэги, линь берёт их из
-- названий параметров в определении And.intro.
--
-- Почему именно left и right:
-- structure And : Prop where
--   intro ::
--     left  : Prop  -- ← именно это имя берётся для case left
--     right : Prop  -- ← и это для case right
--
-- Lean запоминает имена полей / параметров конструктора и использует их
-- как метки подцелей, чтобы ты мог явно обращаться к нужной ветке.
-- Это удобно: можно закрывать ветки в произвольном порядке (см. test₄).
--
-- Так можно и самому структурировать свои доказательства,
-- cast <tag> => <tactics>.

theorem test₃ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  -- · exact hp или тоже самое ниже:
  case left  => exact hp
  case right =>
    apply And.intro
    case left  => exact hq
    case right => exact hp

-- Когда мы попадаем в конкретный кейс, остальные прячутся,
-- т.е. мы как бы фокусируемся на данной подцели.

-- Можно менять кейсы местами и доказать сначала правую часть.
theorem test₄ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    exact hq
    exact hp
  case left => exact hp

-- Не всегда имеет смысл менять местами подцели,
-- поэтому у нас есть более простая возможность фокусироваться на них,
-- не "называя их по имени".

theorem test₅ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  · exact hp
  · apply And.intro
    · exact hq
    · exact hp

-- 5.2. Basic Tactics

-- Iff.intro требует доказательства обоих направлений (→ и ←), поэтому
-- apply Iff.intro создаёт две подцели — по одной на каждое направление.
-- Or.elim : (a ∨ b) → (a → c) → (b → c) → c
-- Применяем его к h.right (это q ∨ r), передавая два обработчика-ветки.
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro h
    apply Or.elim h.right
    · intro hq
      apply Or.inl
      apply And.intro
      · exact h.left
      · exact hq
    · intro hr
      apply Or.inr
      apply And.intro
      · exact h.left
      · exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr

-- intro a — забирает из цели "α →" и кладёт a : α в контекст.
-- Это тактика-аналог lambda-абстракции из пруф-терм-стиля.
-- После intro a цель меняется с "α → α" на просто "α".
example (α : Type) : α → α := by
  intro a
  exact a

-- def rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a

-- rfl в тактик-моде — это отдельная тактика (не просто терм rfl).
-- Она пытается закрыть цель вида "a = b", проверяя что a и b
-- совпадают по бета/дельта-редукции (т.е. по определению).
-- Под капотом это Eq.refl, но тактика rfl умеет сама редуцировать
-- обе стороны перед сравнением, поэтому закрывает больше целей,
-- чем просто "exact rfl" в терм-стиле.
-- apply_rfl — ещё один вариант той же тактики.
example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x
  -- exact rfl
  -- rfl
  -- apply_rfl

-- Тактика intro позволяет разбирать и
-- затаскивать в контекст гипотезу по кусочкам.
-- intro ⟨x, hpx, hqx⟩ — это деструктурирующий паттерн:
-- гипотеза ∃ x, p x ∧ q x сразу разбирается на свидетеля x,
-- доказательство левой части hpx и правой части hqx.
-- Это экономит промежуточные шаги по сравнению с intro h; cases h; cases h.right.
example (q p : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨x, hpx, hqx⟩
  exact ⟨x, hqx, hpx⟩

-- Вот кстати эквивалентный пример с использованием тактики obtain,
-- тут в целом должно быть понятно, что она делает.
-- obtain — это тактика деструктуризации: она берёт уже существующую
-- гипотезу h и разбирает её по паттерну.
-- Разница с intro: intro забирает цель в контекст И сразу деструктурирует,
-- а obtain деструктурирует уже имеющуюся в контексте гипотезу.
-- Тоже работает и для дизъюнкции, только форма будет выглядеть как-то так:
-- obtain a | b | c := h
example (q p : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  obtain ⟨x, hpx, hqx⟩ := h
  exact ⟨x, hqx, hpx⟩

-- Паттерн-матчинг с помощью intro.
-- Когда гипотеза имеет несколько конструкторов (дизъюнкция, сумма),
-- intro можно использовать как match: перечислять ветки через |.
-- Здесь ∃ x, p x ∨ q x имеет две ветки по форме вложенного Or.
-- intro без имени + | — это краткая запись "введи и сразу разбери".
example (q p : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨x, Or.inl h⟩ => exact ⟨x, Or.inr h⟩
  | ⟨x, Or.inr h⟩ => exact ⟨x, Or.inl h⟩

variable (x y z w : Nat)

-- Тактика assumption ищет в контексте и применяет всё, что применяется.
example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption -- Применяет h₃

-- Тактика assumption умеет унифицировать метапеременные.
example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans -- x = ?b → ?b = w → x = w
  · assumption   -- Унифицирует case h₁: x = ?b, используя h₁: x = y
  · -- Остаётся доказать case h₂ : ?b = w, т.е. h₂ : y = w (не путать с гипотезой h₂)
    apply Eq.trans -- y = ?h₂.b → ?h₂.b = w → y = w
    · assumption   -- Унифицирует case h₂.h₁: y = ?h₂.b, используя h₂ : y = z
    · assumption   -- Унификация z = w с помощью h₃

-- intro vs intros — в чём разница:
--   intro x y z — именует переменные явно, ты сам даёшь им имена.
--   intros       — то же самое, но имена генерирует Lean (a✝, b✝, ...).
--                  Имена с символом ✝ (крестик) — "недоступные": на них
--                  нельзя ссылаться ни в других тактиках, ни в термах.
--
-- Почему это нужно: иногда просто хочешь затащить всё подряд в контекст,
-- не задумываясь об именах — например, когда дальше используешь assumption,
-- которой вообще не нужны имена.
--
-- Тактика intros забирает в контекст всё и сама выбирает имена.
-- На сгенерированные имена ты никак не можешь ссылаться
-- (если не переименовал с помощью rename_i, об этом ниже).
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption

-- Это можно обойти комбинатором unhygienic и тогда intros будет
-- давать имена, на которые можно ссылаться.
-- unhygienic — это команда, которая отключает гигиену имён:
-- Lean перестаёт помечать сгенерированные имена как недоступные.
-- Использование unhygienic считается плохой практикой для финальных доказательств,
-- потому что делает код хрупким — имена могут поменяться при рефакторинге.
-- Лучше пользоваться rename_i.
example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1

-- А ещё можно переименовать последние сгенерированные
-- имена с помощью тактики rename_i.
-- rename_i h1 h2 — берёт последние N имён из контекста (справа налево)
-- и переименовывает их. После этого можно ссылаться на них по имени.
-- Это предпочтительный способ: явно называешь только то, что нужно.
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  rename_i h1 h2 -- Переименовать 2 из 3-х последних гипотез в контексте.
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1

-- Можно использовать rfl для доказательства любых
-- рефлексивных отношений в целях. Работает для аргументов
-- равных по определению. Например можно написать rfl вместо Eq.refl.
-- Здесь цель: (λ x : Nat => 0) y = 0.
-- Левая часть бета-редуцируется до 0, поэтому обе стороны — 0.
-- rfl применяет бета-редукцию и закрывает цель.
example (y : Nat) : (λ x : Nat => 0) y = 0 := by
  rfl

/-
rfl более мощная тактика, чем может показаться на первый взгляд.
Хотя формулировка теоремы звучит как a = a, Lean позволяет использовать всё, что
является равным этому типу по определению. Например, утверждение 2 + 2 = 4 доказывается
при помощи rfl, потому что обе стороны одинаковы с точки зрения определённого равенства.

Тактика rfl фактически разворачивает определение сложения,
редуцирует пока редуцируется и проверяет равны ли обе стороны равенства.
-/

-- Как видишь, rfl понимает a + b = c + d.
example (y : Nat) : (λ _ : Nat => 0) y + 1 = 0 + 1 := by
  rfl

-- repeat t — применяет тактику t снова и снова, пока она успешно применяется.
-- Как только t не может быть применена (фейлится), repeat останавливается
-- без ошибки. Это отличает repeat от простого повторения: не нужно знать заранее
-- сколько раз применять.
-- Здесь после apply Eq.symm нужно закрыть две подцели assumption'ом.
-- repeat assumption применит assumption дважды — по одному разу на каждую цель.
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption

-- 5.3. More Tactics

-- Тактика revert является обратной к intro.
-- Она перемещает переменную или гипотезу из контекста обратно в цель,
-- превращая её в универсально квантифицированную часть.
-- revert x при цели "x = x" и x : Nat в контексте
-- даёт новую цель "∀ x : Nat, x = x".
-- Зачем это нужно: иногда перед применением какой-то тактики
-- (например induction) нужно обобщить утверждение — убрать конкретный
-- аргумент из контекста и вернуть его в цель.
example (x : Nat) : x = x := by
  revert x
  intro y
  rfl

-- Гипотезы тоже можно втаскивать в цель.
example (x y : Nat) (h : x = y) : y = x := by
  revert h
  intro h₁
  apply Eq.symm
  assumption

-- Тактика revert втащит в цель так же и всё, что зависит от втаскиваемого.
-- В данном случае это гипотеза h : x = y. Ну просто потому, что для того,
-- чтобы её определить нужно сначала определить что такое x, тк она от него зависит.
example (x y : Nat) (h : x = y) : y = x := by
  revert x
  intros
  apply Eq.symm
  assumption

-- Можно сразу несколько штуковин втаскивать.
example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  intros
  apply Eq.symm
  assumption

-- Можно заменять произвольные выражения в цели,
-- используя тактику generalize. Обобщение короче.
-- generalize expr = x — заменяет все вхождения expr в цели на свежую
-- переменную x. Это позволяет работать с абстрактным x вместо конкретного значения.
-- Вот так можно сделать из 3 = 3 общее утвеждение о равенстве x = x.
example : 3 = 3 := by
  generalize 3 = x
  revert x
  intro y
  rfl

-- Обобщить-то можно что хочешь, а доказать можно не всё.
-- После generalize 3 = x цель становится 2 + x = 5,
-- что уже неверно для произвольного x. Lean честно требует доказательства.
example : 2 + 3 = 5 := by
  generalize 3 = x
  sorry

-- Свои обобщения можно сохранять в контексте как гипотезы.
-- generalize h : expr = x — делает то же самое, что и выше,
-- но дополнительно кладёт в контекст гипотезу h : expr = x.
-- Это уравнение позволяет потом переписать обратно: rw [← h]
-- вернёт x обратно в expr и мы получим доказуемую цель.
-- Обобщаем цель, сохраняем это обобщение как гипотзу и
-- переписываем обратно, перепсывая x на 3.
example : 2 + 3 = 5 := by
  generalize h : 3 = x
  rw [← h]

-- 5.3. More Tactics

-- Тактика cases по сути это паттерн-матичинг для типа-суммы
-- (вообще для любого индуктивного типа).
-- В примере ниже использование cases эквивалентно Or.elim.
-- cases h with | inl hp => ... | inr hq => ... — синтаксис похож на match:
-- каждая ветка обрабатывает один конструктор.
-- В ветке inl доступна гипотеза hp : p, в ветке inr — hq : q.
-- Для Or это два конструктора: Or.inl и Or.inr.
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq
-- ^ Порядок не важен

-- Та же фигня, только в тактик-мод (без with).
-- Только cases создаёт не именованные гипотезы.
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  · apply Or.inr
    assumption
  · apply Or.inl
    assumption

-- Использование cases удобно в частности,
-- если можно решить сразу несколько подцелей какой-то одной тактикой.
-- Тактике assumption как раз всё равно, что гипотезы анонимные.
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption

-- Можно использовать вот такой комбинатор тактик tac1 <;> tac2,
-- чтобы применить тактику tac2 ко всем подцелям, которые
-- производит тактика tac1.
-- Здесь cases h порождает две подцели (ветку inl и ветку inr),
-- и assumption применяется к обеим. В каждой ветке в контексте
-- есть анонимная гипотеза : p, и assumption её находит.
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption

-- Хорошо комбинировать cases с тактикой case и/или
-- нотацией для фокусировки на подцели.

-- Вот ниже всякие возможные варинты как
-- сделать одно и тоже разными способами.

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  · apply Or.inr
    assumption
  · apply Or.inl
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  case inl h =>
    apply Or.inr
    assumption

-- Можно смешивать.
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  · apply Or.inr
    assumption

-- С помощью cases можно распаковать и конъюнкцию
-- (и вообще любой индуктивный тип).
-- Тактика constructor распаковывает единственный
-- конструктор типа-произведения.
-- Для And цель p ∧ q имеет единственный конструктор And.intro,
-- поэтому constructor порождает две подцели: p и q.
-- Это удобнее чем apply And.intro, потому что не нужно знать имя конструктора.
-- Правило: если тип цели имеет ровно один конструктор — используй constructor.
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      . apply Or.inl; constructor <;> assumption
      . apply Or.inr; constructor <;> assumption
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq =>
        constructor; exact hp; apply Or.inl; exact hq
    | inr hpr =>
      cases hpr with
      | intro hp hr =>
        constructor; exact hp; apply Or.inr; exact hr

-- С cases можно распаковывать любой индуктивный тип.
-- Например, квантор существования.
-- ∃ x, p x определён как Exists (fun x => p x),
-- и его единственный конструктор — Exists.intro x hpx.
-- cases разбирает его на части: свидетель x и доказательство hpx : p x.
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with -- Появляется x и px в контексте
  | intro x px =>
    constructor
    apply Or.inl
    exact px

-- ^ Это немного надуманный пример, потому что лучше сделать вот так:
--   intro ⟨x, px⟩

-- Применение constructor к ∃ x, p x распаковывает
-- конструктор этого квантора и создаёт в цели метапеременную вместо x.
-- Дальше, когда мы показываем exact px, то ?x унифицируется с x.
-- Если хочешь избежать появления этой метапеременной и такой
-- типа поздней унификации, то можешь сразу показать что такое х,
-- c помощью exists x.
-- exists x — это тактика специально для ∃-целей: она сразу задаёт свидетеля,
-- оставляя только подцель с предикатом p x. Это яснее чем constructor + exact.

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px =>
    exists x
    apply Or.inl
    exact px

-- Ещё пример.
example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x
--     ^^^ Тут когда мы пишем exists x, линь
--         ищет в контексте требуемые в цели гипотезы.
--         Попробуй, например, написать exists y,
--         линь попросит тебя предъявить q y ∧ p y.

-- Раскидывам гипотезу конъюнкции до отдельных
-- конъюнктов и пересобираем в обратном порядке.
def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption

def swap_sum : Sum α β → Sum β α := by
  intro p
  cases p
  · apply Sum.inr; assumption
  · apply Sum.inl; assumption

section
open Nat

-- С помощью cases можно и по натуральным числам Пеано матчиться.
-- Nat — индуктивный тип с двумя конструкторами:
--   Nat.zero : Nat
--   Nat.succ : Nat → Nat
-- cases m with | zero => ... | succ m' => ... — это аналог match m with
-- в терм-стиле. В ветке succ доступен предшественник m' : Nat.
-- Это базовый приём при доказательстве по случаям для натуральных чисел
-- (не путать с индукцией — cases не даёт индукционную гипотезу).
example (P : Nat → Prop)
        (h₀ : P 0) (h₁ : ∀ n, P (succ n))
        (m : Nat) : P m := by
cases m with
| zero => exact h₀
| succ m' => exact h₁ m'

-- Тактика contradiction сама ищет в контексте
-- гипотезы противоречащие цели или друг другу.
-- Она закрывает любую цель, если в контексте есть:
--   - h : P и h' : ¬P для одного и того же P
--   - h : False
--   - гипотеза вида a ≠ a
-- Здесь после cases h в контексте оказываются hp : p и hright : ¬p (т.е. p → False),
-- contradiction находит это противоречие и закрывает цель q автоматически.
example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction
end

-- match внутри тактик — это полноценный паттерн-матчинг прямо в середине
-- доказательства. После intro h мы получаем h в контексте и сразу разбираем его
-- через match. Это альтернатива cases: match более гибок (можно матчить вложенные паттерны),
-- но менее идиоматичен в тактик-стиле чем cases with.
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨_, Or.inl _⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ =>
      apply Or.inr; constructor <;> assumption
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ =>
      constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ =>
      constructor; exact hp; apply Or.inr; exact hr

-- Можно делать то же самое (intro + match) за один шаг,
-- не именуя гипотезу, тк мы её сразу же хотим разбирать.
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨hp, Or.inl hq⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨hp, Or.inr hr⟩ =>
      apply Or.inr; constructor <;> assumption
  . intro
    | Or.inl ⟨hp, hq⟩ =>
      constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨hp, hr⟩ =>
      constructor; assumption; apply Or.inr; assumption

-- 5.4. Structuring Tactic Proofs

-- Можно комбинировать тактик-мод и прямое конструирование пруф-термов.
-- Внутри exact можно писать have ... в терм-стиле (не как тактику),
-- а потом переключиться обратно в тактик-мод через show ... by.
-- Это мощный гибридный стиль: exact фиксирует форму терма,
-- а by-блок внутри show позволяет дальше работать тактиками.
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  -- Нихуясе, братик, ты тут пишешь exact, а дальше,
  -- а дальше, начинаешь have-have и show .. by, нихуясе.
  -- Как часто ты такое применяешь?
  exact
    have hp  : p     := h.left
    have hqr : q ∨ r := h.right
    -- Вот тут show это не просто "комментарий",
    -- тут именно требуется показать какой терм мы конструируем.
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro h
    cases h.right with
    | inl hq => exact Or.inl ⟨h.left, hq⟩
    | inr hr => exact Or.inr ⟨h.left, hr⟩
  · intro h
    cases h with
    | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩

-- Тактика show p — проверяет, что текущая цель равна p по определению
-- (т.е. по бета/дельта-редукции), и переименовывает цель в p.
-- Это полезно как документирование: явно указываешь что собираешься доказать,
-- и Lean проверяет что ты не ошибся. Если p не совпадает с целью — ошибка.
-- Внутри exact (как в примере выше) — show переключает в тактик-мод.
-- Как самостоятельная тактика (ниже) — просто переименовывает цель.
-- Можно использовать show как "комментарий".
-- Ну т.е. не как сабтактику, не show .. by внутри чего-то (типа exact).
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro h
    cases h.right with
    | inl hq =>
      show p ∧ q ∨ p ∧ r
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show p ∧ q ∨ p ∧ r
      exact Or.inr ⟨h.left, hr⟩
  · intro h
    cases h with
    | inl hpq =>
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩

-- Тактику show можно использовать, когда хочется
-- поменять цель на какую-то ей эквивалентную.
-- Здесь n + 1 и Nat.succ n — одно и то же по определению сложения,
-- поэтому show Nat.succ n = Nat.succ n не вызывает ошибки.
-- После такой замены rfl закрывает цель trivially.
example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl

-- С помощью тактики have можно вводить свои подцели в любой момент.
-- have h : p := e — добавляет в контекст гипотезу h : p,
-- где e — доказательство p (либо в терм-стиле, либо через последующий by-блок).
-- Если написать simply have h : p — то Lean сначала генерирует подцель p,
-- ты её закрываешь, а потом h появляется в контексте для дальнейшей работы.
-- have удобен когда хочешь именовать промежуточный факт и потом сослаться на него.
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have hpq : p ∧ q := ⟨hp, hq⟩
    apply Or.inl
    exact hpq
  | inr hr =>
    have hpr : p ∧ r := ⟨hp, hr⟩
    apply Or.inr
    exact hpr

-- Если написать have : p ∧ q := ... или have := ...,
-- то эта гипотеза получит название this.
-- Тип тоже можно не писать, т.е. можно вот так:

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  cases hqr with
  | inl hq =>
    have : p ∧ q := And.intro hp hq -- << Вот так
    apply Or.inl; exact this
  | inr hr =>
    have := And.intro hp hr -- << Вот так
    apply Or.inr; exact this

-- Тактика let похожа на have, но используется, чтобы
-- ввести какие-то локальные штуки (термы), в отличии от have,
-- которая нужна, чтобы вводить вводить вспомогательные утверждения (вместе с их доказательствами).
-- Разница между have и let:
--   have h : T := e  — вводит h : T в контекст как непрозрачную гипотезу;
--                      определение e не видно дальше (Lean "забывает" что h = e).
--   let a : T := e   — вводит a : T := e как прозрачное определение;
--                      Lean помнит что a разворачивается в e.
-- Используй let когда нужно вычислить конкретное значение и потом передать его
-- как свидетеля (например, в exists). Используй have для логических фактов.
example : ∃ x, x + 2 = 8 := by
  let a : Nat := 3 * 2 -- Тип тут можно было бы и не писать
  exists a

-- Тактические блоки можно определять не только с помощью точки ·
-- Это можно делать используя фигурные скобки.
-- { tacs } — альтернативный синтаксис для фокусировки на подцели.
-- Поведение то же что у ·, но фигурные скобки позволяют писать несколько
-- тактик в одной строке без переносов. Это скорее вопрос стиля.

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  { intro h; -- Тк есть перенос строки, то точка с запятой не обязательна.
    cases h.right;
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inl ⟨h.left, ‹q›⟩ }
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inr ⟨h.left, ‹r›⟩ } }
  { intro h;
    cases h;
    { show p ∧ (q ∨ r);
      rename_i hpq;
      exact ⟨hpq.left, Or.inl hpq.right⟩ }
    { show p ∧ (q ∨ r);
      rename_i hpr;
      exact ⟨hpr.left, Or.inr hpr.right⟩ } }

-- 5.5. Tactic Combinators

-- Простейший комбинатор тактик это ;
-- t₁; t₂ — выполни t₁, потом t₂ для первой текущей подцели.
-- Это последовательное применение, не ко всем подцелям.
example (p q : Prop) (hp : p) : p ∨ q := by
  apply Or.inl; assumption

-- Комбинатор <;> мы уже видели.
-- Это пиздато использовать, когда для всех подцелей,
-- которые мы получили после применения тактики
-- слева от комбинатора <;> можно применить тактику справа.
-- t₁ <;> t₂ — выполни t₁, затем примени t₂ ко ВСЕМ подцелям,
-- которые породила t₁. Если t₂ не справляется хотя бы с одной — ошибка.
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor <;> assumption

-- first | t₁ | t₂ | ... | tₙ
-- Комбинатор first пробует по очереди тактики t₁, t₂, ..., tₙ
-- пока не получится применить одну из них, либо фейлится,
-- если не получилось применить ни одну.
-- Это backtracking: если t₁ не сработала, состояние целей откатывается
-- и пробуется t₂. Так работает поиск нужной тактики без явного ветвления.

-- Хуёвины разделённые ; он считает за одно применение тактики.

example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption
--                       ^^ решает

example (p q : Prop) (hq : q) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption
--                       ^^ не решает               ^^ решает

example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr; assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r := by
  first | apply Or.inl; assumption | apply Or.inr; apply Or.inl; assumption
example (p q r : Prop) (hq : q) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

-- Комбинатор try t выполняет тактику t и завершается всегда без ошибки.
-- По сути try t = first | t | skip, где тактика skip ничего не делает.
-- Используется когда хочешь применить тактику "если получится",
-- не прерывая доказательство при неудаче.

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption

-- Repeat (try t) will loop forever
-- Важно: repeat (try t) зациклится, потому что try t никогда не фейлится,
-- а repeat останавливается только при неудаче внутренней тактики.

-- Комбинатор all_goals t применяет тактику t ко всем подцелям.
-- Отличие от <;>: all_goals применяется к ТЕКУЩИМ подцелям,
-- а не только к тем, что породила предыдущая тактика.
-- all_goals фейлится, если t не удалась хотя бы для одной подцели.
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption

-- Комбинатор any_goals t завершается успехом, если удалось применить
-- тактику t хотя бы к одной из текущих подцелей.
-- Это почти эквивалентно all_goals.
-- any_goals tac = all_goals try tac, за исключением того, что
-- any_goals зафейлится, если не удалось применить тактику
-- хотя бы к одной цели/подцели.
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption

-- Благодаря эти комбинторам, можно в одну строчку раскидать
-- на конъюнкты по подцелям эту одну большую конъюнкцию.
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
  p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption

-- Можно ужать это док-во до одной строчки.
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))

-- Комбинатор focus изолирует влияние тактики.
-- focus (all_goals t) = t

-- 5.6. Rewriting

-- Тактика rw (rewrite) переписывает цель, используя уравнение.
-- rw [h] где h : a = b — заменяет первое вхождение a на b в цели.
-- rw [← h] где h : a = b — заменяет b на a (переписывание справа налево).
-- rw [h₁, h₂, ...] — применяет переписывания последовательно одно за другим.
-- rw [h] at hyp — переписывает не в цели, а в гипотезе hyp.
-- Важно: rw ищет синтаксически точное вхождение, не модульно унификации.
-- После каждого rw тактика пытается закрыть цель через rfl — это удобно
-- когда переписывание сразу приводит к рефлексивности.

section
variable (k : Nat) (f : Nat → Nat)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- replace k with 0
  rw [h₁] -- replace f 0 with 0

example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
  rw [h hq]; assumption

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂, h₁]

end

section
variable (a b : Nat) (f : Nat → Nat)

-- rw [← h] — переписывание справа налево.
-- Если h : a = b, то rw [← h] заменяет b на a в цели.
-- Здесь h₁ : a = b, поэтому rw [← h₁] заменяет b на a в цели f b = 0,
-- получая f a = 0, что совпадает с h₂.
example (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁, h₂]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]

example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]
end

section
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t
end

-- 5.7. Using the Simplifier

-- Тактика simp — автоматический упроститель.
-- Она применяет набор лемм (помеченных атрибутом @[simp]) до тех пор,
-- пока дальнейшее упрощение невозможно (нормальная форма).
-- simp умеет: раскрывать определения, применять арифметику, логику,
--             переписывать по леммам равенства, упрощать if-then-else и т.д.
-- simp [h₁, h₂] — добавляет h₁, h₂ к стандартному набору simp-лемм.
-- simp only [h₁, h₂] — использует только указанные леммы, игнорируя все стандартные.
-- simp [-h] — запрещает использование леммы h.
-- simp at hyp — применяет к гипотезе вместо цели.
-- simp at * — применяет ко всем гипотезам и к цели.
-- simp [*] — добавляет все локальные гипотезы к набору лемм.
example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption

section
open List

example (xs : List Nat)
        : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
  simp

example (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
  simp [Nat.add_comm]
--        ^^^ По-умолчанию simp использовует все леммы/теоремы,
--            помеченные атрибутом simp. А в квадратных скобках мы можем
--            перечислить дополнительные леммы, которые мы хотим, чтобы
--            использовала тактика simp.
example (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
  simp
  rw [Nat.add_comm]

example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption
end

section
-- attribute [local simp] lemma — помечает lemma атрибутом simp,
-- но только в пределах текущей секции/пространства имён.
-- Это позволяет временно добавить леммы в набор simp
-- без загрязнения глобального состояния.
-- Здесь добавляем законы коммутативности и ассоциативности умножения и сложения,
-- чтобы simp мог автоматически приводить выражения к нормальной форме.
attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

-- Звёздочка/вайлдкарт астериск указывает на то, что
-- мы хотим применить simp ко всем гипотезам из контекста и к цели.
example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp at *; assumption

example (x y z : Nat) (p : Nat → Prop)
        (h₁ : p (1 * x + y)) (h₂ : p (x * z * 1))
        : p (y + 0 + x) ∧ p (z * x) := by
  simp at * <;> constructor <;> assumption

example (w x y z : Nat) (p : Nat → Prop)
        : x * y + z * w * x = x * w * z + y * x := by
  simp

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp; simp at h; assumption

end

def f (m n : Nat) : Nat :=
  m + n + m

-- Тут выполнит указанные переписывания + развернёт определение f + упростит.
example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h, ←h', f]

-- Идиоматичный ход это упростить цель, используя локальные гипотезы.
variable (k : Nat) (f : Nat → Nat)
example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [h₂, h₁]

-- Если написать [*], то simp будет использовать все гипотезы,
-- которые доступны в локальном контексте.
variable (k : Nat) (f : Nat → Nat)
example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*]

-- Используй все + коммутативность сложения.
example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  simp [*, Nat.add_comm]

-- Тактика simp умеет переписывать и высказывания.
example (p q : Prop) (hp : p) : p ∧ q ↔ q := by simp [*]
example (p q : Prop) (hp : p) : p ∨ q := by simp [*]
example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by simp [*]

section
set_option linter.unusedVariables false

example (u w x x' y y' z : Nat) (p : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at * -- Такая запись используется для упрощения всех гипотез и цели.
  simp [*]  -- Используем упрощённые гипотезы для доказательства цели.
end

namespace Whatever
open List

def mk_symm (xs : List α) :=
  xs ++ xs.reverse

-- Можешь применить локально.
-- attribute [local simp] mk_symm

theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp [reverse_mk_symm] at h; assumption

end Whatever

section
open List

def mk_symm (xs : List α) :=
 xs ++ xs.reverse

-- @[simp] перед теоремой — это атрибут, который помечает теорему как simp-лемму
-- глобально (на уровне всего файла и любого кода, который его импортирует).
-- После этого simp будет автоматически применять эту теорему без явного указания.
-- Это удобно для "очевидных" упрощений, которые хочется применять везде.
-- Альтернатива: attribute [simp] reverse_mk_symm — добавить атрибут после определения.
@[simp] theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

-- attribute [simp] reverse_mk_symm

-- Сужает скоуп до текущего файла или секции (или неймспейса?).
-- attribute [local simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

end

section
example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

-- Можно запрещать использовать конкретные леммы.
-- simp [-lemma] — запрещает использование lemma, оставляя всё остальное.
-- Это полезно когда стандартная simp-лемма мешает (например, упрощает
-- в нежелательном направлении) и ты хочешь исключить только её.
example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp [-reverse_mk_symm] at h; assumption

-- Или можно вообще исключать все, кроме указанного в скобках списка,
-- c помощью модификатора only.
-- simp only [lemmas] — отключает все стандартные simp-леммы и
-- использует только явно перечисленные. Это делает доказательство
-- более предсказуемым и устойчивым к изменениям в библиотеке.
example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp only [List.reverse_append] at h; assumption
end

section
-- Модификатор +contextual говорит simp'у:
-- используй тот факт, что x = 0, когда упрощаешь ветку then
-- и тот факт что, x ≠ 0, когда упрощаешь ветку else.
-- Иначе говоря: simp +contextual учитывает локальный контекст каждой ветки
-- if-then-else или match, используя условие как дополнительную гипотезу.
-- Без +contextual simp пытается доказывать каждую ветку без учёта условия.
example : if x = 0 then y + x = y else x ≠ 0 := by
  simp +contextual

example : ∀ (x : Nat) (h : x = 0), y + x = y := by
  simp +contextual
end

-- Ещё полезный модификатор +arith,
-- позволяет упрощать арифметические выражения.
-- simp +arith подключает линейную арифметику (похожую на omega),
-- что позволяет доказывать неравенства и равенства с конкретными числами.
example : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  simp +arith

-- 5.8. Split Tactic

def f₀ (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

-- Тактика split разбивает match по кейсам.
-- Сколько было веток в match, столько будет и кейсов.
-- То же и для if-then-else.
-- split полезна когда функция определена через match и нужно
-- доказать что-то о ней: split раскрывает все случаи матча
-- и ты доказываешь каждый отдельно.
-- Здесь simp [f₀] раскрывает определение f₀, после чего
-- в цели появляется match-выражение, которое split разбивает на 4 ветки.
-- В первых трёх ветках одна из переменных равна 5, а у нас есть гипотеза что ≠5 —
-- противоречие закрывается через contradiction.
-- Четвёртая ветка — f₀ возвращает 1, цель 1 = 1 закрывается через rfl.
example (x y z : Nat)
        : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f₀ x y w = 1 := by
  intros
  simp [f₀] -- Раскрывает определение f₀
  split
  · contradiction
  · contradiction
  · contradiction
  · rfl

example (x y z : Nat) :
  x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w →
  f₀ x y w = 1 := by
  intros; simp [f₀]; split <;> first | contradiction | rfl

def g (xs ys : List Nat) : Nat :=
  match xs, ys with
  | [a, b], _ => a+b+1
  | _, [b, _] => b+1
  | _, _      => 1

example (xs ys : List Nat) (h : g xs ys = 0) : False := by
  simp [g] at h; split at h <;> simp +arith at h

-- 5.9. Extensible Tactics

-- Lean 4 позволяет определять собственные тактики через макросы.
-- Это не просто алиасы: тактику можно расширять по частям через macro_rules.
-- Каждое новое macro_rules добавляет ещё одну "ветку" к тактике.
-- При вызове тактики Lean пробует все ветки по порядку (от последней к первой)
-- пока одна не сработает — это встроенный механизм backtracking.

namespace ExtensibleTactics
  -- Создадим свою тактику.
  -- syntax "triv" : tactic — объявляет новый синтаксис (лексему "triv")
  -- в категории tactic. Пока что это просто декларация, не реализация.
  syntax "triv" : tactic

  -- Собственная тактика это по сути набор существующих тактик,
  -- они называются расширениями.

  -- Пока что наша тактика triv это просто алиас для assumption.
  macro_rules
    | `(tactic| triv) => `(tactic| assumption)

  example (h : p) : p := by
    triv

  -- Пока что не получится доказать рефлексивность с помощью нашей
  -- самодельной тактики triv.

  -- Error: Tactic `assumption` failed
  -- example (x : α) : x = x := by
  --   triv

  -- Второе использование macro_rules расширяет нашу тактику
  -- рефлексивностью отношения равенства.
  -- Интепретатор тактик будет пробовать все такие "расширения"
  -- нашей тактики пока не сработает какая-то из них.
  macro_rules
    | `(tactic| triv) => `(tactic| rfl)

  -- Вот теперь доказывается.
  example (x : α) : x = x := by
    triv

  example (x : α) (h : p) : x = x ∧ p := by
    apply And.intro <;> triv

  -- Можно добавлять рекурсивные расширения.
  macro_rules | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

  -- Теперь все доказывается тривиально :)
  example (x : α) (h : p) : x = x ∧ p := by
    triv

end ExtensibleTactics

-- 5.10. Exercises

-- Сделай столько, сколько по кайфу

-- Propositions and Proofs

namespace Exercises_1
  variable (p q r : Prop)

  -- 1.a
  example : p ∨ q ↔ q ∨ p := by
    apply Iff.intro
    · intro h
      apply Or.elim h
      · intro ev_p
        apply Or.inr
        exact ev_p
      · intro ev_q
        apply Or.inl
        exact ev_q
    · intro h
      apply Or.elim h
      · intro ev_q
        apply Or.inr
        exact ev_q
      · intro ev_p
        apply Or.inl
        exact ev_p

  -- 1.b
  example : p ∨ q ↔ q ∨ p := by
    constructor
    repeat
      intro
      | Or.inl p => exact Or.inr p
      | Or.inr q => exact Or.inl q

  -- 1.c
  example : p ∨ q ↔ q ∨ p := by
    constructor
    repeat intro h; cases h <;> first
    | apply Or.inl; assumption
    | apply Or.inr; assumption

  -- 2.a
  example : p ∧ q ↔ q ∧ p := by
    apply Iff.intro
    · intro h
      apply And.intro
      · exact h.right
      · exact h.left
    · intro h
      constructor
      case left => exact h.right
      case right => exact h.left

  -- 2.b
  example : p ∧ q ↔ q ∧ p := by
    constructor
    · intro h
      constructor
      case mp.right => exact h.left
      case mp.left => exact h.right
    · intro ⟨hq, hp⟩
      exact ⟨hp, hq⟩

  -- 2.c
  example : p ∧ q ↔ q ∧ p := by
    constructor
    · intro | ⟨hp, hq⟩ => exact ⟨hq, hp⟩
    · intro | ⟨hq, hp⟩ => exact ⟨hp, hq⟩

  -- 2.d
  example : p ∧ q ↔ q ∧ p := by
    apply Iff.intro
    · intro h
      cases h
      rename_i hp hq; exact ⟨hq, hp⟩
    · intro h
      cases h with
      | intro hq hp => exact ⟨hp, hq⟩

  -- 2.e
  example : p ∧ q ↔ q ∧ p := by
    apply Iff.intro
    repeat
      intro h
      cases h <;> constructor; repeat assumption

  -- 2.f
  example : p ∧ q ↔ q ∧ p := by
    constructor <;> (intro h; cases h; constructor <;> assumption)

  -- И intro и саses могут распаковать конструкторы
  -- любого индуктивного типа, но ведут себя чуть по-разному.

  -- 3.a
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
    apply Iff.intro
    · intro ⟨⟨hp, hq⟩, hr⟩; exact ⟨hp, ⟨hq, hr⟩⟩
    · intro ⟨hp, ⟨hq, hr⟩⟩; exact ⟨⟨hp, hq⟩, hr⟩

  -- 3.b
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
    constructor
    · intro | ⟨⟨hp, hq⟩, hr⟩ => exact ⟨hp, ⟨hq, hr⟩⟩
    · intro | ⟨hp, ⟨hq, hr⟩⟩ => exact ⟨⟨hp, hq⟩, hr⟩

  -- 4.a
  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
    apply Iff.intro
    · intro h
      cases h with
      | inl h_pq =>
        cases h_pq with
        | inl ev_p =>
          apply Or.inl
          exact ev_p
        | inr ev_q =>
          apply Or.inr; apply Or.inl
          assumption
      | inr h_r =>
        let h_qr : q ∨ r := Or.inr h_r
        exact Or.inr h_qr
    · intro h
      cases h
      · rename_i h_p
        exact (Or.inl (Or.inl h_p))
      · rename_i h_qr
        match h_qr with
        | Or.inl ev_q =>
          have h_pq : (p ∨ q) := Or.inr ev_q
          exact Or.inl h_pq
        | Or.inr ev_r => exact Or.inr ev_r

  -- 5.a
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
    constructor
    · intro ⟨h_p, h_qr⟩
      cases h_qr with
      | inl h_q =>
        apply Or.inl; exact ⟨h_p, h_q⟩
      | inr h_r =>
        apply Or.inr; exact ⟨h_p, h_r⟩
    · intro
      | Or.inl h_pq =>
        have : q ∨ r := Or.inl h_pq.right
        exact ⟨h_pq.left, this⟩
      | Or.inr h_pr =>
        have : q ∨ r := Or.inr h_pr.right
        exact ⟨h_pr.left, this⟩

  -- 5.b
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
    constructor
    · intro ⟨h_p, h_qr⟩
      cases h_qr <;> first
      | (apply Or.inl; apply And.intro) <;> assumption
      | (apply Or.inr; apply And.intro) <;> assumption
    · intro
      | Or.inl ⟨h_p, h_q⟩ =>
        have : q ∨ r := Or.inl h_q
        exact ⟨h_p, this⟩
      | Or.inr ⟨h_p, h_r⟩ =>
        constructor
        · assumption
        · first
          | apply Or.inl; assumption
          | apply Or.inr; assumption

  -- 6.a
  example : (p → (q → r)) ↔ (p ∧ q → r) := by
    constructor
    · intro h ⟨h_p, h_q⟩; apply h <;> assumption
    · intro h h_p h_q; exact h ⟨h_p, h_q⟩

  -- 7.a
  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
    constructor
    · intro h
      constructor
      · intro ev; exact h (Or.inl ev)
      · intro ev; exact h (Or.inr ev)
    · intro ⟨h_pr, h_qr⟩
      intro
      | Or.inl h_p => exact h_pr h_p
      | Or.inr h_q => exact h_qr h_q

  -- 7.b
  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
    constructor
    · intro h; constructor <;> intro ev
      repeat first | apply h (Or.inl ev) | apply h (Or.inr ev)
    · intro ⟨h_pr, h_qr⟩ h_pq; apply Or.elim h_pq <;> assumption

  -- 8.a
  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
    sorry

  -- 9.a
  example : ¬p ∨ ¬q → ¬(p ∧ q) := by
    sorry

  -- 10.a
  example : ¬(p ∧ ¬p) := by
    sorry

  -- 11.a
  example : p ∧ ¬q → ¬(p → q) := by
    sorry

  -- 12.a
  example : ¬p → (p → q) := by
    sorry

  -- 13.a
  example : (¬p ∨ q) → (p → q) := by
    sorry

  -- 14.a
  example : p ∨ False ↔ p := by
    sorry

  -- 15.a
  example : p ∧ False ↔ False := by
    sorry

  -- 16.a
  example : (p → q) → (¬q → ¬p) := by
    sorry
end Exercises_1

namespace ExercisesClassical_1
  open Classical
  -- open Classical открывает доступ к законам классической логики:
  --   em  : ∀ p : Prop, p ∨ ¬p  (закон исключённого третьего)
  --   byContradiction : (¬p → False) → p
  -- Без открытия Classical эти законы недоступны — логика конструктивна.
  -- Конструктивная логика не принимает исключённое третье как аксиому,
  -- потому что нет алгоритма который для любого p даёт его доказательство или опровержение.

  variable (p q r : Prop)

  -- 17.a
  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
    sorry

  -- left  ~ apply Or.inl
  -- right ~ apply Or.inr

  -- 18.a
  example : ¬(p ∧ q) → ¬p ∨ ¬q := by
    intro h_npq
    cases (em p) with
    | inl h_p =>
      apply Or.elim (em q)
      · intro h_q
        have : p ∧ q := ⟨h_p, h_q⟩
        exact absurd this h_npq
      · intro; right; assumption
    | inr h_np => left; assumption

  -- Пользуйся:
  -- 1. simp?
  -- 2. apply?
  -- 3. show_term {tactic}

  -- 19.a
  example : ¬(p → q) → p ∧ ¬q := by
    intro h_npq
    -- Как узнать что сделала simp:
    -- simp? at h_npq
    -- simp only [not_imp] at h_npq; assumption
    -- exact Decidable.not_imp_iff_and_not.mp h_npq
    exact not_imp.mp h_npq

  -- 20.a
  example : (p → q) → (¬p ∨ q) := by
    apply Or.elim (em p)
    · intro h_p h_pq
      right
      exact h_pq h_p
    · intro h_np h_pq
      left
      exact h_np

  -- 21.a
  example : (¬q → ¬p) → (p → q) := by
    intro h h_p
    cases em q with
    | inl h_q => assumption
    | inr h_nq =>
      have : ¬ p := h h_nq
      exact absurd h_p this

  -- 22.a
  example : p ∨ ¬p := by
    apply em

  -- 23.a
  example : (((p → q) → p) → p) := by
    intro h
    cases em (p → q) with
    | inl h_pq => exact h h_pq
    | inr h_npq =>
      -- simp only [not_imp] at h_npq
      rw [not_imp] at h_npq
      exact h_npq.left

end ExercisesClassical_1

namespace ExercisesNonClassical_1
  variable (p : Prop)

  -- 24.a
  -- TODO: Prove without using classical logic.
  example : ¬(p ↔ ¬ p) := by
    apply iff_not_self

end ExercisesNonClassical_1

-- Quantifies and Equality

namespace Exercises_2
  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  -- 25.a
  example : (∃ _ : α, r) → r := by
    intro h
    cases h with
    | intro _ h_r => exact h_r

  -- 25.b
  example : (∃ _ : α, r) → r := by
    intro ⟨x, h_r⟩; assumption

  -- 26.a
  example (a : α) : r → (∃ _ : α, r) := by
    intros; exists a

  -- 27.a
  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
    constructor
    · intro
      | Exists.intro x h_pxr =>
        exact ⟨⟨x, h_pxr.left⟩, h_pxr.right⟩
    · intro ⟨⟨x, h_px⟩, h_r⟩
      exists x

  -- 28.a
  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
    constructor
    · intro ⟨x, h⟩
      cases h with
      | inl h_px => left; exists x
      | inr h_qx => right; exists x
    · intro h
      cases h with
      | inl h_epx =>
        cases h_epx with
        | intro x h_px => exists x; left; exact h_px
      | inr h_eqx =>
        cases h_eqx with
        | intro x h_qx => exists x; right; exact h_qx

  -- 28.b
  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
    constructor
    · intro ⟨x, h⟩
      cases h with
      | inl h_px => left; exists x
      | inr h_qx => right; exists x
    · intro h
      cases h with
      | inl h_epx =>
        cases h_epx with
        | intro x h_px =>
          exists x; left; exact h_px
      | inr h_eqx =>
        cases h_eqx with
        | intro x h_qx =>
          exists x; right; exact h_qx

  -- 29.a
  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
    constructor
    · intro h
      rw [not_exists]
      simp only [Classical.not_not]
      assumption
    · intro h
      rw [not_exists] at h
      simp only [Classical.not_not] at h
      assumption

  -- 29.b
  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
    constructor <;> repeat
    intro h
    rw [not_exists] at *
    simp only [Classical.not_not] at *
    assumption

  -- 29.c
  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
    simp

  -- 30.a
  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
    constructor
    repeat
      intro h
      rw [← not_exists] at *
      simp only [Classical.not_not] at *
      assumption

  -- 31.a
  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
    constructor
    repeat
      intro h
      rw [not_exists] at *
      assumption

  -- 32.a
  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
    sorry

  -- 33.a
  example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
    sorry

  -- 34.a
  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
    sorry

  -- 35.a
  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
    sorry

  -- 36.a
  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
    sorry

  -- 37.a
  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
    sorry

  -- 38.a
  -- В этом упражнении постарайся понять почему обратное недоказуемо.
  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
    sorry

  -- 39.a
  -- Обратное не доказуемо потому что из разных иксов ты
  -- можешь выбрать какой-то один, а наборот хуй там утонул.
  example : ∀ x, p x ∨ q x → (∀ x, p x) ∨ (∀ x, q x) := by
    sorry -- Нельзя доказать

  -- 40.a
  example : α → ((∀ x : α, r) ↔ r) := by
    sorry

  open Classical

  -- 41.a
  -- Одно из направлений требует классической логики.
  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
    sorry

  -- 42.a
  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
    sorry

  -- 43.a
  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
    sorry

  -- Парадокс брадобрея (одна из интерпретаций парадокса Рассела)

  variable (men : Type) (barber : men)
  variable (shaves : men → men → Prop)

  #check ((and_not_self_iff (shaves barber barber)).mp :
    shaves barber barber ∧ ¬shaves barber barber → False)

  theorem paradox : ¬(a ↔ ¬a) := iff_not_self

  -- 44.a
  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
    apply paradox
    exact h barber

end Exercises_2

namespace Exercises_3

  -- 45.a
  -- Получить доказательство в одну строчку.
  example (p q r : Prop) (hp : p)
          : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
    sorry

end Exercises_3
