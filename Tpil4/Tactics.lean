theorem test₀ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

-- Можно использовать apply везде, где сработает exact,
-- но если можешь использовать exact, то лучше используй её.

-- Пруф-терм можно посмотеть вот так
#print test₀

-- Применение составных выражений
theorem test₁ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  apply And.intro hq hp

-- Пруф-терм получится такой же
#print test₁

-- Можно применять сразу несколько тактик на одной строке,
-- разделяя точкой с запятой
theorem test₂ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp

-- Заметь как называются кейсы (case left, case right) при применении
-- тактики apply And.intro в самом верхнем примере (test₀).
-- Это тэги, линь берёт их из названий параметров в определении And.intro.
--
-- Так можно и самому структурировать свой доказательства,
-- cast <tag> => <tactics>.

theorem test₃ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

-- Когда мы попадает в конкретный кейс, остальные прячутся,
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

example (α : Type) : α → α := by
  intro a
  exact a

example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x
  -- rfl

variable (α : Type)

-- Тактика intro позволяет разбирать и
-- затаскивать в контекст гипотезу по кусочкам.
example (q p : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨x, hpx, hqx⟩
  exact ⟨x, hqx, hpx⟩

-- Паттерн-матчинг с помощью intro.
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
  assumption     -- Унифицирует case h₁: x = ?b, используя h₁: x = y
  -- Остаётся доказать case h₂ : ?b = w, т.е. h₂ : y = w
  apply Eq.trans -- y = ?h₂.b → ?h₂.b = w → y = w
  assumption     -- Унифицирует case h₂.h₁: y = ?h₂.b, используя h₂ : y = z
  assumption     -- Унификация z = w с помощью h₃

-- Тактика intros забирает в конеткст всё и сама выбирает имена.
-- На сгенерированные имена ты никак не можешь ссылаться.
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption

-- Это можно обойти комбинатором unhygienic.
example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1

-- А ещё можно переименовать последние сгенерированные
-- имена с помощью тактики rename_i.
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  rename_i h1 h2 -- Переименовать 2 из 3-х последних гипотез в контексте.
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1

-- Можно использовать rfl для решения любых рефлексивностей в целях.
-- Работает для аргументов равных по определению.
-- Например можно написать rfl вместо Eq.refl.
example (y : Nat) : (λ x : Nat => 0) y = 0 := by
  rfl

-- repeat
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption

-- Тактика revert является обратной к intro.
-- Она втаскивает из контекста что-либо в цель.
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
-- В данном случае это гипотеза h.
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
-- используюя тактику generalize. Обобщение короче.
example : 3 = 3 := by
  generalize 3 = x
  revert x
  intro y
  rfl

-- Обобщить-то можно что хочешь, а доказать можно не всё.
example : 2 + 3 = 5 := by
  generalize 3 = x
  sorry

-- Свои обобщения можно сохранять в контексте как гипотезы.
example : 2 + 3 = 5 := by
  generalize h : 3 = x
  rw [← h]

-- 5.3. More Tatics

-- Тактика cases по сути это паттерн-матичинг для типа-суммы
-- (вообще для любого индуктивного типа).
-- В примере ниже использование cases эквивалентно Or.elim.
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq
-- ^ Порядок не важен

-- Та же фигня, только в тактик-мод (без with).
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption

-- Использование cases удобно в частности,
-- если можно решить сразу несколько подцелей какой-то одной тактикой.
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption

-- Можно использовать вот такой комбинатор тактик tac1 <;> tac2,
-- чтобы применить тактику tac2 ко всем подцелям, которые
-- производит тактика tac1.
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption

-- Хорошо комбинировать cases с тактикой case и
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
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with -- Появляется x и px в контексте
  | intro x px => constructor; apply Or.inl; exact px

-- Применение constructor к ∃ x, p x распаковывает
-- конструктор этого квантора и создаёт в цели метапеременную вместо x.
-- Дальше, когда мы показываем exact px, то ?x унифицируется с x.
-- Если хочешь избежать появления этой метапеременной и такой
-- типа поздней унификации, то можешь сразу показать что такое х,
-- c помощью exists x.

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px

-- Ещё пример.
example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x
--     ^^^ Тут когда мы пишем exists x, линь вроде как
-- ищет в контексте требуемые в цели гипотезы.

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
example (P : Nat → Prop)
  (h₀ : P 0) (h₁ : ∀ n, P (succ n))
  (m : Nat) : P m := by
cases m with
| zero => exact h₀
| succ m' => exact h₁ m'

-- Тактика contradiction сама ищет в контексте гипотезы
-- противоречащие цели.
example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction

end

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
-- не именую гипотезу, тк мы её сразу же хотим разбирать.
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
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  exact
    have hp  : p := h.left
    have hqr : q ∨ r := h.right
    -- Вот тут show это не просто "комментарий",
    -- тут именно требуется показать какой терм мы конструируем.
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩

-- Более наглядный пример.
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

-- Можно использовать show как "комментарий".
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
example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl

-- С помощью тактики have можно вводить свои подцели в любой момент.
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

-- Если написать просто have : p ∧ q,
-- то эта гипотеза получит название this.
-- Тип тоже можно не писать, т.е. можно вот так:

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  cases hqr with
  | inl hq =>
    have := And.intro hp hq -- << Вот так
    apply Or.inl; exact this
  | inr hr =>
    have := And.intro hp hr -- << Вот так
    apply Or.inr; exact this

-- Тактика let похожа на have, но используется, чтобы
-- ввести какие-то локальные штуки (термы), в отличии от have,
-- которая нужна, чтобы вводить вводить вспомогательные утверждения (вместе с их доказательствами).
example : ∃ x, x + 2 = 8 := by
  let a : Nat := 3 * 2 -- Тип тут можно было бы и не писать
  exists a

-- Тактические блоки можно определять не только с помощью точки ·
-- Это можно делать используя фигурные скобки.

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

-- 5.5. Tatic Combinators

-- Простейший комбинатор тактик это ;
example (p q : Prop) (hp : p) : p ∨ q :=
  by apply Or.inl; assumption

-- Комбинатор <;> мы уже видели.
example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption
