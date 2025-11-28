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

-- Можно заменять ggпроизвольные выражения в цели,
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
-- Только cases создаёт не именованные гипотезы.
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
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

-- Тактика contradiction сама ищет в контексте
-- гипотезы противоречащие цели.
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
example (p q : Prop) (hp : p) : p ∨ q := by
  apply Or.inl; assumption

-- Комбинатор <;> мы уже видели.
-- Это пиздато использовать, когда для всех подцелей,
-- которые мы получили после применения тактики
-- слева от комбинатора <;> можно применить тактику справа.
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor <;> assumption

-- first | t₁ | t₂ | ... | tₙ
-- Комбинатор first пробует по очереди тактики t₁, t₂, ..., tₙ
-- пока не получится применить одну из них, либо фейлится,
-- если не получилось применить ни одну.

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
-- По сути try t = first | t | skip, где тактика skip ничего не делает,

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption

-- Repeat (try t) will loop forever

-- Комбинатор all_goals t применяет тактику t ко всем подцелям.
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption

-- Комбинатор any_goals t завершается успехом, если удалось применить
-- тактику t хотя бы к одной из текущих подцелей.
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
example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp [-reverse_mk_symm] at h; assumption

-- Или можно вообще исключать все, кроме указанного в скобках списка,
-- c помощью модификатора only.
example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp only [List.reverse_append] at h; assumption
end

section
-- Модификатор +contextual говорит simp'у:
-- используй тот факт, что x = 0, когда упрощаешь ветку then
-- и тот факт что, x ≠ 0, когда упрощаешь ветку else
example : if x = 0 then y + x = y else x ≠ 0 := by
  simp +contextual

example : ∀ (x : Nat) (h : x = 0), y + x = y := by
  simp +contextual
end

-- Ещё полезный модификатор +arith,
-- позволяет упрощать арифметические выражения.

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

namespace ExtensibleTactics
  -- Создадим свою тактику.
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
    sorry
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
    sorry

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
    sorry

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
