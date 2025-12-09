namespace UniversalQuantifier
  example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
      λ h : ∀ x : α, p x ∧ q x =>
      λ y : α =>
      show p y from (h y).left

  example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
      λ h : ∀ x : α, p x ∧ q x =>
      λ z : α =>
      show p z from And.left (h z)

  namespace Transitivity
    variable (α : Type) (r : α → α → Prop)
    variable (trans_r : ∀ x y z, r x y → r y z → r x z)

    variable (a b c : α)
    variable (h_ab : r a b) (h_bc : r b c)

    #check trans_r
    #check trans_r a b c
    #check trans_r a b c h_ab
    #check trans_r a b c h_ab h_bc
  end Transitivity

  namespace TransitivityImplicitArgs
    variable (α : Type) (r : α → α → Prop)
    variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

    variable (a b c : α)
    variable (h_ab : r a b) (h_bc : r b c)

    #check trans_r
    #check trans_r h_ab
    #check trans_r h_ab h_bc
  end TransitivityImplicitArgs

  namespace Reasoning
    variable (α : Type) (r : α → α → Prop)
    variable (refl_r : ∀ x, r x x)
    variable (symm_r : ∀ {x y}, r x y → r y x)
    variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

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

  example : a = d :=
    Eq.trans (Eq.trans h_ab (Eq.symm h_cb)) h_cd

  -- projection notation
  example : a = d := (h_ab.trans h_cb.symm).trans h_cd

  namespace PowerOfReflexivity
    variable (α β : Type)

    example (f : α → β) (a : α) : (λ x => f x) a = f a := Eq.refl (f a)
    example (f : α → β) (a : α) : (λ x => f x) a = f a := Eq.refl _
    example (f : α → β) (a : α) : (λ x => f x) a = f a := rfl

    example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
    example (a : α) (b : β) : (a, b).1 = a := rfl

    example : 2 + 3 = 5 := Eq.refl _
    example : 2 + 3 = 5 := rfl

  end PowerOfReflexivity

  namespace Substitution
    variable (α : Type)

    example (α : Type) (a b : α) (p : α → Prop)
      (h1 : a = b) (h2 : p a) : p b := Eq.subst h1 h2

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
    example : f a = f b := congrArg f h₁
    -- Позволяет сделать замену функции на другую ей равную.
    example : f a = g a := congrFun h₂ a

    example : f a = g b := congr h₂ h₁
  end Congr

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
  variable (a b c d e : Nat)

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

  theorem T₃
    (h₁ : a = b)
    (h₂ : b = c + 1)
    (h₃ : c = d)
    (h₄ : e = 1 + d) :
    a = e := by
  rw [h₁, h₂, h₃, Nat.add_comm, h₄]

  theorem T₄
    (h₁ : a = b)
    (h₂ : b = c + 1)
    (h₃ : c = d)
    (h₄ : e = 1 + d) :
    a = e := by
  simp [h₁, h₂, h₃, Nat.add_comm, h₄]

  -- Можно комбинировать разные отношения.
  example (h₁ : a = b) (h₂ : b ≤ c) (h₃ : c + 1 < d) : a < d :=
    calc
      a = b := h₁
      b < b + 1 := Nat.lt_succ_self b
      b + 1 ≤ c + 1 := Nat.succ_le_succ h₂
      c + 1 < d := h₃

  -- Можно определять свои транзитивные отношения и
  -- сообщать Lean как с ними работать, реализуя тайпкласс Trans.

  def divides (x y : Nat) : Prop :=
    ∃ k, k * x = y

  def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
    let ⟨k₁, d₁⟩ := h₁
    let ⟨k₂, d₂⟩ := h₂
    ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

  def divides_mul (x : Nat) (k : Nat) : divides x (k * x) :=
    ⟨k, rfl⟩

  instance : Trans divides divides divides where
    trans := divides_trans

  example (h₁ : divides x y) (h₂ : y = z) : divides x (2 * z) :=
    calc
      divides x y := h₁
      y = z       := h₂
      divides z (2 * z) := divides_mul ..

  infix:50 " | " => divides

  example (h₁ : x | y) (h₂ : y = z) : x | (2 * z) :=
    calc
      x | y       := h₁
      y = z       := h₂
      z | (2 * z) := divides_mul ..

end CalculationalProofs

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

  example : ∃ x : Nat, x > 0 :=
    have h : 1 > 0 := Nat.zero_lt_succ 0
    Exists.intro 1 h

  example (x : Nat) (h : 0 < x) : ∃ y, y < x :=
    Exists.intro 0 h

  example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
    Exists.intro y ⟨hxy, hyz⟩

  #check @Exists.intro

  example : ∃ x : Nat, x > 0 :=
    have h : 1 > 0 := Nat.zero_lt_succ 0
    ⟨1, h⟩

  example (x : Nat) (h : 0 < x) : ∃ y, y < x :=
    ⟨0, h⟩

  example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
    ⟨y, hxy, hyz⟩
    -- ⟨y, ⟨hxy, hyz⟩⟩

  section
  variable (g : Nat → Nat → Nat)

  theorem gex1 (hg : g 0 0 = 0) : ∃ x, g x x = x := ⟨0, hg⟩
  theorem gex2 (hg : g 0 0 = 0) : ∃ x, g x 0 = x := ⟨0, hg⟩
  theorem gex3 (hg : g 0 0 = 0) : ∃ x, g 0 0 = x := ⟨0, hg⟩
  theorem gex4 (hg : g 0 0 = 0) : ∃ x, g x x = 0 := ⟨0, hg⟩

  -- Показывать неявные аргументы.
  set_option pp.explicit true

  #print gex1
  #print gex2
  #print gex3
  #print gex4

  end

  section
  variable (α : Type) (p q : α → Prop)

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    Exists.elim h
      (λ w =>
        λ hw : p w ∧ q w =>
          show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)


  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    match h with
    | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    match h with
    | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    match h with
    | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    let ⟨w, hpw, hqw⟩ := h
    ⟨w, hqw, hpw⟩

  example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
    fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

  end

  def IsEven (a : Nat) := ∃ b, a = 2 * b

  variable (a b : Nat)

  theorem even_plus_even (h₁ : IsEven a) (h₂ : IsEven b) : IsEven (a + b) :=
    Exists.elim h₁ (λ w₁ (hw₁ : a = 2 * w₁) =>
      Exists.elim h₂ (λ w₂ (hw₂ : b = 2 * w₂) =>
        Exists.intro (w₁ + w₂)
          (calc a + b
            _ = 2 * w₁ + 2 * w₂ := by rw [hw₁, hw₂]
            _ = 2 * (w₁ + w₂)   := by rw [Nat.mul_add]
            )))

  theorem even_plus_even₀ (h₁ : IsEven a) (h₂ : IsEven b) : IsEven (a + b) :=
    match h₁, h₂ with
    | ⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩ =>
      ⟨w₁ + w₂, by rw [hw₁, hw₂, Nat.mul_add]⟩

  theorem even_plus_even₁ : IsEven a → IsEven b → IsEven (a + b) :=
    λ ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ =>
      ⟨w₁ + w₂, by rw [hw₁, hw₂, Nat.mul_add]⟩

  section
  open Classical

  variable (α : Type)
  variable (p : α → Prop)

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

  example : (∃ _ : α, r) → r :=
    λ ⟨_, hx⟩ => hx

  example (a : α) : r → (∃ _ : α, r) :=
    λ h => ⟨a, h⟩

  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
    Iff.intro
      (λ ⟨x, h⟩ => ⟨⟨x, h.left⟩, h.right⟩)
      (λ ⟨⟨x, h⟩, r⟩ => ⟨x, ⟨h, r⟩⟩)

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

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    Iff.intro
      (λ h => λ ⟨x, h_npx⟩ => h_npx (h x))
      (λ h : ¬∃ x, ¬p x =>
        λ x : α => byContradiction
          (λ h_npx : ¬p x =>
            have h₀ : ∃ x, ¬p x := ⟨x, h_npx⟩
            show False from h h₀))

  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    Iff.intro
      (λ ⟨x, h_px⟩ =>
        λ h : ∀ (x : α), ¬p x => absurd h_px (h x))
      (λ h : ¬∀ (x : α), ¬p x => byContradiction
        (λ h₀ : ¬∃ x, p x =>
          have h_inv : ∀ (x : α), ¬p x :=
            λ x : α => sorry

          -- have x : α := sorry
          -- have h_px : p x := sorry
          -- have h₀_inv : ∃ x, p x := ⟨x, h_px⟩
          -- show False from h₀ h₀_inv
          show False from h h_inv))

  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    Iff.intro
      (λ h : ¬∃ x, p x =>
        λ x => sorry)
      (λ h => sorry)

  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry

  end

end ExistentialQuantifier

namespace ProofLanguage
  variable (f : Nat → Nat)
  variable (h : ∀ x : Nat, f x ≤ f (x + 1))

  example : f 0 ≤ f 3 :=
    have : f 0 ≤ f 1 := h 0
    have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
    show f 0 ≤ f 3 from Nat.le_trans this (h 2)

  example : f 0 ≤ f 3 :=
    have : f 0 ≤ f 1 := h 0
    have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
    show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)

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
  example (n : Nat) : Nat := ‹Nat›

end ProofLanguage

namespace Exercises_1
  variable (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    Iff.intro
      (λ h : ∀ (x : α), p x ∧ q x =>
        ⟨λ x => (h x).left, λ x => (h x).right⟩)
      (λ h : (∀ (x : α), p x) ∧ ∀ (x : α), q x =>
        λ x => ⟨h.left x, h.right x⟩ )

  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    λ h₁ : ∀ (x : α), p x → q x =>
    λ h₂ : ∀ x, p x =>
    λ x => h₁ x (h₂ x)

  -- В этом упражнении постарайся понять почему обратное недоказуемо.
  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
    λ h => Or.elim h
      (λ h₀ : ∀ x, p x => λ x => Or.inl (h₀ x))
      (λ h₁ : ∀ x, q x => λ x => Or.inr (h₁ x))

  -- Потому что из разных иксов ты можешь выбрать какой-то один.
  -- А наборот хуй там плавал.
  example : ∀ x, p x ∨ q x → (∀ x, p x) ∨ (∀ x, q x) :=
    λ x h =>
      Or.elim h
        (λ h_px : p x => Or.inl (λ _ => sorry /-h_px-/ ))
        (λ h_qx : q x => sorry)

end Exercises_1

namespace Exercises_2
  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : α → ((∀ x : α, r) ↔ r) :=
    λ x =>
      Iff.intro
        (λ h => h x)
        (λ r => λ _ => r)

  open Classical

  -- Одно из направлений требует классической логики.
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

  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    Iff.intro
      (λ h => λ ev_r : r => λ x => (h x) ev_r)
      (λ h => λ x => (λ ev_r : r => (h ev_r) x))

end Exercises_2

namespace Exercises_3
  -- Парадокс брадобрея (одна из интерпретаций парадокса Рассела)

  variable (men : Type) (barber : men)
  variable (shaves : men → men → Prop)

  open Classical

  -- h_b:     shaves barber barber → (shaves barber barber → False)
  -- h_b_inv: (shaves barber barber → shaves barber barber) → False
  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
    have h_self := h barber
    Iff.elim
      (λ h_b : shaves barber barber → ¬shaves barber barber =>
        λ h_b_inv : ¬shaves barber barber → shaves barber barber =>
          sorry) h_self

  -- туду: венуться сюда позже

end Exercises_3

namespace Exercises_4
  def even (n : Nat) : Prop :=
    ∃ k, n = 2 * k

  def prime (n : Nat) : Prop :=
    n = 1 ∨ ¬ ∃ x, x | n

  def infinitely_many_primes : Prop :=
    ∀ n : Nat, ∃ m, m > n ∧ prime m

  -- If 2*k+1 is prime and k > 0, then k itself must be a power of 2,
  -- so 2*k+1 is a Fermat number; such primes are called Fermat primes.
  -- https://mathworld.wolfram.com/FermatPrime.html
  --
  -- F_k = pow(2, pow(2, k)) + 1

  def Fermat_prime (n : Nat) : Prop :=
    n > 1 ∧ ∀ (k : Nat), (k < 5 ∨ k > 32) ∧ n = 2^(2^k) + 1

  def infinitely_many_Fermat_primes : Prop :=
    ∀ n : Nat, ∃ m, m > n ∧ Fermat_prime m

  -- Every even natural number greater than 2 is
  -- the sum of two prime numbers.

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

  def Goldbach's_weak_conjecture : Prop :=
    ∀ n : Nat,
      (¬ even n) ∧ n > 5 →
      ∀ (p₁ p₂ p₃ : Nat), prime p₁ ∧ prime p₂ ∧ prime p₃ →
      n = p₁ + p₂ + p₃

  -- Теорема утверждает, что для любого натурального числа n > 2
  -- уравнение a^n + b^n = c^n не имеет решений в целых
  -- ненулевых числах a, b, c.

  def Fermat's_last_theorem : Prop :=
    ∀ n : Nat, n > 2 →
      ¬ ∃ (a b c : Nat), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 →
      a^n + b^n = c^n

end Exercises_4
