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

    example : f a = f b := congrArg f h₁
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

  theorem T
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

end CalculationalProofs
