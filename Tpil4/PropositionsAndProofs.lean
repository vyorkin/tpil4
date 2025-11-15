namespace Basics
  #check And
  #check Or
  #check Not

  variable (p q r : Prop)

  #check And p q
  #check Or p q
  #check Not p

  def Implies (p q : Prop) : Prop := p → q
  def Proof (p : Prop) := p

  #check Implies (And p q) (Or p q)

  axiom and_commut (p q : Prop) :
    Proof (Implies (And p q) (And q p))

  #check and_commut p q

  axiom modus_ponens (p q : Prop) :
    Proof (Implies p q) → Proof p → Proof q

  axiom implies_intro (p q : Prop) :
    (Proof p -> Proof q) -> Proof (Implies p q)
end Basics

namespace PropositionsAsTypes
  set_option linter.unusedVariables false

  variable {p : Prop}
  variable {q : Prop}

  theorem t1 : p → q → p :=
    λ (hp : p) => λ (hq : q) => V

  #print t1

  theorem t2 : p → q → p :=
    fun hp : p =>
    fun hq : q =>
    show p from hp
    -- ^ which is equivalent to:
    -- (hp : p)

  #print t2

  theorem t3 (hp : p) (hq : q) : p := hp
  #print t3

  axiom hp : p
  theorem t4 : q -> p := t3 hp

  axiom unsound : False

  theorem ex : 1 = 0 := False.elim unsound

  theorem t5 : ∀ {p q : Prop}, p → q → p :=
    fun {p q : Prop} (hp : p) (hq : q) => hp

  variable {α β : Prop}
  theorem t6 : α → β → α := fun (ha : α) (hb : β) => ha

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

namespace Conjunction
  variable (p q : Prop)

  example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

  #check fun (hp : p) (hq : q) => And.intro hp hq

  example (h : p ∧ q) : p := And.left h
  example (h : p ∧ q) : q := And.right h

  example (h : p ∧ q) : q ∧ p :=
    And.intro (And.right h) (And.left h)

end Conjunction

namespace SyntacticGadgets
  variable (p q : Prop)
  variable (hp : p) (hq : q)
  #check (⟨hp, hq⟩ : p ∧ q)

  variable (xs : List Nat)
  #check List.length xs
  #check xs.length

  example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

  example (h : p ∧ q) : q ∧ p ∧ q :=
    ⟨h.right, ⟨h.left, h.right⟩⟩

  example (h : p ∧ q) : q ∧ p ∧ q :=
    ⟨h.right, h.left, h.right⟩

end SyntacticGadgets

namespace Disjunction
  variable (p q r : Prop)

  example (hp : p) : p ∨ q := Or.intro_left q hp
  example (hq : q) : p ∨ q := Or.intro_right p hq

  example (h : p ∨ q) : q ∨ p :=
    Or.elim h
    (fun hp : p => Or.intro_right _ hp)
    (fun hq : q => Or.intro_left _ hq)

  example (h : p ∨ q) : q ∨ p :=
    Or.elim h
    (fun hp => Or.inr hp)
    (fun hq => Or.inl hq)

  example (h : p ∨ q) : q ∨ p :=
    Or.elim h Or.inr Or.inl

  example (h : p ∨ q) : q ∨ p :=
    h.elim Or.inr Or.inl

end Disjunction

namespace NegationAndFalsity
  variable (p q r : Prop)

  example (hpq : p → q) (hnq : ¬q) : ¬p :=
    fun hp : p => -- p -> False
      let hq := (hpq hp : q)
      show False from hnq hq

  example (hp : p) (hnp : ¬p) : q := -- ¬p : p → False
    False.elim (hnp hp)

  example (hp : p) (hnp : ¬p) : q :=
    absurd hp hnp

  example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
    absurd (hqp hq) hnp

end NegationAndFalsity

namespace LogicalEquivalence
  variable (p q r : Prop)

  theorem and_swap : p ∧ q ↔ q ∧ p :=
    Iff.intro
      (fun h : p ∧ q => ⟨h.right, h.left⟩)
      (fun h : q ∧ p => ⟨h.right, h.left⟩)

  variable (h : p ∧ q)
  example : q ∧ p := Iff.mp (and_swap p q) h

  theorem and_swap' : p ∧ q ↔ q ∧ p :=
    ⟨fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩⟩

  example (h : p ∧ q) : q ∧ p := (and_swap' p q).mp h

end LogicalEquivalence

namespace AuxiliarySubgoals
  variable (p q : Prop)

  example (h : p ∧ q) : q ∧ p :=
    have hp : p := h.left
    have hq : q := h.right
    (⟨hq, hp⟩ : q ∧ p)

  example (h : p ∧ q) : q ∧ p :=
    have hp : p := h.left
    suffices hq : q from And.intro hq hp
    show q from And.right h

end AuxiliarySubgoals

namespace ClassicalLogic
  open Classical

  variable (p : Prop)

  #check em p

  -- use  em: (p ∨ ¬p)  to create dne: (¬¬p → p)
  -- use dne: (¬¬p → p) to create  em: (p ∨ ¬p)

  theorem dne (p : Prop) (h : ¬¬p) : p :=
    let hh := em p -- p ∨ ¬p
    Or.elim hh
      id
      (λ hnp : ¬p => absurd hnp h)

  theorem em' (p : Prop) : p ∨ ¬p :=
    have h : ¬¬(p ∨ ¬p) := -- ((p ∨ ¬p) -> False) -> False
      λ hnpnp : ¬(p ∨ ¬p) => -- (p ∨ ¬p) -> False
        have hnp : ¬p := λ hp => hnpnp (Or.inl hp) -- p -> False
        have hnpnp' : ¬¬p := λ hp => hnpnp (Or.inr hp) -- (p -> False) -> False
        absurd hnp hnpnp'
    dne (p ∨ ¬p) h

  example (h : ¬¬p) : p :=
    byCases
      (λ h1 : p => h1)
      (λ h1 : ¬p => absurd h1 h)

  example (h : ¬¬p) : p :=
    byContradiction
      (λ h1 : ¬p => h h1)

end ClassicalLogic

namespace Exercises
  variable (p q r : Prop)

  -- commutativity of ∨ and ∧
  example : p ∨ q ↔ q ∨ p :=
    Iff.intro
      (λ (hpq : p ∨ q) => Or.elim hpq Or.inr Or.inl)
      (λ (hqp : q ∨ p) => Or.elim hqp Or.inr Or.inl)

  example : p ∧ q ↔ q ∧ p :=
    Iff.intro
      (λ (hpq : p ∧ q) => ⟨hpq.right, hpq.left⟩)
      (λ (hqp : q ∧ p) => ⟨hqp.right, hqp.left⟩)

  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    Iff.intro
      (λ h => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
      (λ h => ⟨⟨h.left, h.right.left⟩, h.right.right⟩)

  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    Iff.intro
      (λ h => Or.elim h
        (λ pq => Or.elim pq Or.inl (λ q => Or.inr (Or.inl q)))
        (λ r => Or.inr (Or.inr r)))
      (λ h => Or.elim h
        (λ p => Or.inl (Or.inl p))
        (λ qr => Or.elim qr (λ q => Or.inl (Or.inr q)) Or.inr))

  -- distributivity
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

    example : (p → (q → r)) ↔ (p ∧ q → r) :=
      Iff.intro
        (λ h_p_qr => λ h_pq => (h_p_qr h_pq.left) h_pq.right)
        (λ h_pq_r => λ h_p => λ h_q => h_pq_r ⟨h_p, h_q⟩)

    example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
      Iff.intro
        (λ h_pq_r => ⟨λ p => h_pq_r (Or.inl p), λ q => h_pq_r (Or.inr q)⟩)
        (λ pr_qr => λ pq => Or.elim pq pr_qr.left pr_qr.right)

    example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
      Iff.intro
        (λ h_npq =>
          ⟨λ h_p => h_npq (Or.inl h_p),
           λ h_q => h_npq (Or.inr h_q)⟩)
        (λ h_npnq => λ h_pq => Or.elim h_pq
          (λ h_p => absurd h_p h_npnq.left)
          (λ h_q => absurd h_q h_npnq.right))

    example : ¬p ∨ ¬q → ¬(p ∧ q) :=
      λ h_npnq => λ h_pq => Or.elim h_npnq
        (λ h_np => h_np h_pq.left)
        (λ h_nq => h_nq h_pq.right)

    example : ¬(p ∧ ¬p) :=
      λ ⟨h_p, h_np⟩ => absurd h_p h_np

    example : p ∧ ¬q → ¬(p → q) :=
      λ ⟨h_p, h_nq⟩ =>
        λ h_pfq => h_nq (h_pfq h_p)

    example : ¬p → (p → q) :=
      λ h_np => (λ h_p => absurd h_p h_np)

    example : (¬p ∨ q) → (p → q) :=
      λ h => (λ h_p => Or.elim h (absurd h_p) id)

    example : p ∨ False ↔ p :=
      Iff.intro
        (λ h_pfalse => Or.elim h_pfalse id (λ h_f => False.elim h_f))
        (λ h_p => Or.inl h_p)

    example : p ∧ False ↔ False :=
      Iff.intro
        (λ ⟨_, h_f⟩ => h_f)
        False.elim

    example : (p → q) → (¬q → ¬p) :=
      λ h_pfq => (λ h_nq => λ h_p => absurd (h_pfq h_p) h_nq)

end Exercises

namespace ExercisesClassical
  open Classical

  variable (p q r : Prop)

  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
    λ h => Or.elim (em p)
      (λ h_p => Or.elim (h h_p)
        (λ h_q => Or.inl (λ _ => h_q))
        (λ h_r => Or.inr (λ _ => h_r)))
      (λ h_np => Or.inl (λ h_p => absurd h_p h_np))

  example : ¬(p ∧ q) → ¬p ∨ ¬q :=
    λ h => Or.elim (em p)
      (λ h_p => Or.elim (em q)
        (λ h_q =>
          have h_pq : p ∧ q := ⟨h_p, h_q⟩
          False.elim (h h_pq))
        (λ h_nq => Or.inr h_nq))
      (λ h_np => Or.inl h_np)

  example : ¬(p → q) → p ∧ ¬q :=
    λ h => Or.elim (em ¬(p → q))
      (λ h_npq => False.elim (h h_pq))
      (λ _ => Or.elim (em p)
        (λ h_p =>
          sorry)
        (λ h_np => sorry)
        )

  example : (p → q) → (¬p ∨ q) := sorry

  example : (¬q → ¬p) → (p → q) := sorry

  example : p ∨ ¬p := sorry

  example : (((p → q) → p) → p) := sorry

end ExercisesClassical
