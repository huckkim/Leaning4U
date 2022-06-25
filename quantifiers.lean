variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  have h_lhs : (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) :=
    (fun h : (∀ x, p x ∧ q x) => 
      And.intro
      (fun y : α =>
          (show (p y) from (h y).left))
      (fun y : α =>
          (show (q y) from (h y).right)))
  have h_rhs :  (∀ x, p x) ∧ (∀ x, q x) → (∀ x, p x ∧ q x):=
    (fun h : (∀ x, p x) ∧ (∀ x, q x) =>
      (fun y : α =>
        And.intro ((And.left h) y) ((And.right h) y)))
  Iff.intro h_lhs h_rhs

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun f : (∀ x, p x → q x) =>
  fun g : (∀ x, p x) =>
  (fun y : α =>
    (f y) (g y))

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun f : (∀ x, p x) ∨ (∀ x, q x) =>
  (fun y : α => 
    Or.elim f
      (fun f1 : (∀ x, p x) => 
        Or.inl (f1 y))
      (fun f2 : (∀ x, q x) => 
        Or.inr (f2 y)))

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

#check @Exists.intro

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x:=
  Exists.elim h
    (fun w =>
      (fun hw : p w ∧ q w =>
        Exists.intro w (And.intro hw.right hw.left)))

def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2 , by rw [hw1, hw2, Nat.mul_add]⟩
