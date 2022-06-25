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
