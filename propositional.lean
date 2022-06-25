variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  Iff.intro
    (fun h : p ∧ q => And.intro (And.right h) (And.left h))
    (fun h : q ∧ p => And.intro (And.right h) (And.left h))

example : p ∨ q ↔ q ∨ p :=
  have hpq : p ∨ q → q ∨ p := 
    (fun h : p ∨ q =>
      Or.elim h
        (fun hp : p => Or.inr hp)
        (fun hq : q => Or.inl hq))
  have hqp : q ∨ p → p ∨ q :=
    (fun h : q ∨ p =>
      Or.elim h
        (fun hq : q => Or.inr hq)
        (fun hp : p => Or.inl hp))
  Iff.intro hpq hqp 

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro 
    (fun h_lhs : (p ∧ q) ∧ r =>
      And.intro (And.left (And.left h_lhs)) (And.intro (And.right (And.left h_lhs)) (And.right h_lhs)))
    (fun h_rhs : p ∧ (q ∧ r) =>
      And.intro (And.intro (And.left h_rhs) (And.left (And.right h_rhs))) (And.right (And.right h_rhs)))

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  have h_lhs : (p ∨ q) ∨ r → p ∨ (q ∨ r) :=
    (fun h : (p ∨ q) ∨ r => 
      Or.elim h 
        (fun hpq : (p ∨ q) => 
          Or.elim hpq
            (fun hp : p => Or.inl hp)
            (fun hq : q => Or.inr (Or.inl hq)))
        (fun hr : r => 
          Or.inr (Or.inr hr)))
  have h_rhs : p ∨ (q ∨ r) → (p ∨ q) ∨ r :=
    (fun h : p ∨ (q ∨ r) =>
      Or.elim h
        (fun hp : p =>
          Or.inl (Or.inl hp))
        (fun hqr : q ∨ r =>
          Or.elim hqr
            (fun hq : q =>
              Or.inl (Or.inr hq))
            (fun hr : r =>
              Or.inr hr)))
  Iff.intro h_lhs h_rhs

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  have h_lhs : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
    (fun h_pqr : p ∧ (q ∨ r) =>
      have hp : p := And.left h_pqr
      Or.elim (And.right h_pqr)
        (fun hq : q => Or.inl (And.intro hp hq))
        (fun hr : r => Or.inr (And.intro hp hr)))
  have h_rhs : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) := 
    (fun h_pq_pr : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h_pq_pr
        (fun hpq : p ∧ q =>
          (And.intro (And.left hpq) (Or.inl (And.right hpq))))
        (fun hpr : p ∧ r =>
          (And.intro (And.left hpr) (Or.inr (And.right hpr)))))
  Iff.intro h_lhs h_rhs

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
  have h_p_qr : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r) :=
    (fun hp_qr : p ∨ (q ∧ r) =>
      Or.elim hp_qr
        (fun hp : p => And.intro (Or.inl hp) (Or.inl hp))
        (fun hqr : q ∧ r => And.intro (Or.inr (And.left hqr)) (Or.inr (And.right hqr))))
  have h_pq_pr : (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r) := 
    (fun h_pq_pr : (p ∨ q) ∧ (p ∨ r) => 
      Or.elim (And.left h_pq_pr)
        (fun hp : p => Or.inl hp)
        (fun hq : q =>
          Or.elim (And.right h_pq_pr)
            (fun hp : p => Or.inl hp)
            (fun hr : r => Or.inr (And.intro hq hr))))
  Iff.intro h_p_qr h_pq_pr

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
  have h_lhs : (p → (q → r)) → (p ∧ q → r) := 
    (fun h_pqr : p → (q → r) =>
      (fun hpq : p ∧ q =>
        (h_pqr (And.left hpq) (And.right hpq)))) 
  have h_rhs : (p ∧ q → r) → (p → (q → r)) :=
    (fun h_pqr : (p ∧ q → r) => 
      (fun hp : p =>
        (fun hq : q => 
          (h_pqr (And.intro hp hq))))) 
  Iff.intro h_lhs h_rhs

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
  have h_lhs : ((p ∨ q) → r) → (p → r) ∧ (q → r) :=
    (fun h_pq_r : ((p ∨ q) → r) =>
      And.intro
        (fun hp : p => 
          h_pq_r (Or.inl hp))
        (fun hq : q =>
          h_pq_r (Or.inr hq)))
  have h_rhs : (p → r) ∧ (q → r) → ((p ∨ q) → r) :=
    (fun h_pr_qr : (p → r) ∧ (q → r) => 
      (fun hpq : p ∨ q =>
        Or.elim hpq 
          (fun hp : p => (And.left h_pr_qr) hp)
          (fun hq : q => (And.right h_pr_qr) hq)))
  Iff.intro h_lhs h_rhs

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
  have h_lhs : ¬(p ∨ q) → ¬p ∧ ¬q :=
    (fun (npq : (p ∨ q) → False) => 
      (And.intro 
        (fun (hp : p) => (npq (Or.inl hp)))
        (fun (hq : q) => (npq (Or.inr hq)))))
  have h_rhs : ¬p ∧ ¬q → ¬(p ∨ q) :=
    (fun (hnpnq : ¬p ∧ ¬q) => 
      (fun (hpq : p ∨ q) => 
        Or.elim hpq
          (fun (hp : p) => 
            (And.left hnpnq) hp)
          (fun (hq : q) =>
            (And.right hnpnq) hq)))
  Iff.intro h_lhs h_rhs

example : ¬p ∨ ¬q → ¬(p ∧ q) := 
  (fun (hnpnq : ¬p ∨ ¬q) (hpq: p ∧ q) =>
    Or.elim hnpnq
      (fun hnp : ¬p => False.elim (hnp (And.left hpq)))
      (fun hnq : ¬q => False.elim (hnq (And.right hpq))))

example : ¬(p ∧ ¬p) :=
  (fun hpnp : p ∧ ¬p =>
    (False.elim ((And.right hpnp) (And.left hpnp))))

example : p ∧ ¬q → ¬(p → q) := 
  (fun (hpnq : p ∧ ¬q) (hpq : p → q) =>
    (False.elim ((And.right hpnq) (hpq (And.left hpnq)))))

example : ¬p → (p → q) := 
  (fun (hnp : ¬p) (hp : p) =>
    False.elim (hnp hp))

example : (¬p ∨ q) → (p → q) := 
  (fun h_npq : (¬p ∨ q) =>
    (fun hp : p => 
      Or.elim h_npq
        (fun hnp : ¬p =>
          False.elim (hnp hp))
        (fun hq : q => hq)))

example : p ∨ False ↔ p := 
  have h_lhs : p ∨ False → p :=
    (fun h_pf : p ∨ False => 
      Or.elim h_pf 
        (fun hp : p => hp)
        (fun hf : False => False.elim hf))
  have h_rhs : p → p ∨ False :=
    (fun hp : p => Or.inl hp)
  Iff.intro h_lhs h_rhs

example : p ∧ False ↔ False := 
  have h_lhs : p ∧ False → False :=
    (fun h_pf : p ∧ False => 
      And.right h_pf)
  have h_rhs : False → p ∧ False :=
    (fun h_f : False =>
      And.intro (False.elim h_f) h_f)
  Iff.intro h_lhs h_rhs

example : (p → q) → (¬q → ¬p) := 
  (fun h_pq : p → q =>
    (fun hnq : ¬q =>
      (fun hp : p =>
        False.elim (hnq (h_pq hp)))))

open Classical

variable (p q r s : Prop)

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
  (fun hp : p => hp)
  (fun nhp : ¬p => False.elim (h nhp))

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
