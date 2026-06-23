/- Brief guide to coding classical logic in Lean 4-/

theorem weak_LEM (P : Prop) : ¬¬(P ∨ ¬P) :=
/- To prove ¬¬(P ∨ ¬P), we wnat to construct ¬(P ∨ ¬P) → ⊥
which is the same as λ h : ¬(P ∨ ¬P). proof : ⊥ -/

-- We construct λ h : ¬(P ∨ ¬P). X : ⊥
fun h =>
  /- To obtain the proof X of type ⊥, we take the application
  h (P ∨ ¬P), which gives us ⊥, where (P ∨ ¬P) is obtained from
  Or introduction using ¬P
  -/
  h (Or.inr (fun hp =>
  -- λ hp : P. ¬(P ∨ ¬ P)hp gives P → ⊥
    h (Or.inl hp)))

theorem weak_LEM' (P : Prop) : ¬¬(P ∨ ¬P) :=
fun h =>
  h (Or.inr (fun hp =>
    h (Or.inl hp)))

-- Axiom that induces classical logic
axiom doubleNeg {P : Prop} : ¬¬P → P

-- Recovering Law of Excluded Middle (LEM) from axiom doubleNeg
theorem LEM (Q : Prop) : Q ∨ ¬ Q :=
 doubleNeg (weak_LEM Q)
