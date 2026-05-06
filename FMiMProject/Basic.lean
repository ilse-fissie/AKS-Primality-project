import Mathlib.Tactic
import Mathlib.RingTheory.SimpleRing.Basic

-- Mathlib.Algebra
/-
We start with an example theorem we need to prove. For this we
will also need to install the right packages etc.
-/

def hello := "world"

theorem Theorem1 {R : Type u_1} [CommSemiring R] (n : ℕ)
(x :R) [CharP R n] : n.Prime ↔  (x+1)^n = x^n+1 := by
  constructor
  · intro h
    have name : Fact (Nat.Prime n) := {out := h}
    rw [add_pow_char x 1]
    simp
  · contrapose
    intro h
    push Not
