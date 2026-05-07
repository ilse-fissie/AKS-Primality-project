import Mathlib.Tactic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Polynomial.Basic

-- Mathlib.Algebra
/-
We start with an example theorem we need to prove. For this we
will also need to install the right packages etc.
-/

open Polynomial


theorem Theorem1 (n : ℕ) (h_ngone: n > 1) :
 n.Prime ↔ (X+1: (ZMod n)[X])^n = X^n+1 := by
  constructor
  · intro h
    have name : Fact (Nat.Prime n) := {out := h}
    rw [add_pow_char]
    simp
  · contrapose
    intro h
    push Not
    intro h_not_prime
    sorry




--def order_n_modr {α β : Type*} (f : α → β) : List α → List β
--  | []      => []

--Dont forget to implement the order condition: smallest k st n^k mod n = 1
/- ord (n) = n Mod r ∈ ℤ (smallest k ∈ ℕ s.t. ∃ m ∈ ℤ  s.t. n= m·r + k)
and n Mod r >
-/
theorem AKS_Primality_Test {R : Type u_1} (n r : ℕ) (h_ngone: n > 1)
  (h_r_less_than_n : r < n) (h_order : orderOf (n: ZMod r) > (Real.log n)^2): n.Prime ↔
  True := by sorry
