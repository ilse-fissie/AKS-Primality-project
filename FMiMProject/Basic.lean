import Mathlib.Tactic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Polynomial.Basic

-- Mathlib.Algebra
/-
We start with an example theorem we need to prove. For this we
will also need to install the right packages etc.
-/

open Polynomial

--Dont forget to add some comments to explain your proof.

--set_option backward.isDefEq.respectTransparency false in (sometimes this is nice)

theorem Theorem1 (n : ℕ) (h_ngone: n > 1) :
 n.Prime ↔ (X+1: (ZMod n)[X])^n = X^n+1 := by
  constructor
  · intro h
    have name : Fact (Nat.Prime n) := {out := h}
    rw [add_pow_char]
    simp
  · contrapose
    intro h
    let p := Nat.minFac n
    have p_lt : p < n := (Nat.not_prime_iff_minFac_lt (by omega)).1 h
    have p_prime : Nat.Prime p := by
      apply Nat.minFac_prime
      grind --you can also use "omega"
    push Not
    intro h_not_prime
    rw[add_pow] at h_not_prime
    have := congrArg (fun (f : (ZMod n)[X]) => Polynomial.coeff f p) h_not_prime
    dsimp at this
    simp[le_of_lt p_lt, ne_of_lt p_lt] at this
    rw[Polynomial.coeff_one] at this
    simp[Nat.Prime.ne_zero p_prime] at this
    have h_intermideate: (n.choose p).factorization p < n.factorization p := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      /- Alain: You need to provide a proof that p.factorial divides n.descFactorial p. Look at the lemma Nat.factorial_dvd_descFactorial. -/
      rw [Nat.factorization_div (by exact Nat.factorial_dvd_descFactorial n p)]
      /- Alain: Suggestion. Give a name to the statement below, and prove it 'for every n', i.e. add a universal quantifier over 'n'. This is so that you can later apply it with a different 'n'. Even better, write it as a separate lemma. See comment (*) below.
      Regarding how to prove it. Here is a suggestion with a proof skeleton. I have sorry'ed some parts. -/
      have : ((n.descFactorial p).factorization p = n.factorization p) := by
        rw [Nat.descFactorial_eq_prod_range, Nat.factorization_prod_apply (by grind), Finset.sum_eq_single_of_mem 0]
        · simp
        · simp
          apply Nat.Prime.pos at p_prime
          omega
        · intro b hbmem hbne
          simp at hbmem
          rw [Nat.factorization_eq_zero_iff]
          simp[p_prime]
          constructor
          rw[Nat.dvd_sub_iff_right]
          apply Nat.not_dvd_of_pos_of_lt
          lia
          exact hbmem
          lia
          exact Nat.minFac_dvd n
      simp only [Finsupp.coe_tsub, Pi.sub_apply, gt_iff_lt]
      rw [this]
      /- Alain: (*) Suggestion: Use Nat.descFactorial_self with p, and then apply the previous result. Look at Nat.Prime.factorization_self  -/
      have : p.factorial.factorization p = 1 := by
        by_cases h_p_is_2 : p = 2
        · rw[h_p_is_2]
          norm_num
        · nth_rw 1[← Nat.mul_one p]
          rw[Nat.factorization_factorial_mul p_prime]
          simp
      rw [this]
      have : n.factorization p ≠ 0 := by
        apply Nat.factorization_minFac_ne_zero
        assumption
      omega
    -- have := Nat.factorization_choose p_prime (le_of_lt p_lt) (by sorry : _ < n)
    -- simp at this
    rw[ZMod.natCast_eq_zero_iff] at this
    rw[← Nat.factorization_le_iff_dvd] at this
    have := this p
    lia
    lia
    apply Nat.choose_ne_zero
    lia








-- theorem Theorem1 (n : ℕ) (h_ngone: n > 1) :
--  n.Prime ↔ (X+1: (ZMod n)[X])^n = X^n+1 := by
--   constructor
--   · intro h
--     have name : Fact (Nat.Prime n) := {out := h}
--     rw [add_pow_char]
--     simp
--   · contrapose
--     intro h
--     let p := Nat.minFac n
--     have p_lt : p < n := (Nat.not_prime_iff_minFac_lt (by omega)).1 h
--     have p_prime : Nat.Prime p := by
--       apply Nat.minFac_prime
--       grind --you can also use "omega"
--     push Not
--     intro h_not_prime
--     rw[add_pow] at h_not_prime
--     have := congrArg (fun (f : (ZMod n)[X]) => Polynomial.coeff f p) h_not_prime
--     dsimp at this
--     simp[le_of_lt p_lt, ne_of_lt p_lt] at this
--     rw[Polynomial.coeff_one] at this
--     simp[Nat.Prime.ne_zero p_prime] at this
--     have : (n.choose p).factorization p < n.factorization p := by
--       rw [Nat.choose_eq_descFactorial_div_factorial]
--       rw [Nat.factorization_div (by sorry)]
--       have : ((n.descFactorial p).factorization p = n.factorization p) := by sorry
--       simp only [Finsupp.coe_tsub, Pi.sub_apply, gt_iff_lt]
--       rw [this]
--       have : p.factorial.factorization p = 1 := by
--         by_cases h_p_is_2 : p = 2
--         ·sorry
--         ·sorry
--       --For p > 2 use Nat.factorization_factorial_le_div_pred
--       rw [this]
--       have : n.factorization p ≠ 0 := by
--         apply Nat.factorization_minFac_ne_zero
--         assumption
--       omega
--     -- have := Nat.factorization_choose p_prime (le_of_lt p_lt) (by sorry : _ < n)
--     -- simp at this

--     sorry

--try padicValNat_choose hint pjtor ???



--def order_n_modr {α β : Type*} (f : α → β) : List α → List β
--  | []      => []

--Dont forget to implement the order condition: smallest k st n^k mod n = 1
/- ord (n) = n Mod r ∈ ℤ (smallest k ∈ ℕ s.t. ∃ m ∈ ℤ  s.t. n= m·r + k)
and n Mod r >
-/
theorem AKS_Primality_Test {R : Type u_1} (n r : ℕ) (h_ngone: n > 1)
  (h_r_less_than_n : r < n) (h_order : orderOf (n: ZMod r) > (Real.log n)^2): n.Prime ↔
  True := by sorry
