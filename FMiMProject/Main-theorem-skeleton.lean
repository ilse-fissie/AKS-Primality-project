import Mathlib.Tactic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Polynomial.Basic
-- import Mathlib.Data.Nat.Prime.Defs

/- In this file we will start with the proof of the main theorem
of the AKS primality test.
-/

/-
-- We do not use this (thought we would in the beginning)
structure values where
  n : ℕ
  n_geq_two: n ≥ 2
  r : ℕ
  r_nonneg : r ≥ 0
  r_le_n : r < n
  ordergeq: addOrderOf (n : ZMod r) > (Nat.log 10 n)^2
-/

open Polynomial

variable (p: ℕ) (r: ℕ ) (n_A :ℕ ) [Fact p.Prime]

abbrev PolyRing_Z_p_Xr :=
  AdjoinRoot (X^r -1 : (ZMod p)[X])
-- PolyRing_Z_p_Xr = (ZMod p)[X] /(X^r -1)
-- abbrev instead of def, to make lean read it in instances
-- one extra layer of visibility?

/-
instance : Algebra (ZMod p)[X] (PolyRing_Z_p_Xr p r) :=

If we do need the instance: RingHom.toAlgebra, with
RingHom = AdjoinRoot.mk (X^r -1 : (ZMod p)[X])
-/


noncomputable def Closure_X_to_Xn_A : Submonoid (ZMod p)[X] :=
  Submonoid.closure { (X : (ZMod p)[X]) + (C i : (ZMod p)[X]) | (i :ℤ ) (_ : 0 ≤ i) (_ : i ≤ n_A) }
-- Closure_X_to_Xn_A = ⟨X, X+1, X+2, ..., X+A⟩ ⊆ ℤ/p[X]

noncomputable def H_Monoid : Submonoid (PolyRing_Z_p_Xr p r) := by
  exact Submonoid.map (AdjoinRoot.mk (X^r -1 : (ZMod p)[X]))
    (Closure_X_to_Xn_A p n_A )
-- H_Monoid = ⟨X, X+1, X+2, ..., X+A⟩ / (p, X^r-1)
-- is the monoid given by the image of the map f: ℤ[X] → ℤ/p[X]/(X^r -1),
-- restricted to domain (X, X+1, ...., X+n_A)

-- add assumptions:
structure irred_mod_p_factor_Xr where
  h_poly :(ZMod p)[X]
  h_irred : Irreducible h_poly
  h_factor_Xr : h_poly ∣ (X^r -1 :(ZMod p)[X] )
-- h_poly is a polynomial in ℤ/p[X], it is irriducible, and a factor of X^r -1
-- *This might have to be specified to a factor of Φ_r, the cyclotomic polynomial*

variable {p r} in -- *Why is this needed*
abbrev Field_F (h: irred_mod_p_factor_Xr p r) := AdjoinRoot h.h_poly
-- F = Field_F =(ℤ/p[X]/(X^r-1))/h,
-- since h is irred and a factor of X^r -1, F is a field (Lean knows this)

variable (h : irred_mod_p_factor_Xr p r)

noncomputable def map : PolyRing_Z_p_Xr p r →ₐ[ZMod p] Field_F h  := by
  unfold PolyRing_Z_p_Xr Field_F
  refine AdjoinRoot.mapAlgHom (AlgHom.id (ZMod p) (ZMod p) )
    (X ^ r - 1 : (ZMod p)[X]) h.h_poly ?_
  simp
  apply h.h_factor_Xr
-- The map ℤ/p[X]/(X^r-1)→ ℤ/p[X]/(h), needed to define G, as submonoid of F

noncomputable def G_h : Submonoid (Field_F h) :=
  Submonoid.map (map p r h) (H_Monoid p r n_A)
--  G = ⟨ X, X+1, X+2, ..., X+[A]⟩ / (p, h(X))
--    = H/ (h(X))

-- g ∈ G, g ≠ 0
-- g(X) = Π _{0 ≤ a ≤ A}(x+a)^{e_a} ∈ H
-- g(X)^n = g(X^n) mod (p, X^r-1)


def property_of_S : ℕ → Prop := by
  intro k
  exact ∀ g ∈ (Closure_X_to_Xn_A p n_A),
  AdjoinRoot.mk h.h_poly (g.comp X^k ) = (AdjoinRoot.mk h.h_poly g)^k
-- k has the property of S if g(X^k) = g(X)^k ∈ Field_F

def Set_S : Set ℕ :=
  {k: Nat | property_of_S p r n_A h k }
-- S = {k ∈ ℕ | g(X^k) = g(X)^K ∈ Field_F }

def Set_R (r: ℕ) (p' n' : (ZMod r)ˣ) : Subgroup (ZMod r)ˣ :=
   (Subgroup.closure ( {p', n'}) )
-- We assume p', n'∈ (ZMod r)ˣ, we need to prove this for p, n in the lemma's
-- Use rangle langle to give elements in combination with proof of properties

-- S = { k \in \Z : g(X^k) = g(X)^k mod (p, X^r -1)}
-- p, n ∈ S

-- A = √r log n
-- p | n, p prime
-- Cyclotomic polynomials Φ_d :
-- x^r -1 = Π_{d|r} Φ_d(X)
-- h(X) irriducible factor of Φ_r(X) in (ℤ/pℤ)[X]
-- 𝔽 :≡ ℤ [X]/(p, h(x)) iso to field of p^m elements
-- m = deg h, 𝔽 - {0} cyclic group of order p^m -1,
--   and r | p^m-1, because x of order r

/-
Lemma 4.1
\begin{lemma}
   If $a, b \in S$, then $ab \in S$.
\end{lemma}

Lemma 4.2
\begin{lemma}
   If $a, b \in S$ and $a \equiv b \mod r$, then $a \equiv b \mod |G|$.
\end{lemma}

Let $p$ be a prime dividing $n$ so that $(x + a)^n \equiv x^n + a \mod (p, x^r - 1)$.\\
for $d|r$, $\Phi_d(x)$ is the $d$th cyclotomic polynomial, whose roots are the primitive $d$th roots of unity.\\
Let $h(x)$ be an irreducible factor of $\Phi_r(x) (\mod p)$.

Lemma 4.3
\begin{lemma}
   Suppose that $f(x), g(x) \in \mathbb{Z}[x]$ with $f(x) \equiv g(x) \mod (p, h(x))$
   and that the reductions of $f$ and $g$ in $\mathbb{F}$ both belong to $G$.
   If $f$ and $g$ both have degree $< |R|$, then $f(x) equiv g(x) (\mod p)$
\end{lemma}
-/
theorem lemma_one (a b : ℕ) (ha: a ∈ Set_S p r n_A h) (hb: b ∈ Set_S p r n_A h)
  : a*b ∈ (Set_S p r n_A h) := by sorry

theorem lemma_two (a b : Set_S p r n_A h)(h_r_g_one: r > 1)(h_ngone: n > 1)
  (h_r_less_than_n : r < n) (h_order : addOrderOf (n: ZMod r) > (Real.log n)^2)
  : (a : ZMod r) = b → (a : ZMod (G_h p r n_A h).ctorIdx) = b := by sorry

variable(a : ℕ+)
def p_condition (n r p : ℕ) : Prop :=
  ∀ a:ℕ+, a ≤ Int.floor (Real.sqrt r)*(Real.log n) →
  AdjoinRoot.mk (X^r -1 : (ZMod p)[X]) ((X: (ZMod p)[X]) + (C a: (ZMod p)[X]))^n =
  AdjoinRoot.mk (X^r -1 : (ZMod p)[X]) ((X^n:(ZMod p)[X]) + (C a: (ZMod p)[X]))

theorem lemma_three --still add in *{R : Type u_1}*
  (h_r_g_one: r > 1)(h_ngone: n > 1)(h_r_less_than_n : r < n) (h_order : addOrderOf (n: ZMod r) > (Real.log n)^2)
  (h_n_r_coprime : Nat.Coprime n r)(h_p_r_coprime : Nat.Coprime p r)
  /-(h_p_prime : p.Prime)-/(h_p_div_n: p ∣ n)(h_p_condition: p_condition n r p)
  (f g : ℤ[X]) (h_f_equiv_g : AdjoinRoot.mk (h.h_poly : (ZMod p)[X]) (f.map (algebraMap ℤ (ZMod p))) =
  AdjoinRoot.mk (h.h_poly : (ZMod p)[X]) (g.map (algebraMap ℤ (ZMod p))))
  (h_reductions : AdjoinRoot.mk (h.h_poly : (ZMod p)[X]) (f.map (algebraMap ℤ (ZMod p))) ∈ (G_h p r n_A h) ∧
  AdjoinRoot.mk (h.h_poly : (ZMod p)[X]) (g.map (algebraMap ℤ (ZMod p))) ∈ (G_h p r n_A h))
  : f.degree < Subgroup.index (Set_R r (ZMod.unitOfCoprime p h_p_r_coprime) (ZMod.unitOfCoprime n h_n_r_coprime)) ∧
  g.degree < Subgroup.index (Set_R r (ZMod.unitOfCoprime p h_p_r_coprime) (ZMod.unitOfCoprime n h_n_r_coprime)) →
  (f.map (algebraMap ℤ (ZMod p))) = (g.map (algebraMap ℤ (ZMod p))) := by sorry

def first_condition (n : ℕ) : Prop :=
  ∀  (a b : ℕ),a ≠ n → 2 ≤ b → a^b ≠ n

def seccond_condition (n r : ℕ) : Prop :=
   ∀ b ≤ r, b ∉ Nat.primeFactors n

variable (n : ℕ)
variable(a : ℕ+)
def third_condition (n r : ℕ) : Prop :=
  ∀ a:ℕ+, a ≤ Int.floor (Real.sqrt r)*(Real.log n) →
  AdjoinRoot.mk (X^r -1 : (ZMod n)[X]) ((X: (ZMod n)[X]) + (C a: (ZMod n)[X]))^n =
  AdjoinRoot.mk (X^r -1 : (ZMod n)[X]) ((X^n:(ZMod n)[X]) + (C a: (ZMod n)[X]))

theorem AKS_Primality_Test {R : Type u_1}  (h_ngone: n > 1)(h_r_g_one: r > 1)
  (h_r_less_than_n : r < n) (h_order : addOrderOf (n: ZMod r) > (Real.log n)^2): n.Prime ↔
  first_condition n ∧ seccond_condition n r ∧ third_condition n r  := by
  constructor
  · intro h
    constructor
    · unfold first_condition
      intro a b h_a_not_n h_b_geq_two
      have h_a_pow_b_not_prime : ¬ (a^b).Prime := by
        apply Nat.Prime.not_prime_pow h_b_geq_two
      intro hc
      rw[hc] at h_a_pow_b_not_prime
      apply h_a_pow_b_not_prime
      exact (Nat.irreducible_iff_nat_prime ↑n).mp h
--      apply ¬ Nat.Prime.pow_eq_iff h
    · constructor
      · unfold seccond_condition
        simp [Nat.Prime.primeFactors h]
        intro b h_b_leq_r
        have h_b_l_n : b < n := by
          apply lt_of_le_of_lt h_b_leq_r h_r_less_than_n
        apply ne_of_lt h_b_l_n
      · unfold third_condition
        intro a h_a_leq
        have name : Fact (Nat.Prime n) := {out := h}
        rw[← map_pow]
        congr
        rw[add_pow_char]
        rw[← C_pow, ZMod.pow_card]
  · contrapose
    intro h
--    let (p : ℕ)(h_p_prime : p.Prime)(h_p_div_n: p ∣ n)(h_p_condition: p_condition n r p)
    sorry
