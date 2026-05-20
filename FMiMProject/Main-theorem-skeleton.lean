import Mathlib.Tactic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Polynomial.Basic
-- import Mathlib.Data.Nat.Prime.Defs

/- In this file we will start with the proof of the main theorem
of the AKS primality test. The main theorem is:
-/
--set_option trace.Meta.synthInstance true

structure values where
  n : ℕ
  n_geq_two: n ≥ 2
  r : ℕ
  r_nonneg : r ≥ 0
  r_le_n : r < n
  ordergeq: addOrderOf (n : ZMod r) > (Nat.log 10 n)^2




-- Construction of the set S

-- A = √r log n
-- p | n, p prime
-- Cyclotomic polynomials Φ_d :
-- x^r -1 = Π_{d|r} Φ_d(X)
-- h(X) irriducible factor of Φ_r(X) in (ℤ/pℤ)[X]
-- 𝔽 :≡ ℤ [X]/(p, h(x)) iso to field of p^m elements
-- m = deg h, 𝔽 - {0} cyclic group of order p^m -1,
--   and r | p^m-1, because x of order r

open Polynomial

abbrev PolyRing_Z_p_Xr (p: ℕ) (r: ℕ ) [Fact p.Prime]  :=
  AdjoinRoot (X^r -1 : (ZMod p)[X])
-- abbrev instead of def, to make lean read it in instances
-- one extra layer of visibility?

variable (p: ℕ) (r: ℕ ) (n_A :ℕ ) [Fact p.Prime]
instance : Algebra ℤ[X] (PolyRing_Z_p_Xr p r) :=
  sorry
-- *I do not remember what I needed to do here and why*

noncomputable def H_Monoid
    -- (p: ℕ )(r: ℕ) [Fact p.Prime] -- These are already general variables
    : Submonoid (PolyRing_Z_p_Xr p r) := -- type : submonoid of (Z/p[X])/(X^r -1)
  Submonoid.map (algebraMap ℤ[X] (PolyRing_Z_p_Xr p r))
  (Submonoid.closure ( { (X + C i )| (i :ℤ ) (_ : 0 ≤ i) (_ : i ≤ n_A) }) )
-- H_Monoid = ⟨X, X+1, X+2, ..., X+A⟩ / (p, X^r-1)
-- is the monoid given by the image of the map f: ℤ[X] → ℤ/p[X]/(X^r -1),
-- restricted to domain (X, X+1, ...., X+n_A)

-- add assumptions
-- h_poly is a polynomial in ℤ/p[X], which is irriducible and is a factor of X^r -1
structure irred_mod_p_factor_Xr where
  h_poly :(ZMod p)[X]
  h_irred : Irreducible h_poly
  h_factor_Xr : h_poly ∣ (X^r -1 :(ZMod p)[X] )
  -- *This needs to be specified to a factor of Φ_r, the cyclotomic polynomial*

variable {p r} in
abbrev Field_F (h: irred_mod_p_factor_Xr p r) := AdjoinRoot h.h_poly
-- F = Field_F =(ℤ/p[X]/(X^r-1))/h,
-- since h is irred and a factor of X^r -1, F is a field (Lean knows this)

variable (h : irred_mod_p_factor_Xr p r)

-- *Also see below*
noncomputable def map : PolyRing_Z_p_Xr p r →ₐ[ZMod p] Field_F h :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (AdjoinRoot.root _) <| by
  simp
  -- h.h_factor_Xr
  sorry

/-
/-- `AdjoinRoot.map` as an `AlgHom`. -/
def mapAlgHom (f : S →ₐ[R] T) (p : S[X]) (q : T[X]) (h : q ∣ p.map f) :
    AdjoinRoot p →ₐ[R] AdjoinRoot q where
  __ := map f p q h
  commutes' r := by simp [map, AdjoinRoot.algebraMap_eq']

-- *Use this to define map (maybe with an instance?)*
def map₂  : PolyRing_Z_p_Xr p r →ₐ[ZMod p] Field_F h  := AdjoinRoot.mapAlgHom ()
-/

-- This is the map we need to define G, as submonoid of F

noncomputable def G_h : Submonoid (Field_F h) :=
  Submonoid.map (map p r h) (H_Monoid p r n_A)
--  G = ⟨ X, X+1, X+2, ..., X+[A]⟩ / (p, h(X))
--    = H/ (h(X))


-- g ∈ G, g ≠ 0
-- g(X) = Π _{0 ≤ a ≤ A}(x+a)^{e_a} ∈ H
-- g(X)^n = g(X^n) mod (p, X^r-1)

-- noncomputable def Set_S : Set ℕ :=

-- S = { k \in \Z : g(X^k) = g(X)^k mod (p, X^r -1)}
-- p, n ∈ S

/-
Lemma 4.1
\begin{lemma}
   If $a, b \in S$, then $ab \in S$.
\end{lemma}
-/

/-
Lemma 4.2
\begin{lemma}
   If $a, b \in S$ and $a \equiv b \mod r$, then $a \equiv b \mod |G|$.
\end{lemma}

Let $p$ be a prime dividing $n$ so that $(x + a)^n \equiv x^n + a \mod (p, x^r - 1)$.\\
for $d|r$, $\Phi_d(x)$ is the $d$th cyclotomic polynomial, whose roots are the primitive $d$th roots of unity.\\
Let $h(x)$ be an irreducible factor of $\Phi_r(x) (\mod p)$.
-/

/-
Lemma 4.3
\begin{lemma}
   Suppose that $f(x), g(x) \in \mathbb{Z}[x]$ with $f(x) \equiv g(x) \mod (p, h(x))$ and that the reductions of $f$ and $g$ in $\mathbb{F}$ both belong to $G$. If $f$ and $g$ both have degree $< |R|$, then $f(x) equiv g(x) (\mod p)$
\end{lemma}
-/
def first_condition (n : ℕ) : Prop :=
  ∀  (a b : ℕ),a ≠ n → 2 ≤ b → a^b ≠ n

def seccond_condition (n r : ℕ) : Prop :=
   ∀ b ≤ r, b ∉ Nat.primeFactors n

variable (n : ℕ)
#check AdjoinRoot.mk (X^r -1 : (ZMod n)[X])

variable(a : ℕ+)
def third_condition (n r : ℕ) : Prop :=
  ∀ a:ℕ+, a ≤ Int.floor (Real.sqrt r)*(Real.log n) → AdjoinRoot.mk (X^r -1 : (ZMod n)[X]) ((X: (ZMod n)[X]) + (C a: (ZMod n)[X]))^n = AdjoinRoot.mk (X^r -1 : (ZMod n)[X]) ((X^n:(ZMod n)[X]) + (C a: (ZMod n)[X]))
--  ∀ a:ℕ+, a ≤ Int.floor (Real.sqrt r)*(Real.log n) → (((X: (ZMod n)[X]) +  (C a: (ZMod n)[X])) : AdjoinRoot.mk (X^r -1 : (ZMod n)[X]))^n = (X^n + (C a: (ZMod n)[X]))

--  ∀ (a:ℕ+), ((a : ℕ) : ℤ) ≤ Int.floor ((Real.sqrt r)*(Real.log n)) → ((((X : (ZMod n)[X]) + (C (a : ZMod n) : (ZMod n)[X])):AdjoinRoot (X^r - 1 : (ZMod n)[X])))^n = (((X^n : (ZMod n)[X]) + (C (a : ZMod n) : (ZMod n)[X])) : AdjoinRoot (X^r - 1 : (ZMod n)[X]))
--   ∀ (a:ℕ+), ((a : ℕ) : ℤ) ≤ Int.floor ((Real.sqrt r)*(Real.log n)) → ((((X:(ZMod n)[X]) + (C a :(ZMod n)[X])): AdjoinRoot (X^r -1 : (ZMod n)[X])))^n = ((X^n:(ZMod n)[X]) + (C a: (ZMod n)[X]))
--  ∀ a ≤ (Real.sqrt r) * (Real.log n), ((AdjoinRoot.of (X : (ZMod n)[X]) +
--  AdjoinRoot.of (C a : (ZMod n)[X]))^n: AdjoinRoot (X^r - 1 : (ZMod n)[X])) = ((AdjoinRoot.of (X^n : (ZMod n)[X]) + AdjoinRoot.of (C a : (ZMod n)[X])): AdjoinRoot (X^r - 1 : (ZMod n)[X]))

--   Polynomial.mod ((X + a: (ZMod n)[X] )^n) (X^r - 1) = (X^n + a)


theorem AKS_Primality_Test {R : Type u_1} (n r : ℕ+) (h_ngone: n > 1)
  (h_r_less_than_n : r < n) (h_order : addOrderOf (n: ZMod r) > (Real.log n)^2): n.Prime ↔
  first_condition n ∧ seccond_condition n r ∧ third_condition n r  := by
  constructor
  · intro h
    constructor
    · unfold first_condition
      intro a b
      intro h_a_not_n
      intro h_b_geq_two
      have h_a_pow_b_not_prime : ¬ (a^b).Prime := by
        apply Nat.Prime.not_prime_pow h_b_geq_two
      sorry
--      apply ¬ Nat.Prime.pow_eq_iff h
    · constructor
      · unfold seccond_condition
        simp [Nat.Prime.primeFactors h]
        intro b
        intro h_b_leq_r
        have h_b_l_n : b < n := by
          apply lt_of_le_of_lt h_b_leq_r h_r_less_than_n
        apply ne_of_lt h_b_l_n
      · unfold third_condition
        intro a
        intro h_a_leq
        have name : Fact (Nat.Prime n) := {out := h}
--        unfold AdjoinRoot.mk
        rw[add_pow_char]

        sorry
        --uncomment when third_condition is complete:
/-        unfold third_condition
        intro h_three
        have name : Fact (Nat.Prime n) := {out := h_three}
        rw [add_pow_char]
        simp-/
  · contrapose
    let (p: ℕ)(hp_one: p ∈ Nat.primeFactors n)(hp_two: third_condition p r)
    sorry
