import Mathlib.Tactic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Polynomial.Basic

/- In this file we will start with the proof of the main theorem
of the AKS primality test. The main theorem is:
-/
structure values where
  n : ℕ
  n_geq_two: n ≥ 2
  r : ℕ
  r_nonneg : r ≥ 0
  r_le_n : r < n
  ordergeq: addOrderOf (n : ZMod r) > (Nat.log 10 n)^2


/-
For given integer n ≥ 2, let r be a positive integer < n, for which
n has order > (log n)2 modulo r. Then n is prime if and only if
• n is not a perfect power,
• n does not have any prime factor ≤ r,
• (x + a)n ≡ xn + a mod (n, xr − 1) for each integer a, 1 ≤ a ≤ √r log n.
(x + a)^n ≡  x^n + a mod (p, xr − 1)
for n
-/

-- Construction of the set S

-- A = √r log n
-- p | n, p prime
-- Cyclotomic polynomials Φ_d :
-- x^r -1 = Π_{d|r} Φ_d(X)
-- h(X) irriducible factor of Φ_r(X) in (ℤ/pℤ)[X]
-- 𝔽 :≡ ℤ [X]/(p, h(x)) iso to field of p^m elements
-- m = deg h, 𝔽 - {0} cyclic group of order p^m -1,

def PolyRing_Z_p_Xr (p: ℕ) (r: ℕ ) [Fact p.prime]  := AdjoinRoot (X^r -1 : (ZMod p)[X])
--   and r | p^m-1, because x of order r

-- H = ⟨ X, X+1, X+2, ..., X+[A]⟩ / (p, X^r-1)


def Set_H (p: ℕ )( A : ℕ) (r :ℕ ): Set ℕ := sorry

-- G = ⟨ X, X+1, X+2, ..., X+[A]⟩ / (p, h(X))
-- ? = H/ (h(X))
-- g ∈ G, g ≠ 0
-- g(X) = Π _{0 ≤ a ≤ A}(x+a)^{e_a} ∈ H
-- g(X)^n = g(X^n) mod (p, X^r-1)


-- S = {} k \in \Z : g(X^k) = g(X)^k mod (p, X^r -1)}
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
   ¬IsPrimePow n

def seccond_condition (n r : ℕ) : Prop :=
   ∀ b ≤ r, b ∉ Nat.primeFactors n

open Polynomial

variable(a : ℕ+)
def third_condition (n r : ℕ) : Prop :=
   ∀ a ≤ (Real.sqrt r)*(Real.log n), true
--   Polynomial.mod ((X + a: (ZMod n)[X])^n) (X^r - 1) = X^n + a


theorem AKS_Primality_Test {R : Type u_1} (n r : ℕ+) (h_ngone: n > 1)
  (h_r_less_than_n : r < n) (h_order : addOrderOf (n: ZMod r) > (Real.log n)^2): n.Prime ↔
  first_condition n ∧ seccond_condition n r ∧ third_condition n r  := by sorry
