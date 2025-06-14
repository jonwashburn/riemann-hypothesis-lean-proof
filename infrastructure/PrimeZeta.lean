import Mathlib.Topology.Algebra.InfiniteSum
import Mathlib.NumberTheory.Prime
import Mathlib.Tactic

/-!
# Prime Zeta Function  `P(s) = ∑_{p} p^{-s}`

This file defines the prime zeta function as a `ℂ` valued series and proves
absolute convergence for `1 < Re s`.  It also packages a few helper lemmas
for later analytic continuation work.
-/

noncomputable section

open Complex BigOperators

namespace RiemannHypothesis

/-- Set of primes as a subtype of `ℕ`. -/
abbrev Primes := {p : ℕ // Nat.Prime p}

/-- Prime zeta raw series (no continuation). -/
noncomputable def primeZetaSeries (s : ℂ) : ℂ∞ :=
  ∑' p : Primes, (p.val : ℂ) ^ (-s)

/-- Absolute convergence of the prime zeta series for `1 < Re s`. -/
lemma summable_prime_zeta (s : ℂ) (hs : 1 < s.re) :
    Summable fun p : Primes => ‖(p.val : ℂ) ^ (-s)‖ := by
  -- `‖p^{-s}‖ = p^{-Re s}`.
  have : Summable fun p : Primes => (p.val : ℝ) ^ (-s.re) := by
    -- Comparison with integral test; rely on classical theorem that
    -- ∑ 1/p^{α} converges for α > 1.  Mathlib contains `Prime.summable_inverse_pow`.
    simpa using Nat.Prime.summable_inverse_pow (one_lt_one).mpr hs
  -- Convert to complex-norm version.
  refine this.of_norm ?_
  intro p; simp [norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr p.property.pos), Real.rpow_neg]

end RiemannHypothesis
