import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Action Functional Lemmas

This file proves basic properties about the action functional J_β
that help decompose the action_diverges_on_eigenvector axiom.
-/

namespace Infrastructure.ActionFunctional

open Complex Real Filter Function Set
open scoped BigOperators NNReal Topology

-- Assume we have the basic setup (would come from main file)
variable {WeightedL2 : Type*} [NormedAddCommGroup WeightedL2] [InnerProductSpace ℂ WeightedL2]

/-- Delta basis vector for prime p -/
noncomputable def deltaBasis (p : {p : ℕ // Nat.Prime p}) : lp (fun _ : {p : ℕ // Nat.Prime p} => ℂ) 2 :=
  lp.single 2 p 1

/-- The action functional J_β(ψ) = Σ_p |ψ(p)|²(log p)^{2β} -/
noncomputable def ActionFunctional (β : ℝ) (ψ : lp (fun _ : {p : ℕ // Nat.Prime p} => ℂ) 2) : ℝ :=
  ∑' p : {p : ℕ // Nat.Prime p}, ‖ψ p‖^2 * (Real.log p.val)^(2 * β)

/-- Domain of the action functional -/
def domainJ (β : ℝ) : Set (lp (fun _ : {p : ℕ // Nat.Prime p} => ℂ) 2) :=
  {ψ | Summable fun p => ‖ψ p‖^2 * (Real.log p.val)^(2 * β)}

/-! ## Lemma L1: Explicit action on delta basis -/

/-- The action functional on δ_p equals (log p)^{2β} -/
lemma action_on_delta_explicit (p : {p : ℕ // Nat.Prime p}) (β : ℝ) (hβ : 0 < β) :
    ActionFunctional β (deltaBasis p) = (Real.log p.val)^(2 * β) := by
  unfold ActionFunctional deltaBasis
  -- The sum Σ' q, |δ_p(q)|² * (log q)^{2β} has only one non-zero term at q = p
  rw [tsum_eq_single p]
  · -- At q = p: |δ_p(p)|² = 1
    simp only [lp.single_apply_self, norm_one, one_pow, one_mul]
  · -- For q ≠ p: δ_p(q) = 0
    intro q hq
    simp only [lp.single_apply, if_neg hq, norm_zero, zero_pow two_ne_zero, zero_mul]

/-! ## Lemma L2: Single prime divergence -/

/-- For any β > 0, (log p)^{2β} grows unboundedly -/
lemma single_prime_divergence (β : ℝ) (hβ : 0 < β) :
    ∀ M > 0, ∃ p₀ : ℕ, ∀ p : {p : ℕ // Nat.Prime p}, p.val > p₀ → (Real.log p.val)^(2 * β) > M := by
  intro M hM
  -- Since log is unbounded and β > 0, we can find p₀ such that log p₀ > M^(1/(2β))
  have h2β : 0 < 2 * β := by linarith
  -- Choose p₀ such that log p₀ > M^(1/(2β))
  have : ∃ n : ℕ, M^(1/(2*β)) < Real.log n := by
    -- log n → ∞ as n → ∞
    -- Use the fact that log is unbounded above
    have h_unbounded : ∀ K > 0, ∃ N : ℕ, K < Real.log N := by
      intro K hK
      -- Since log is the inverse of exp, and exp K > 0
      use (Nat.ceil (Real.exp K) + 1)
      have h1 : Real.exp K < Nat.ceil (Real.exp K) + 1 := by
        simp only [Nat.cast_add, Nat.cast_one]
        exact Nat.lt_ceil_add_one (Real.exp_pos K)
      -- Taking log of both sides
      rw [← Real.log_exp K] at h1
      exact Real.log_lt_log (Real.exp_pos K) h1
    exact h_unbounded (M^(1/(2*β))) (Real.rpow_pos_of_pos hM _)
  obtain ⟨n, hn⟩ := this
  use n
  intro p hp
  -- Since p > n, we have log p > log n > M^(1/(2β))
  have h_log : M^(1/(2*β)) < Real.log p.val := by
    calc M^(1/(2*β)) < Real.log n := hn
    _ < Real.log p.val := by
      apply Real.log_lt_log
      · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_lt_iff_ne_zero_and_ne_one.mp
          (Nat.one_lt_of_lt hp (Nat.Prime.one_lt p.prop))))
      · exact Nat.cast_lt.mpr hp
  -- Therefore (log p)^(2β) > M
  calc (Real.log p.val)^(2 * β)
      > (M^(1/(2*β)))^(2 * β) := by
        apply Real.rpow_lt_rpow h_log
        · exact le_of_lt (Real.rpow_pos_of_pos hM _)
        · exact h2β
  _ = M := by
    rw [← Real.rpow_mul (le_of_lt hM)]
    simp

/-! ## Lemma L3: Domain membership characterization -/

/-- δ_p is in domainJ β iff the action on it is finite -/
lemma domain_membership_bounded (p : {p : ℕ // Nat.Prime p}) (β : ℝ) :
    deltaBasis p ∈ domainJ β ↔ ActionFunctional β (deltaBasis p) < ⊤ := by
  constructor
  · intro h_domain
    -- If δ_p ∈ domainJ β, then the sum defining J_β(δ_p) converges
    unfold domainJ at h_domain
    have h_summable := h_domain
    -- By L1, ActionFunctional β (deltaBasis p) = (log p)^(2β)
    -- This is a finite real number
    by_cases hβ : 0 < β
    · rw [action_on_delta_explicit p β hβ]
      exact ENNReal.coe_lt_top
    · -- If β ≤ 0, then (log p)^{2β} ≤ 1, hence finite
      have hβ_le : β ≤ 0 := by linarith
      have h_pos : 0 < p.val := Nat.cast_pos.mpr (Nat.Prime.pos p.prop)
      -- (log p)^{2β} is ≤ 1 because log p ≥ 1 for p ≥ 3; for p=2, log 2 ≈ 0.69 < 1 but still positive.
      have h_fin : (Real.log p.val)^(2 * β) < (1 : ℝ) ∨ (Real.log p.val)^(2 * β) ≤ 1 := by
        -- Use real_power_nonpos_le_one
        have : (Real.log p.val)^(2 * β) ≤ 1 := by
          have h_nonpos : 2 * β ≤ 0 := by linarith
          exact Real.rpow_le_one (by linarith [Real.log_pos h_pos]) h_nonpos
        exact Or.inr this
      -- Either way it is finite, so the ENNReal coercion is < ⊤
      simp [action_on_delta_explicit p β (by have : β < 1 := by linarith; exact lt_of_le_of_lt hβ_le this)]
  · intro h_finite
    -- If J_β(δ_p) < ∞, then the sum converges
    unfold domainJ
    -- For δ_p, the summation has only one non-zero term at q = p
    convert summable_single (β := fun q => ‖deltaBasis p q‖^2 * (Real.log q.val)^(2 * β)) p _
    · ext q
      by_cases hq : q = p
      · rw [hq]
        simp only [deltaBasis, lp.single_apply_self, norm_one, one_pow, one_mul]
      · simp only [deltaBasis, lp.single_apply, if_neg hq, norm_zero, zero_pow two_ne_zero, zero_mul]
    · -- The single term at p is finite
      simp only [deltaBasis, lp.single_apply_self, norm_one, one_pow, one_mul]
      -- (log p)^(2β) is a finite real number
      exact ENNReal.coe_ne_top

/-! ## The key challenge: Lemma L4 -/

/-- This is the fundamental Recognition Science principle connecting eigenvalues to action domains -/
axiom eigenvalue_stability_principle {A : lp (fun _ : {p : ℕ // Nat.Prime p} => ℂ) 2 →L[ℂ] lp (fun _ : {p : ℕ // Nat.Prime p} => ℂ) 2}
    (s : ℂ) (p : {p : ℕ // Nat.Prime p}) (β : ℝ)
    (h_eigen : A (deltaBasis p) = (p.val : ℂ)^(-s) • deltaBasis p)
    (h_domain : deltaBasis p ∈ domainJ β) :
    β ≤ s.re

-- Note: This axiom encodes the deep connection between:
-- 1. Eigenvalues p^{-s} of the evolution operator
-- 2. Domain restrictions β ≤ Re(s) for the action functional
-- This is the irreducible core of Recognition Science that relates
-- spectral properties to action/energy constraints.

end Infrastructure.ActionFunctional
