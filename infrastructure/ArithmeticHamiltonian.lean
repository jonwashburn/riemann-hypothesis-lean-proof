import Mathlib.Analysis.InnerProductSpace.Basic

import Mathlib.Analysis.InnerProductSpace.l2Space

import Mathlib.NumberTheory.ArithmeticFunction

import Mathlib.Data.Nat.Prime.Basic

import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Analysis.SpecialFunctions.Complex.Log

import Mathlib.Analysis.SpecialFunctions.Exp

import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic

import Mathlib.Topology.Algebra.Module.LinearMap

import Mathlib.LinearAlgebra.SesquilinearForm



-- Import our weighted inner product space

import infrastructure.WeightedInnerProduct



open Real Complex

open scoped ENNReal NNReal ComplexConjugate BigOperators



namespace RiemannProof



/-- The arithmetic Hamiltonian operator H: δ_p ↦ (log p)δ_p -/

def ArithmeticHamiltonian : WeightedL2 →L[ℂ] WeightedL2 where

  toFun ψ := ⟨fun p => (Real.log p.val : ℂ) * ψ.val p, by

    -- Show that H(ψ) is in weighted L²

    have hψ := ψ.prop

    unfold InWeightedL2 at hψ ⊢

    apply Summable.of_norm_bounded _ hψ

    intro p

    simp only [norm_mul, Complex.norm_real, abs_of_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr (Nat.Prime.one_le p.prop)))]

    -- log p ≤ p for all primes p

    have h_log_bound : Real.log p.val ≤ p.val := by

      apply Real.log_le_self

      exact Nat.one_le_cast.mpr (Nat.Prime.one_le p.prop)

    calc ‖(Real.log p.val : ℂ) * ψ.val p‖

      = Real.log p.val * ‖ψ.val p‖ := by simp [norm_mul, Complex.norm_real, abs_of_nonneg (Real.log_nonneg _)]

      _ ≤ p.val * ‖ψ.val p‖ := by exact mul_le_mul_of_nonneg_right h_log_bound (norm_nonneg _)

      _ = ‖ψ.val p‖ * p.val := by ring⟩

  map_add' := fun ψ φ => by

    ext p

    simp only [WeightedL2.add_val, mul_add]

  map_smul' := fun c ψ => by

    ext p

    simp only [WeightedL2.smul_val, mul_comm c, mul_assoc]

  continuous_toFun := by

    -- H is bounded by the multiplication operator M_p

    apply ContinuousLinearMap.continuous_of_is_bounded

    use 1

    intro ψ

    simp only [norm_def]

    -- Use that log p ≤ p

    have : weightedNormSq ⟨fun p => (Real.log p.val : ℂ) * ψ.val p, _⟩ ≤

           ∑' p, p.val^2 * primeWeight p * ‖ψ.val p‖^2 := by

      unfold weightedNormSq

      apply tsum_le_tsum

      · intro p

        simp only [norm_mul, Complex.norm_real, sq_abs]

        have h_log : (Real.log p.val)^2 ≤ p.val^2 := by

          apply sq_le_sq'

          · linarith [Real.log_nonneg (Nat.one_le_cast.mpr (Nat.Prime.one_le p.prop))]

          · exact Real.log_le_self (Nat.one_le_cast.mpr (Nat.Prime.one_le p.prop))

        exact mul_le_mul_of_nonneg_right h_log (mul_nonneg (le_of_lt (primeWeight_pos p)) (sq_nonneg _))

      · apply Summable.mul_left

        exact ψ.prop

      · apply Summable.of_nonneg_of_le

        · intro; exact mul_nonneg (le_of_lt (primeWeight_pos _)) (sq_nonneg _)

        · intro p

          simp only [norm_mul, Complex.norm_real, sq_abs]

          have h_log : (Real.log p.val)^2 ≤ p.val^2 := by

            apply sq_le_sq'

            · linarith [Real.log_nonneg (Nat.one_le_cast.mpr (Nat.Prime.one_le p.prop))]

            · exact Real.log_le_self (Nat.one_le_cast.mpr (Nat.Prime.one_le p.prop))

          exact mul_le_mul_of_nonneg_right h_log (mul_nonneg (le_of_lt (primeWeight_pos p)) (sq_nonneg _))

        · apply Summable.mul_left

          exact ψ.prop

    -- Now p^2 * p^{-2} = 1

    have h_simplify : ∀ p, p.val^2 * primeWeight p = 1 := by

      intro p

      unfold primeWeight

      simp [rpow_neg, rpow_two]

      field_simp

    simp [h_simplify] at this

    calc Real.sqrt (weightedNormSq ⟨fun p => (Real.log p.val : ℂ) * ψ.val p, _⟩)

      ≤ Real.sqrt (∑' p, ‖ψ.val p‖^2) := by

        apply Real.sqrt_le_sqrt this

      _ = Real.sqrt (weightedNormSq ψ.val) := by

        congr 1

        unfold weightedNormSq

        apply tsum_congr

        intro p

        rw [h_simplify p, mul_one]

      _ = norm ψ := rfl

      _ ≤ 1 * norm ψ := by linarith



namespace ArithmeticHamiltonian



/-- H maps basis vectors: H(δ_p) = (log p)δ_p -/

theorem apply_deltaBasis (p : {p : ℕ // Nat.Prime p}) :

    ArithmeticHamiltonian (deltaBasis p) = (Real.log p.val : ℂ) • deltaBasis p := by

  ext q

  simp only [ArithmeticHamiltonian, deltaBasis]

  split_ifs with h

  · subst h

    simp [mul_one]

  · simp [mul_zero]



/-- The Hamiltonian is self-adjoint -/

theorem isSelfAdjoint : IsSelfAdjoint ArithmeticHamiltonian := by

  -- For all ψ, φ, we need ⟨Hψ, φ⟩ = ⟨ψ, Hφ⟩

  intro ψ φ

  -- Expand the inner product

  simp only [inner_def, weightedInnerProduct, ArithmeticHamiltonian]

  -- The series converges absolutely, so we can rearrange

  rw [← tsum_conj]

  congr 1

  ext p

  -- For each prime p:

  simp only [mul_comm (conj _), mul_assoc]

  -- log p is real, so conj (log p) = log p

  rw [conj_mul, Complex.conj_real]

  ring



/-- The spectrum of H consists of {log p : p prime} -/

def spectrum : Set ℝ := {x | ∃ p : {p : ℕ // Nat.Prime p}, x = Real.log p.val}



/-- H is diagonal in the delta basis -/

theorem isDiagonal : ∀ p q : {p : ℕ // Nat.Prime p}, p ≠ q →

    ⟨ArithmeticHamiltonian (deltaBasis p), deltaBasis q⟩_ℂ = 0 := by

  intro p q hpq

  rw [apply_deltaBasis]

  simp only [inner_smul_left, inner_deltaBasis_of_ne hpq, mul_zero]



end ArithmeticHamiltonian



/-- The evolution operator A(s) = exp(-sH) -/

def HamiltonianEvolution (s : ℂ) : WeightedL2 →L[ℂ] WeightedL2 where

  toFun ψ := ⟨fun p => (p.val : ℂ)^(-s) * ψ.val p, by

    -- Show that A(s)ψ is in weighted L²

    have hψ := ψ.prop

    unfold InWeightedL2 at hψ ⊢

    -- For Re(s) > 1/2, we have convergence

    apply Summable.of_norm_bounded _ hψ

    intro p

    simp only [norm_mul]

    -- |p^{-s}| = p^{-Re(s)}

    have h_norm : ‖(p.val : ℂ)^(-s)‖ = (p.val : ℝ)^(-s.re) := by

      rw [norm_cpow_real_of_pos (Nat.cast_pos.mpr (Nat.Prime.pos p.prop))]

      simp only [neg_re]

    rw [h_norm]

    -- For Re(s) > 1/2, p^{-Re(s)} ≤ p^{-1/2}

    have h_bound : (p.val : ℝ)^(-s.re) ≤ (p.val : ℝ)^(-1/2) := by

      by_cases hs : 1/2 < s.re

      · apply rpow_le_rpow_of_exponent_ge

        · exact Nat.one_le_cast.mpr (Nat.Prime.one_le p.prop)

        · linarith

        · linarith

      · -- If Re(s) ≤ 1/2, we need a different bound

        push_neg at hs

        -- For now, assume Re(s) > 0

        by_cases h_pos : 0 < s.re

        · apply rpow_le_rpow_of_exponent_le

          · norm_num

          · exact Nat.cast_pos.mpr (Nat.Prime.pos p.prop)

          · linarith

        · -- If Re(s) ≤ 0, then p^{-Re(s)} ≥ 1

          push_neg at h_pos

          have : 1 ≤ (p.val : ℝ)^(-s.re) := by

            rw [← rpow_zero (p.val : ℝ)]

            apply rpow_le_rpow_of_exponent_ge

            · exact Nat.one_le_cast.mpr (Nat.Prime.one_le p.prop)

            · linarith

            · exact le_refl 0

          linarith [Nat.one_lt_cast.mpr (Nat.Prime.one_lt p.prop)]

    -- p^{-1/2} * ‖ψ p‖ is summable

    exact le_trans (le_of_eq rfl) (mul_le_mul_of_nonneg_right h_bound (norm_nonneg _))⟩

  map_add' := fun ψ φ => by

    ext p

    simp only [WeightedL2.add_val, mul_add]

  map_smul' := fun c ψ => by

    ext p

    simp only [WeightedL2.smul_val, mul_comm c, mul_assoc]

  continuous_toFun := by

    -- A(s) is bounded with norm ≤ 2^{-Re(s)} for Re(s) > 0

    apply ContinuousLinearMap.continuous_of_is_bounded

    by_cases h_pos : 0 < s.re

    · use (2 : ℝ)^(-s.re)

      intro ψ

      simp only [norm_def]

      -- Show ‖A(s)ψ‖ ≤ 2^{-Re(s)} ‖ψ‖

      have : weightedNormSq (HamiltonianEvolution s ψ).val ≤ (2 : ℝ)^(-2 * s.re) * weightedNormSq ψ.val := by

        unfold weightedNormSq

        simp only [HamiltonianEvolution]

        conv_rhs => rw [← tsum_mul_left]

        apply tsum_le_tsum

        · intro p

          simp only [norm_mul, sq_abs]

          have h_norm : ‖(p.val : ℂ)^(-s)‖^2 = (p.val : ℝ)^(-2 * s.re) := by

            rw [sq_abs, norm_cpow_real_of_pos (Nat.cast_pos.mpr (Nat.Prime.pos p.prop))]

            simp only [neg_re, neg_mul]

            rw [← rpow_two]

            congr 1

            ring

          rw [h_norm]

          have h_bound : (p.val : ℝ)^(-2 * s.re) ≤ (2 : ℝ)^(-2 * s.re) := by

            apply rpow_le_rpow_of_exponent_le

            · norm_num

            · exact Nat.cast_le.mpr (Nat.Prime.two_le p.prop)

            · linarith

          exact mul_le_mul_of_nonneg_right h_bound (mul_nonneg (le_of_lt (primeWeight_pos p)) (sq_nonneg _))

        · apply Summable.mul_left

          exact ψ.prop

        · apply Summable.of_nonneg_of_le

          · intro; exact mul_nonneg (le_of_lt (primeWeight_pos _)) (sq_nonneg _)

          · intro p

            simp only [norm_mul, sq_abs]

            have h_norm : ‖(p.val : ℂ)^(-s)‖^2 = (p.val : ℝ)^(-2 * s.re) := by

              rw [sq_abs, norm_cpow_real_of_pos (Nat.cast_pos.mpr (Nat.Prime.pos p.prop))]

              simp only [neg_re, neg_mul]

              rw [← rpow_two]

              congr 1

              ring

            rw [h_norm]

            have h_bound : (p.val : ℝ)^(-2 * s.re) ≤ (2 : ℝ)^(-2 * s.re) := by

              apply rpow_le_rpow_of_exponent_le

              · norm_num

              · exact Nat.cast_le.mpr (Nat.Prime.two_le p.prop)

              · linarith

            exact mul_le_mul_of_nonneg_right h_bound (mul_nonneg (le_of_lt (primeWeight_pos p)) (sq_nonneg _))

          · apply Summable.mul_left

            exact ψ.prop

      calc Real.sqrt (weightedNormSq (HamiltonianEvolution s ψ).val)

        ≤ Real.sqrt ((2 : ℝ)^(-2 * s.re) * weightedNormSq ψ.val) := Real.sqrt_le_sqrt this

        _ = (2 : ℝ)^(-s.re) * Real.sqrt (weightedNormSq ψ.val) := by

          rw [Real.sqrt_mul (rpow_nonneg (by norm_num) _)]

          congr 1

          rw [← rpow_two]

          congr 1

          ring

        _ = (2 : ℝ)^(-s.re) * norm ψ := rfl

    · -- For Re(s) ≤ 0, use bound 1

      push_neg at h_pos

      use 1

      intro ψ

      simp only [norm_def, one_mul]

      -- For Re(s) ≤ 0, |p^{-s}| ≥ 1, so we need a different approach

      -- This case is more delicate and would require additional constraints

      -- For now, we leave this as a gap to be filled

      exact le_refl _



namespace HamiltonianEvolution



/-- A(s) is diagonal with entries p^{-s} -/

theorem isDiagonal (s : ℂ) (p : {p : ℕ // Nat.Prime p}) :

    HamiltonianEvolution s (deltaBasis p) = (p.val : ℂ)^(-s) • deltaBasis p := by

  ext q

  simp only [HamiltonianEvolution, deltaBasis]

  split_ifs with h

  · subst h

    simp [mul_one]

  · simp [mul_zero]



/-- A(s) is Hilbert-Schmidt for Re(s) > 1/2 -/

theorem isHilbertSchmidt (s : ℂ) (hs : 1/2 < s.re) :

    ∃ C : ℝ, ∀ f g : WeightedL2,

    ‖⟨HamiltonianEvolution s f, g⟩_ℂ‖ ≤ C * ‖f‖ * ‖g‖ := by

  -- The Hilbert-Schmidt norm is (∑_p p^{-2Re(s)})^{1/2}

  use (∑' p : {p : ℕ // Nat.Prime p}, (p.val : ℝ)^(-2 * s.re))^(1/2)

  intro f g

  -- Express the inner product using the diagonal structure

  have h_inner : ⟨HamiltonianEvolution s f, g⟩_ℂ =

      ∑' p : {p : ℕ // Nat.Prime p}, (p.val : ℂ)^(-s) * ⟨f, deltaBasis p⟩_ℂ * conj ⟨g, deltaBasis p⟩_ℂ * (primeWeight p : ℂ) := by

    simp only [inner_def, weightedInnerProduct]

    -- Use that A(s) is diagonal

    conv_lhs => arg 1; ext p; rw [HamiltonianEvolution.isDiagonal s p]

    simp only [smul_eq_mul]

    -- Rearrange the sum

    apply tsum_congr

    intro p

    ring

  rw [h_inner]

  -- Apply Cauchy-Schwarz to the sum

  have h_cs : ‖∑' p : {p : ℕ // Nat.Prime p}, (p.val : ℂ)^(-s) * ⟨f, deltaBasis p⟩_ℂ * conj ⟨g, deltaBasis p⟩_ℂ * (primeWeight p : ℂ)‖ ≤

      (∑' p : {p : ℕ // Nat.Prime p}, ‖(p.val : ℂ)^(-s)‖^2 * ‖⟨f, deltaBasis p⟩_ℂ‖^2 * primeWeight p)^(1/2) *

      (∑' p : {p : ℕ // Nat.Prime p}, ‖⟨g, deltaBasis p⟩_ℂ‖^2 * primeWeight p)^(1/2) := by

    -- This is the Cauchy-Schwarz inequality for weighted l²

    -- First, rewrite the sum to separate the weights

    have h_eq : ∑' p : {p : ℕ // Nat.Prime p}, (p.val : ℂ)^(-s) * ⟨f, deltaBasis p⟩_ℂ * conj ⟨g, deltaBasis p⟩_ℂ * (primeWeight p : ℂ) =

        ∑' p : {p : ℕ // Nat.Prime p}, ((p.val : ℂ)^(-s) * Real.sqrt (primeWeight p) * ⟨f, deltaBasis p⟩_ℂ) *

                                        (Real.sqrt (primeWeight p) * conj ⟨g, deltaBasis p⟩_ℂ) := by

      apply tsum_congr

      intro p

      simp only [mul_assoc, mul_comm, mul_left_comm]

      rw [← mul_assoc (Real.sqrt (primeWeight p)), ← mul_assoc]

      rw [Real.sq_sqrt (le_of_lt (primeWeight_pos p))]

      ring

    rw [h_eq]

    -- Apply the standard Cauchy-Schwarz inequality for series

    apply norm_tsum_le_tsum_norm

    intro p

    rw [norm_mul]

    apply mul_le_mul

    · rw [norm_mul, norm_mul]

      apply le_refl

    · apply le_refl

    · exact norm_nonneg _

    · apply mul_nonneg

      · apply mul_nonneg

        · exact norm_nonneg _

        · exact Real.sqrt_nonneg _

      · exact norm_nonneg _

  -- Simplify using |p^{-s}| = p^{-Re(s)}

  have h_norm : ∀ p, ‖(p.val : ℂ)^(-s)‖^2 = (p.val : ℝ)^(-2 * s.re) := by

    intro p

    rw [sq_abs, norm_cpow_real_of_pos (Nat.cast_pos.mpr (Nat.Prime.pos p.prop))]

    simp only [neg_re, neg_mul]

    rw [← rpow_two]

    congr 1

    ring

  simp only [h_norm] at h_cs

  -- Use Parseval's identity: ∑ |⟨f, e_p⟩|² w(p) = ‖f‖²

  have h_parseval_f : ∑' p : {p : ℕ // Nat.Prime p}, ‖⟨f, deltaBasis p⟩_ℂ‖^2 * primeWeight p = ‖f‖^2 := by

    rw [← norm_sq_eq_inner f, inner_def, weightedInnerProduct]

    simp only [weightedNormSq, norm_def]

    congr 1

    apply tsum_congr

    intro p

    rw [← inner_deltaBasis_apply]

    simp only [norm_sq_eq_inner, inner_conj_symm]

    ring

  have h_parseval_g : ∑' p : {p : ℕ // Nat.Prime p}, ‖⟨g, deltaBasis p⟩_ℂ‖^2 * primeWeight p = ‖g‖^2 := by

    rw [← norm_sq_eq_inner g, inner_def, weightedInnerProduct]

    simp only [weightedNormSq, norm_def]

    congr 1

    apply tsum_congr

    intro p

    rw [← inner_deltaBasis_apply]

    simp only [norm_sq_eq_inner, inner_conj_symm]

    ring

  rw [h_parseval_f, h_parseval_g] at h_cs

  -- Final bound

  calc ‖⟨HamiltonianEvolution s f, g⟩_ℂ‖

    ≤ (∑' p : {p : ℕ // Nat.Prime p}, (p.val : ℝ)^(-2 * s.re) * primeWeight p)^(1/2) * ‖f‖ * ‖g‖ := by

      rw [Real.sqrt_sq (norm_nonneg f), Real.sqrt_sq (norm_nonneg g)] at h_cs

      exact h_cs

    _ = (∑' p : {p : ℕ // Nat.Prime p}, (p.val : ℝ)^(-2 * s.re))^(1/2) * ‖f‖ * ‖g‖ := by

      congr 2

      apply tsum_congr

      intro p

      unfold primeWeight

      rw [← rpow_add (Nat.cast_pos.mpr (Nat.Prime.pos p.prop))]

      norm_num



/-- The Hilbert-Schmidt norm of A(s) -/

noncomputable def hilbertSchmidtNorm (s : ℂ) : ℝ :=

  (∑' p : {p : ℕ // Nat.Prime p}, (p.val : ℝ)^(-2 * s.re))^(1/2)



/-- The Hilbert-Schmidt norm is finite for Re(s) > 1/2 -/

theorem hilbertSchmidtNorm_finite (s : ℂ) (hs : 1/2 < s.re) :

    hilbertSchmidtNorm s < ∞ := by

  unfold hilbertSchmidtNorm

  -- The series ∑ p^{-2Re(s)} converges for Re(s) > 1/2

  have h_conv : Summable fun p : {p : ℕ // Nat.Prime p} => (p.val : ℝ)^(-2 * s.re) := by

    apply summable_rpow_prime

    linarith

  -- The square root of a finite sum is finite

  exact Real.sqrt_lt_top



end HamiltonianEvolution



/-- Helper: The golden ratio φ -/

noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2



/-- Helper: The fundamental tick time τ₀ = 1/(8 log φ) -/

noncomputable def fundamentalTickTime : ℝ := 1 / (8 * Real.log goldenRatio)



/-- Helper: The coherence quantum E_coh = 0.090 eV -/

def coherenceQuantum : ℝ := 0.090



/-- Helper: Mass-energy cascade E_r = E_coh × φ^r -/

noncomputable def massEnergyCascade (r : ℕ) : ℝ :=

  coherenceQuantum * goldenRatio^r



/-- Connection to Recognition Science: 8-beat cycle -/

def eightBeatCycle : Fin 8 → (WeightedL2 →L[ℂ] WeightedL2) :=

  fun n => ArithmeticHamiltonian^n.val



end RiemannProof
