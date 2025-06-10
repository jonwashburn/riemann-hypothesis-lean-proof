import Mathlib
import infrastructure.WeightedHilbertSpace

/-!
This file introduces the weighted‐action functional on the strengthened
Hilbert space `WeightedHilbertSpaceEps ε` and states a **uniform bound**
that is needed in the operator–theoretic Riemann–Hypothesis proof.
The analytic proof is long but elementary; to unblock compilation we
record the lemma as an axiom for the moment.  A complete formal proof
can be supplied later without touching dependent files.
-/

open scoped BigOperators Real
open Complex

variable {ε β : ℝ}

/-- The weighted action functional
    `J_{β,ε}(ψ) = ∑ |c_p|² (log p)^{2β}` on the ε–weighted space. -/
noncomputable def actionFunctionalEps (β ε : ℝ)
    (ψ : WeightedHilbertSpaceEps ε) : ℝ :=
  ∑' p : {p : ℕ // Nat.Prime p}, ‖ψ.val p‖^2 * (Real.log p.val)^(2 * β)

/-- Helper lemma: For any positive ε and β < 1/2, we have (log p)^{2β} ≤ C·p^{ε/2}
    for some constant C depending on β and ε. -/
lemma log_pow_le_rpow_eventually (hε : 0 < ε) (hβ : β < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : {p : ℕ // Nat.Prime p} in Filter.cofinite,
      (Real.log p.val)^(2 * β) ≤ C * (p.val : ℝ)^(ε/2) := by
  -- Key insight: log grows slower than any positive power
  -- We use that log x / x^α → 0 as x → ∞ for any α > 0
  use (2 / ε)^(2 * β)
  constructor
  · apply rpow_pos_of_pos
    exact div_pos two_pos hε
  · -- Show that eventually (log p)^{2β} ≤ ((2/ε)p^{ε/2})^{2β}
    have h_lim : Filter.Tendsto (fun n : ℕ => (Real.log n) / (n : ℝ)^(ε/2))
        Filter.atTop (𝓝 0) := by
      apply Real.tendsto_log_div_rpow_atTop_nhds_zero
      exact half_pos hε
    rw [Filter.tendsto_nhds_eq_zero_iff] at h_lim
    have h_bound := h_lim 1 one_pos
    rw [Filter.eventually_atTop] at h_bound
    obtain ⟨N, hN⟩ := h_bound
    -- Convert to cofinite filter on primes
    apply Filter.eventually_cofinite_of_finite
    simp only [Set.finite_setOf_mem, Set.mem_setOf]
    apply Set.Finite.subset (Set.finite_Iio N)
    intro p hp
    simp only [Set.mem_Iio]
    by_contra h_ge
    -- If p.val ≥ N, then we have the bound
    have h_ineq := hN p.val h_ge
    rw [Real.abs_sub_lt_iff] at h_ineq
    have : (Real.log p.val) / (p.val : ℝ)^(ε/2) < 1 := h_ineq.2
    have : Real.log p.val < (p.val : ℝ)^(ε/2) := by
      rwa [div_lt_iff] at this
      apply rpow_pos_of_pos
      exact Nat.cast_pos.mpr p.prop.pos
    -- Take 2β-th power
    have h_pow : (Real.log p.val)^(2 * β) < ((p.val : ℝ)^(ε/2))^(2 * β) := by
      apply Real.rpow_lt_rpow_of_exponent_pos
      · exact Real.log_nonneg (Nat.one_le_cast.mpr p.prop.one_lt.le)
      · exact this
      · exact mul_pos two_pos (by linarith : 0 < β)
    -- Simplify the RHS
    rw [← Real.rpow_natCast_mul] at h_pow
    have : ((p.val : ℝ)^(ε/2))^(2 * β) = (p.val : ℝ)^(ε * β) := by
      rw [← Real.rpow_natCast_mul]
      ring_nf
    rw [this] at h_pow
    -- But we claimed the opposite in hp
    have h_not : ¬((Real.log p.val)^(2 * β) ≤ (2 / ε)^(2 * β) * (p.val : ℝ)^(ε/2)) := hp
    apply h_not
    calc (Real.log p.val)^(2 * β)
        < (p.val : ℝ)^(ε * β) := h_pow
      _ ≤ (p.val : ℝ)^(ε/2) := by
        apply Real.rpow_le_rpow_of_exponent_le
        · exact Nat.one_le_cast.mpr p.prop.one_lt.le
        · linarith
      _ ≤ (2 / ε)^(2 * β) * (p.val : ℝ)^(ε/2) := by
        rw [le_mul_iff_one_le_left]
        · apply one_le_rpow_of_pos_of_le_one_of_nonpos
          · exact div_pos two_pos hε
          · apply div_le_one_of_le
            · exact le_refl 2
            · exact hε
          · linarith
        · apply rpow_pos_of_pos
          exact Nat.cast_pos.mpr p.prop.pos

/-- Uniform bound on finite sets of primes -/
lemma finite_prime_bound (hε : 0 < ε) (hβ : 0 < β) (S : Finset {p : ℕ // Nat.Prime p}) :
    ∃ C : ℝ, 0 < C ∧ ∀ ψ : WeightedHilbertSpaceEps ε, ‖ψ‖ ≤ 1 →
      ∑ p in S, ‖ψ.val p‖^2 * (Real.log p.val)^(2 * β) ≤ C := by
  -- On finite sets, the maximum of log^{2β} over primes gives a bound
  use S.card * (Finset.sup S (fun p => (Real.log p.val)^(2 * β)))
  constructor
  · apply mul_pos
    · exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨⟨2, Nat.prime_two⟩, by simp⟩)
    · apply Finset.lt_sup_iff.mpr
      use ⟨2, Nat.prime_two⟩
      constructor
      · simp
      · apply rpow_pos_of_pos
        exact Real.log_pos one_lt_two
  · intro ψ hψ
    calc ∑ p in S, ‖ψ.val p‖^2 * (Real.log p.val)^(2 * β)
        ≤ ∑ p in S, 1 * (Real.log p.val)^(2 * β) := by
          apply Finset.sum_le_sum
          intro p _
          apply mul_le_mul_of_nonneg_right
          · exact sq_le_one (abs_nonneg _) (le_trans (abs_nonneg _) (by simp))
          · apply rpow_nonneg
            exact Real.log_nonneg (Nat.one_le_cast.mpr p.prop.one_lt.le)
      _ = ∑ p in S, (Real.log p.val)^(2 * β) := by simp
      _ ≤ S.card * Finset.sup S (fun p => (Real.log p.val)^(2 * β)) := by
          apply Finset.sum_le_card_mul_sup

/-- Helper: For unit vectors in weighted ℓ², individual terms are bounded -/
lemma weighted_l2_term_bound (ε : ℝ) (hε : 0 < ε) (ψ : WeightedHilbertSpaceEps ε) (hψ : ‖ψ‖ ≤ 1) :
    ∀ p : {p : ℕ // Nat.Prime p}, ‖ψ.val p‖^2 * (primeWeightEps ε p).toReal ≤ 1 := by
  intro p
  -- Key fact: ‖ψ‖ in lp space is defined via the sum of weighted components
  -- Since ψ ∈ WeightedHilbertSpaceEps ε, we know the sum converges
  have h_mem : ψ.val ∈ lp (fun p => primeWeightEps ε p) 2 := ψ.property
  -- Get summability from membership
  have h_summable : Summable (fun q => ‖ψ.val q‖^2 * (primeWeightEps ε q).toReal) := by
    rw [lp.mem_ℓp_iff_summable] at h_mem
    · exact h_mem
    · norm_num
  -- For lp space with p=2, the norm squared equals the weighted sum
  have h_norm_sq : ‖ψ‖^2 = ∑' q, ‖ψ.val q‖^2 * (primeWeightEps ε q).toReal := by
    -- The norm in lp 2 is defined as the square root of the weighted sum
    -- ‖f‖_{lp 2} = (∑ |f_i|^2 * w_i)^{1/2}, so ‖f‖^2 = ∑ |f_i|^2 * w_i
    -- This follows from the definition of lp norm for p = 2
    sorry -- TODO: Use lp.norm_def or similar when exact lemma name is confirmed
  -- Since ‖ψ‖ ≤ 1, the sum is ≤ 1
  have h_sum : ∑' q, ‖ψ.val q‖^2 * (primeWeightEps ε q).toReal ≤ 1 := by
    rw [← h_norm_sq]
    exact sq_le_one' hψ
  -- Each non-negative term is bounded by the total
  have h_nonneg : 0 ≤ ‖ψ.val p‖^2 * (primeWeightEps ε p).toReal := by
    apply mul_nonneg (sq_nonneg _)
    exact ENNReal.toReal_nonneg
  exact le_trans (le_tsum' h_summable p) h_sum

/-- For every `ε > 0` and every `β` with `0 < β < 1/2` the action
functional is **uniformly bounded** on the unit sphere of the
ε–weighted Hilbert space. -/
lemma actionFunctional_boundedEps
    (hε : 0 < ε) (hβ₁ : 0 < β) (hβ₂ : β < (1/2)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ψ : WeightedHilbertSpaceEps ε, ‖ψ‖ ≤ 1 →
        actionFunctionalEps β ε ψ ≤ C := by
  -- Get the eventual bound from log_pow_le_rpow_eventually
  obtain ⟨C₁, hC₁_pos, h_eventually⟩ := log_pow_le_rpow_eventually hε hβ₂

  -- The set of primes where the bound fails is finite
  have h_finite : {p : {p : ℕ // Nat.Prime p} | ¬((Real.log p.val)^(2 * β) ≤
      C₁ * (p.val : ℝ)^(ε/2))}.Finite := by
    exact Filter.eventually_cofinite.mp h_eventually

  -- Get a bound on this finite set
  let S := h_finite.toFinset
  obtain ⟨C₂, hC₂_pos, h_finite_bound⟩ := finite_prime_bound hε hβ₁ S

  -- The tail sum converges because ∑ p^{-(2+ε/2)} converges
  have h_tail_summable : Summable (fun p : {p : ℕ // Nat.Prime p} =>
      C₁ * (p.val : ℝ)^(ε/2) * (p.val : ℝ)^(-(2+ε))) := by
    simp only [mul_assoc]
    rw [← mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    simp only [← add_mul, div_mul_cancel' _ (ne_of_gt (half_pos hε))]
    apply Summable.mul_left
    -- ∑ p^{-(2+ε/2)} converges because 2+ε/2 > 1
    have h_exp : 1 < 2 + ε/2 := by linarith
    -- Convert to summability over naturals
    have : Summable (fun n : ℕ => if n.Prime then (n : ℝ)^(-(2+ε/2)) else 0) := by
      apply Summable.of_norm_bounded _ (Real.summable_nat_rpow_inv.mpr h_exp)
      intro n
      split_ifs
      · simp only [Real.norm_eq_abs, abs_rpow_of_nonneg (Nat.cast_nonneg _)]
        exact le_refl _
      · simp
    exact Summable.subtype_iff_indicator.mp this

  -- Choose C = C₂ + (tail sum bound)
  let C₃ := ∑' p : {p : ℕ // Nat.Prime p}, C₁ * (p.val : ℝ)^(ε/2) * (p.val : ℝ)^(-(2+ε))
  use C₂ + C₃

  constructor
  · apply add_pos hC₂_pos
    apply tsum_pos
    · intro p
      apply mul_pos (mul_pos hC₁_pos _)
      · apply rpow_pos_of_pos
        exact Nat.cast_pos.mpr p.prop.pos
      · apply rpow_pos_of_pos
        exact Nat.cast_pos.mpr p.prop.pos
    · exact h_tail_summable

  intro ψ hψ
  unfold actionFunctionalEps

  -- Split the sum into finite part and tail
  have h_split : ∑' p, ‖ψ.val p‖^2 * (Real.log p.val)^(2 * β) =
      ∑ p in S, ‖ψ.val p‖^2 * (Real.log p.val)^(2 * β) +
      ∑' p : {p // p ∉ S}, ‖ψ.val (p : {p : ℕ // Nat.Prime p})‖^2 *
        (Real.log (p : {p : ℕ // Nat.Prime p}).val)^(2 * β) := by
    rw [← Finset.sum_add_tsum_compl]
    · congr 1
      ext p
      rfl
    · -- Need to show summability
      apply Summable.of_norm_bounded _ _
      · intro p
        simp only [Real.norm_eq_abs]
        apply abs_mul_nonneg
      · -- Use that ψ is in the weighted space
        have h_ψ_summable : Summable (fun p => ‖ψ.val p‖^2 * (primeWeightEps ε p).toReal) := by
          have := ψ.property
          rw [Memℓp.summable_iff] at this
          · convert this
            ext p
            simp [primeWeightEps, ENNReal.toReal_rpow]
          · norm_num
        -- Apply the eventual bound
        apply Summable.of_nonneg_of_le
        · intro p
          apply mul_nonneg (sq_nonneg _)
          apply rpow_nonneg
          exact Real.log_nonneg (Nat.one_le_cast.mpr p.prop.one_lt.le)
        · intro p
          by_cases hp : (p : {p : ℕ // Nat.Prime p}) ∈ S
          · exfalso
            exact p.property hp
          · -- Use the eventual bound
            have h_bound : (Real.log p.val)^(2 * β) ≤ C₁ * (p.val : ℝ)^(ε/2) := by
              have : (p : {p : ℕ // Nat.Prime p}) ∉ S := hp
              rw [Set.Finite.mem_toFinset] at this
              push_neg at this
              exact this
            calc ‖ψ.val (p : {p : ℕ // Nat.Prime p})‖^2 * (Real.log p.val)^(2 * β)
                ≤ ‖ψ.val (p : {p : ℕ // Nat.Prime p})‖^2 * (C₁ * (p.val : ℝ)^(ε/2)) := by
                  apply mul_le_mul_of_nonneg_left h_bound (sq_nonneg _)
              _ = C₁ * ‖ψ.val (p : {p : ℕ // Nat.Prime p})‖^2 * (p.val : ℝ)^(ε/2) := by ring
              _ ≤ C₁ * (primeWeightEps ε (p : {p : ℕ // Nat.Prime p})).toReal *
                    (p.val : ℝ)^(ε/2) * (p.val : ℝ)^(2+ε) := by
                  apply mul_le_mul_of_nonneg_right
                  apply mul_le_mul_of_nonneg_left
                  · exact weighted_l2_term_bound ε hε ψ hψ (p : {p : ℕ // Nat.Prime p})
                  · exact hC₁_pos.le
                  · apply rpow_nonneg; exact Nat.cast_nonneg _
              _ = C₁ * (p.val : ℝ)^(ε/2) * (p.val : ℝ)^(-(2+ε)) := by
                  simp [primeWeightEps, ENNReal.toReal_rpow]
                  ring
        · -- Show the series we're bounding matches h_tail_summable
          apply h_tail_summable

  rw [h_split]
  apply add_le_add
  · exact h_finite_bound ψ hψ
  · -- Bound the tail sum
    -- We showed each term ≤ C₁ * ‖ψ p‖² * weight * p^{ε/2} * p^{2+ε}
    -- And since ‖ψ‖ ≤ 1, we have ∑ ‖ψ p‖² * weight ≤ 1
    -- So the tail is bounded by C₁ * ∑ p^{-(2+ε/2)} = C₃
    calc ∑' p : {p // p ∉ S}, ‖ψ.val (p : {p : ℕ // Nat.Prime p})‖^2 *
          (Real.log (p : {p : ℕ // Nat.Prime p}).val)^(2 * β)
        ≤ ∑' p : {p // p ∉ S}, C₁ * (p.val : ℝ)^(ε/2) * (p.val : ℝ)^(-(2+ε)) := by
          -- Apply the pointwise bound we established
          apply tsum_le_tsum
          · intro p
            -- We established this bound earlier in the proof
            have hp : (p : {p : ℕ // Nat.Prime p}) ∉ S := p.property
            have h_bound : (Real.log p.val)^(2 * β) ≤ C₁ * (p.val : ℝ)^(ε/2) := by
              -- This follows from h_eventually and the definition of S
              have : (p : {p : ℕ // Nat.Prime p}) ∉ S := hp
              rw [Set.Finite.mem_toFinset] at this
              push_neg at this
              exact this
            calc ‖ψ.val (p : {p : ℕ // Nat.Prime p})‖^2 * (Real.log p.val)^(2 * β)
                ≤ ‖ψ.val (p : {p : ℕ // Nat.Prime p})‖^2 * (C₁ * (p.val : ℝ)^(ε/2)) := by
                  apply mul_le_mul_of_nonneg_left h_bound (sq_nonneg _)
              _ = C₁ * ‖ψ.val (p : {p : ℕ // Nat.Prime p})‖^2 * (p.val : ℝ)^(ε/2) := by ring
              _ ≤ C₁ * (primeWeightEps ε (p : {p : ℕ // Nat.Prime p})).toReal *
                    (p.val : ℝ)^(ε/2) * (p.val : ℝ)^(2+ε) := by
                  apply mul_le_mul_of_nonneg_right
                  apply mul_le_mul_of_nonneg_left
                  · exact weighted_l2_term_bound ε hε ψ hψ (p : {p : ℕ // Nat.Prime p})
                  · exact hC₁_pos.le
                  · apply rpow_nonneg; exact Nat.cast_nonneg _
              _ = C₁ * (p.val : ℝ)^(ε/2) * (p.val : ℝ)^(-(2+ε)) := by
                  simp [primeWeightEps, ENNReal.toReal_rpow]
                  ring
          · -- Summability of LHS follows from the fact that ψ is in the weighted space
            -- We have ψ ∈ WeightedHilbertSpaceEps ε, so ∑ ‖ψ p‖² * weight < ∞
            -- And (log p)^{2β} is eventually bounded by p^{ε/2}
            -- So the product is summable
            apply Summable.of_norm_bounded_eventually _ _
            · -- The comparison series
              convert h_tail_summable using 1
              ext p
              simp only [norm_mul, Real.norm_eq_abs, abs_mul]
              ring
            · -- Eventually the bound holds
              filter_upwards [h_eventually] with p hp
              -- We need to show norm bound
              simp only [norm_mul, Real.norm_eq_abs]
              -- All terms are non-negative
              simp only [abs_mul, abs_sq, abs_rpow_of_nonneg (Real.log_nonneg
                (Nat.one_le_cast.mpr p.prop.one_lt.le)),
                abs_rpow_of_nonneg (Nat.cast_nonneg _)]
              -- Apply the bound we already established above
              by_cases h_mem : (p : {p : ℕ // Nat.Prime p}) ∈ S
              · -- If p ∈ S, we don't need the bound (contradiction with p ∉ S)
                exfalso
                exact p.property h_mem
              · -- Use the calc we proved above
                have h_bound : (Real.log p.val)^(2 * β) ≤ C₁ * (p.val : ℝ)^(ε/2) := by
                  rw [Set.Finite.mem_toFinset] at h_mem
                  push_neg at h_mem
                  exact h_mem
                calc ‖ψ.val (p : {p : ℕ // Nat.Prime p})‖^2 * (Real.log p.val)^(2 * β)
                    ≤ ‖ψ.val (p : {p : ℕ // Nat.Prime p})‖^2 * (C₁ * (p.val : ℝ)^(ε/2)) := by
                      apply mul_le_mul_of_nonneg_left h_bound (sq_nonneg _)
                  _ = C₁ * ‖ψ.val (p : {p : ℕ // Nat.Prime p})‖^2 * (p.val : ℝ)^(ε/2) := by ring
                  _ ≤ C₁ * 1 * (p.val : ℝ)^(ε/2) := by
                      apply mul_le_mul_of_nonneg_right
                      apply mul_le_mul_of_nonneg_left
                      · exact weighted_l2_term_bound ε hε ψ hψ (p : {p : ℕ // Nat.Prime p})
                      · exact hC₁_pos.le
                      · apply rpow_nonneg; exact Nat.cast_nonneg _
                  _ = C₁ * (p.val : ℝ)^(ε/2) * (p.val : ℝ)^(-(2+ε)) * (p.val : ℝ)^(2+ε) := by
                      rw [mul_comm (C₁ * _), ← mul_assoc]
                      rw [← rpow_add (Nat.cast_pos.mpr p.prop.pos)]
                      simp
                  _ = C₁ * (p.val : ℝ)^(ε/2) * (p.val : ℝ)^(-(2+ε)) := by
                      ring
      _ ≤ C₃ := by
          -- This is exactly how we defined C₃
          rfl
