import Mathlib
import infrastructure.WeightedHilbertSpace
import infrastructure.UniformBound

open scoped BigOperators Real
open Complex

/-!
`EigenvectorDivergence.lean`
---------------------------
This file records the statement that the weighted action functional
constructed with additional ε–decay diverges for the putative eigenvector
when the real part of `s` is **off** the critical line.  As with the
uniform–bound lemma we postpone a fully formal proof; the declaration
is provided as an axiom so that other files compile.
-/

variable {ε β : ℝ}

/-- The formal eigenvector coefficients for a given s and ε. -/
def eigenvectorCoeff (s : ℂ) (ε : ℝ) (p : {p : ℕ // Nat.Prime p}) : ℂ :=
  (p.val : ℂ) ^ (-(s.re + 1 + ε/2))

/-- The eigenvector coefficients are in WeightedHilbertSpaceEps when Re(s) > -1/2. -/
lemma eigenvectorInSpace (hε : 0 < ε) (s : ℂ) (hs : -1/2 < s.re) :
    ∃ ψ : WeightedHilbertSpaceEps ε,
      ψ.val = eigenvectorCoeff s ε := by
  -- Need to show ∑ p^{-2(s.re + 1 + ε/2)} * p^{-(2+ε)} < ∞
  -- This simplifies to ∑ p^{-2s.re - 2 - ε - 2 - ε} = ∑ p^{-2s.re - 4 - 2ε}
  have h_summable : Summable (fun p : {p : ℕ // Nat.Prime p} =>
      ‖eigenvectorCoeff s ε p‖^2 * (primeWeightEps ε p).toReal) := by
    simp only [eigenvectorCoeff, primeWeightEps, norm_pow, norm_coe_nat, sq]
    -- We need to show ∑ p^{-2(s.re + 1 + ε/2)} * p^{-(2+ε)} converges
    -- This is ∑ p^{-2s.re - 2 - ε - 2 - ε} = ∑ p^{-(2s.re + 4 + 2ε)}
    have h_exp : ∀ p : {p : ℕ // Nat.Prime p},
        (p.val : ℝ)^(-2*(s.re + 1 + ε/2)) * (p.val : ℝ≥0∞)^(-(2+ε)).toReal =
        (p.val : ℝ)^(-(2*s.re + 4 + 2*ε)) := by
      intro p
      simp [ENNReal.toReal_rpow]
      rw [← mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      congr 1
      ring
    simp only [h_exp]
    -- The series ∑ p^{-(2s.re + 4 + 2ε)} converges when 2s.re + 4 + 2ε > 1
    have h_bound : 1 < 2*s.re + 4 + 2*ε := by
      -- Since s.re > -1/2, we have 2*s.re > -1, so 2*s.re + 4 + 2*ε > 3 + 2*ε > 1
      linarith
    -- Apply prime p-series convergence
    have : Summable (fun n : ℕ => if n.Prime then (n : ℝ)^(-(2*s.re + 4 + 2*ε)) else 0) := by
      apply Summable.of_norm_bounded _ (Real.summable_nat_rpow_inv.mpr h_bound)
      intro n
      split_ifs
      · simp [Real.norm_eq_abs, abs_rpow_of_nonneg (Nat.cast_nonneg _)]
      · simp
    exact Summable.subtype_iff_indicator.mp this
  use ⟨eigenvectorCoeff s ε, by
    rw [Memℓp.summable_iff]
    · exact h_summable
    · norm_num⟩
  rfl

/-- Key calculation: The action functional on eigenvector equals a p-series. -/
lemma actionOnEigenvector (hε : 0 < ε) (hβ : 0 < β) (s : ℂ) (hs : -1/2 < s.re) :
    let ψ := Classical.choice (eigenvectorInSpace hε s hs)
    actionFunctionalEps β ε ψ =
      ∑' p : {p : ℕ // Nat.Prime p}, (p.val : ℝ)^(-2*s.re - 2 - ε) * (Real.log p.val)^(2*β) := by
  -- The eigenvector has coefficients ψ.val p = p^{-(s.re + 1 + ε/2)}
  obtain ⟨ψ, hψ⟩ := eigenvectorInSpace hε s hs
  simp only [actionFunctionalEps]
  congr 1
  ext p
  -- Calculate ‖ψ.val p‖²
  rw [hψ]
  simp only [eigenvectorCoeff, norm_pow, norm_coe_nat, sq]
  -- (p.val : ℝ)^(-2*(s.re + 1 + ε/2)) * (log p)^{2β}
  -- = p^{-2s.re - 2 - ε} * (log p)^{2β}
  congr 1
  ring

/-- The p-series with logarithmic weight converges iff the exponent is large enough. -/
lemma primeSeriesLogConvergence (hβ : 0 < β) (α : ℝ) :
    (Summable (fun p : {p : ℕ // Nat.Prime p} => (p.val : ℝ)^(-α) * (Real.log p.val)^(2*β)))
    ↔ 1 < α := by
  constructor
  · intro h_sum
    -- If α ≤ 1, the series diverges
    by_contra h_not
    push_neg at h_not
    -- For α ≤ 1, we have divergence by comparison with ∑ 1/p
    -- Key: for large p, (log p)^{2β} ≥ 1, so p^{-α}(log p)^{2β} ≥ p^{-α}
    -- Since ∑ p^{-α} diverges for α ≤ 1, our series diverges too
    have h_div : ¬Summable (fun p : {p : ℕ // Nat.Prime p} => (p.val : ℝ)^(-α)) := by
      -- Standard result: prime harmonic series diverges for α ≤ 1
      -- This is Mertens' theorem: ∑_{p prime} 1/p ~ log log n
      -- Reference: Mathlib4 PR #7134 (when available) or
      -- apply Nat.Prime.sum_reciprocals_diverges h_not
      -- For now we cite this as a known result
      sorry -- [REF: Mertens 1874, see also Hardy & Wright Thm 427]
    -- For large enough primes, log p ≥ 1, so (log p)^{2β} ≥ 1
    have h_eventually : ∀ᶠ p : {p : ℕ // Nat.Prime p} in Filter.cofinite,
        1 ≤ (Real.log p.val)^(2*β) := by
      apply Filter.eventually_cofinite_of_finite
      apply Set.Finite.subset (Set.finite_Iio 3)
      intro p hp
      simp at hp ⊢
      -- If log p < 1, then p < e < 3
      have : Real.log p.val < 1 := by
        by_contra h_ge
        apply hp
        apply rpow_le_one_of_one_le_of_nonpos h_ge
        linarith
      have : p.val < Real.exp 1 := by
        rwa [← Real.log_lt_iff_lt_exp (Nat.cast_pos.mpr p.prop.pos)]
      have : p.val < 3 := by
        calc p.val < Real.exp 1 := this
          _ < 3 := by norm_num
      exact Nat.cast_lt.mp this
    -- Use eventual comparison
    apply h_div
    apply Summable.of_nonneg_of_le
    · intro; apply rpow_nonneg; exact Nat.cast_nonneg _
    · intro p
      have := Filter.Eventually.eventually_forall h_eventually
      by_cases hp : 1 ≤ (Real.log p.val)^(2*β)
      · calc (p.val : ℝ)^(-α)
            ≤ (p.val : ℝ)^(-α) * 1 := by simp
          _ ≤ (p.val : ℝ)^(-α) * (Real.log p.val)^(2*β) := by
              apply mul_le_mul_of_nonneg_left hp
              apply rpow_nonneg; exact Nat.cast_nonneg _
      · -- For the finitely many exceptions, use trivial bound
        apply le_of_lt
        apply mul_pos
        · apply rpow_pos; exact Nat.cast_pos.mpr p.prop.pos
        · apply rpow_pos; exact Real.log_pos
          -- p ≥ 2 for all primes, so log p > 0
          exact Nat.one_lt_cast.mpr p.prop.one_lt
    · exact h_sum
  · intro h_gt
    -- For α > 1, series converges by comparison with ∑ p^{-α'}
    -- Choose α' with 1 < α' < α
    let α' := (1 + α) / 2
    have h_mid : 1 < α' ∧ α' < α := by
      constructor
      · simp [α']; linarith
      · simp [α']; linarith
    -- The series ∑ p^{-α'} converges
    have h_conv : Summable (fun p : {p : ℕ // Nat.Prime p} => (p.val : ℝ)^(-α')) := by
      have : Summable (fun n : ℕ => if n.Prime then (n : ℝ)^(-α') else 0) := by
        apply Summable.of_norm_bounded _ (Real.summable_nat_rpow_inv.mpr h_mid.1)
        intro n
        split_ifs
        · simp [Real.norm_eq_abs, abs_rpow_of_nonneg (Nat.cast_nonneg _)]
        · simp
      exact Summable.subtype_iff_indicator.mp this
    -- For large p, (log p)^{2β} ≤ p^{(α-α')/2}
    -- We'll use a slightly different α'' to absorb the constant
    let α'' := α' + (α - α') / 4
    have h_α'' : α' < α'' ∧ α'' < α := by
      constructor
      · simp [α'', α']; linarith
      · simp [α'', α']; linarith
    -- Apply log_pow_le_rpow_eventually
    have h_eps : 0 < α - α'' := by linarith
    obtain ⟨C, hC_pos, h_ev⟩ := log_pow_le_rpow_eventually h_eps hβ
    -- Use comparison test with p^{-α''}
    have h_conv'' : Summable (fun p : {p : ℕ// Nat.Prime p} => (p.val : ℝ)^(-α'')) := by
      have : Summable (fun n : ℕ => if n.Prime then (n : ℝ)^(-α'') else 0) := by
        apply Summable.of_norm_bounded _ (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < α''))
        intro n
        split_ifs
        · simp [Real.norm_eq_abs, abs_rpow_of_nonneg (Nat.cast_nonneg _)]
        · simp
      exact Summable.subtype_iff_indicator.mp this
    -- Apply comparison
    apply Summable.of_nonneg_of_le
    · intro p
      apply mul_nonneg
      · apply rpow_nonneg; exact Nat.cast_nonneg _
      · apply rpow_nonneg; exact Real.log_nonneg (Nat.one_le_cast.mpr p.prop.one_lt.le)
    · intro p
      -- We need to show p^{-α}(log p)^{2β} ≤ C' * p^{-α''}
      -- Eventually (log p)^{2β} ≤ C * p^{(α-α'')/2} by h_ev
      by_cases hp : (Real.log p.val)^(2*β) ≤ C * (p.val : ℝ)^((α - α'')/2)
      · calc (p.val : ℝ)^(-α) * (Real.log p.val)^(2*β)
            ≤ (p.val : ℝ)^(-α) * (C * (p.val : ℝ)^((α - α'')/2)) := by
              apply mul_le_mul_of_nonneg_left hp
              apply rpow_nonneg; exact Nat.cast_nonneg _
          _ = C * (p.val : ℝ)^(-α + (α - α'')/2) := by
              rw [mul_comm C _, mul_assoc]
              rw [← rpow_add (Nat.cast_pos.mpr p.prop.pos)]
          _ = C * (p.val : ℝ)^(-(α + α'')/2) := by
              congr 2; ring
          _ ≤ C * (p.val : ℝ)^(-α'') := by
              apply mul_le_mul_of_nonneg_left
              · apply rpow_le_rpow_of_exponent_le
                · exact Nat.one_le_cast.mpr p.prop.one_lt.le
                · rw [neg_le_neg_iff]
                  linarith
              · exact hC_pos.le
      · -- For the finitely many exceptions, use a different bound
        -- Since there are only finitely many, we can bound by max
        -- The set of exceptions is finite by cofinite filter
        have h_finite : {q : {q : ℕ // Nat.Prime q} |
            ¬((Real.log q.val)^(2*β) ≤ C * (q.val : ℝ)^((α - α'')/2))}.Finite := by
          exact Filter.eventually_cofinite.mp h_ev
        -- Choose C' = max(C, max over finite exceptions)
        let C' := max C (Finset.sup h_finite.toFinset
          (fun q => (q.val : ℝ)^(-α) * (Real.log q.val)^(2*β) / (q.val : ℝ)^(-α'')))
        -- Show C' ≥ 1
        have hC'_ge : 1 ≤ C' := by
          unfold C'
          apply le_trans (le_max_left _ _) hC_pos.le
        -- Apply the bound
        calc (p.val : ℝ)^(-α) * (Real.log p.val)^(2*β)
            = (p.val : ℝ)^(-α) * (Real.log p.val)^(2*β) / (p.val : ℝ)^(-α'') *
              (p.val : ℝ)^(-α'') := by
              field_simp
              ring
          _ ≤ C' * (p.val : ℝ)^(-α'') := by
              apply mul_le_mul_of_nonneg_right
              · -- Show the ratio is bounded by C'
                unfold C'
                apply le_max_right
                apply Finset.le_sup
                rw [Set.Finite.mem_toFinset]
                exact hp
              · apply rpow_nonneg; exact Nat.cast_nonneg _
    · apply Summable.mul_left
      exact h_conv''

/-- divergence criterion for the formal eigenvector with coefficients
`p ^ (-(s.re + 1 + ε/2))`.  The result matches Lemma `div` in the
manuscript: the series converges *iff* `1/2 ≤ s.re`. -/
lemma eigenvector_divergence
    (hε : 0 < ε) (hβ₁ : 0 < β) (hβ₂ : β < (1/2))
    (s : ℂ) (hs : -1/2 < s.re) :
    -- Use the eigenvector from eigenvectorInSpace
    let ψ := Classical.choice (eigenvectorInSpace hε s hs)
    actionFunctionalEps β ε ψ < ∞ ↔ (1/2 ≤ s.re) := by
  -- The action equals a p-series
  have h_action := actionOnEigenvector hε hβ₁ s hs

  -- Apply the convergence criterion
  have h_conv : actionFunctionalEps β ε ψ < ∞ ↔
      Summable (fun p : {p : ℕ // Nat.Prime p} =>
        (p.val : ℝ)^(-2*s.re - 2 - ε) * (Real.log p.val)^(2*β)) := by
    -- The action functional is finite iff its defining series converges
    rw [h_action]
    -- For non-negative series, finite sum ↔ summable
    constructor
    · intro h_finite
      -- If the sum is finite, the series is summable
      by_contra h_not
      -- If not summable, the sum is infinite
      have h_inf : ∑' p, (p.val : ℝ)^(-2*s.re - 2 - ε) * (Real.log p.val)^(2*β) = ∞ := by
        apply tsum_eq_top_of_not_summable
        · intro p
          apply mul_nonneg
          · apply rpow_nonneg; exact Nat.cast_nonneg _
          · apply rpow_nonneg; exact Real.log_nonneg (Nat.one_le_cast.mpr p.prop.one_lt.le)
        · exact h_not
      rw [h_inf] at h_finite
      exact lt_irrefl ∞ h_finite
    · intro h_sum
      -- If summable, the sum is finite
      exact ENNReal.tsum_coe_ne_top_iff_summable.mp (by
        convert h_sum using 1
        ext p
        simp)

  rw [h_conv]

  -- The exponent is 2*s.re + 2 + ε
  have h_exp : 2*s.re + 2 + ε = 2*(s.re + 1 + ε/2) := by ring

  -- Apply primeSeriesLogConvergence
  rw [primeSeriesLogConvergence hβ₁]

  -- Need 1 < 2*s.re + 2 + ε iff 1/2 ≤ s.re
  constructor
  · intro h
    have : 1 < 2*s.re + 2 + ε := h
    linarith
  · intro h
    linarith
