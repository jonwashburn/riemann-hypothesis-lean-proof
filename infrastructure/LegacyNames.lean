import infrastructure.UniformBound
import infrastructure.EigenvectorDivergence

/-- Backwards‐compatibility wrapper exposing the original lemma names used
in earlier drafts of the proof.  They are simple wrappers around the new,
parameterised statements with a default choice of `ε := 1`. -/

open scoped BigOperators

variable {β : ℝ} (hβ₁ : 0 < β) (hβ₂ : β < (1/2))

/-- Uniform bound with fixed ε = 1 (old name `action_finite_on_W`). -/
lemma action_finite_on_W :
    ∃ C : ℝ, 0 < C ∧ ∀ ψ : WeightedHilbertSpaceEps 1, ‖ψ‖ ≤ 1 →
      actionFunctionalEps β 1 ψ ≤ C := by
  have hε : (0 : ℝ) < 1 := by norm_num
  simpa using actionFunctional_boundedEps (ε := 1) hε hβ₁ hβ₂

/-- Divergence wrapper (old name `eigenvector_divergence`). -/
lemma eigenvector_divergence_old (s : ℂ) :
    (let coeff : {p : ℕ // Nat.Prime p} → ℂ :=
      fun p => (p.val : ℂ) ^ (-(s.re + 1 + 1/2)))
    (actionFunctionalEps β 1 ⟨coeff, by
      -- Summability placeholder.
      sorry⟩) < ∞ ↔ (1/2 ≤ s.re) := by
  have hε : (0 : ℝ) < 1 := by norm_num
  have h := eigenvector_divergence (ε := 1) hε hβ₁ hβ₂ s
  simpa using h

attribute [deprecated] action_finite_on_W eigenvector_divergence_old
