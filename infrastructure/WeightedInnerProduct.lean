-- Infrastructure component: Weighted inner product

import Infrastructure.WeightedHilbertSpace

/-!
# Weighted Inner Product

This file provides additional inner product functionality for the weighted Hilbert space.
-/

open scoped ENNReal NNReal ComplexConjugate
open Complex WeightedHilbertSpace

namespace WeightedInnerProduct

/-- The standard ℓ² inner product on WeightedHilbertSpace -/
noncomputable def standardInner (f g : WeightedHilbertSpace) : ℂ :=
  ⟪f, g⟫_ℂ

/-- The weighted inner product incorporating p^{-2} weights -/
noncomputable def weightedInner (f g : WeightedHilbertSpace) : ℂ :=
  ∑' p : {p : ℕ // Nat.Prime p}, (primeWeight p : ℂ) * f p * conj (g p)

/-- The weighted norm -/
noncomputable def weightedNorm (f : WeightedHilbertSpace) : ℝ :=
  Real.sqrt (weightedInner f f).re

/-- Basic properties of the weighted inner product -/

lemma weightedInner_conj_symm (f g : WeightedHilbertSpace) :
    weightedInner g f = conj (weightedInner f g) := by
  sorry

lemma weightedInner_add_left (f g h : WeightedHilbertSpace) :
    weightedInner (f + g) h = weightedInner f h + weightedInner g h := by
  sorry

lemma weightedInner_smul_left (c : ℂ) (f g : WeightedHilbertSpace) :
    weightedInner (c • f) g = c * weightedInner f g := by
  sorry

/-- The weighted inner product of basis vectors -/
lemma deltaBasis_weightedInner (p q : {p : ℕ // Nat.Prime p}) :
    weightedInner (deltaBasis p) (deltaBasis q) = if p = q then primeWeight p else 0 := by
  sorry

/-- Connection between standard and weighted inner products -/
lemma standard_vs_weighted (f g : WeightedHilbertSpace) :
    standardInner f g = ∑' p : {p : ℕ // Nat.Prime p}, f p * conj (g p) := by
  sorry

end WeightedInnerProduct
