/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/import Copula.Families.Gumbel
import Copula.Order.Orthant


/-! # Gumbel–Hougaard lower-orthant parameter order

The two-coordinate logarithmic power norm decreases with its exponent, so
the exponential CDF increases with the parameter.
-/
open scoped unitInterval
namespace ProbabilityTheory.Copula

/-- Gumbel–Hougaard increases in lower-orthant order with its parameter. -/
theorem lowerOrthantLE_gumbel {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η)
    (hθη : θ ≤ η) : (gumbel θ hθ).LowerOrthantLE (gumbel η hη) := by
  intro z
  have hz : z = ![z 0, z 1] := by funext i; fin_cases i <;> rfl
  rw [hz, gumbel_cdf_full, gumbel_cdf_full]
  by_cases hzero : z 0 = 0 ∨ z 1 = 0
  · simp [hzero]
  simp only [hzero, ↓reduceIte]
  have hx : 0 ≤ -Real.log (z 0 : ℝ) :=
    neg_nonneg.mpr (Real.log_nonpos (z 0).property.1 (z 0).property.2)
  have hy : 0 ≤ -Real.log (z 1 : ℝ) :=
    neg_nonneg.mpr (Real.log_nonpos (z 1).property.1 (z 1).property.2)
  have hnorm := Real.rpow_add_rpow_le hx hy (by linarith : 0 < θ) hθη
  simp only [one_div] at hnorm
  exact Real.exp_le_exp.mpr (by linarith [hnorm])

end ProbabilityTheory.Copula
