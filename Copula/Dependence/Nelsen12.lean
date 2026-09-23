/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/import Copula.Families.Nelsen12Limits
import Copula.Order.Orthant


/-! # Nelsen 12 lower-orthant parameter order

The CDF is the reciprocal of one plus a two-coordinate power norm, which
decreases as its exponent increases.
-/
open scoped unitInterval
namespace ProbabilityTheory.Copula

/-- Nelsen 12 increases in lower-orthant order with its parameter. -/
theorem lowerOrthantLE_nelsen12 {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η)
    (hθη : θ ≤ η) : (nelsen12 θ hθ).LowerOrthantLE (nelsen12 η hη) := by
  intro z
  have hz : z = ![z 0, z 1] := by funext i; fin_cases i <;> rfl
  rw [hz, nelsen12_cdf_full, nelsen12_cdf_full]
  by_cases hzero : z 0 = 0 ∨ z 1 = 0
  · simp [hzero]
  simp only [hzero, ↓reduceIte]
  have hu : 0 < (z 0 : ℝ) := lt_of_le_of_ne (z 0).property.1
    (Ne.symm (fun h => hzero (Or.inl (Subtype.ext h))))
  have hv : 0 < (z 1 : ℝ) := lt_of_le_of_ne (z 1).property.1
    (Ne.symm (fun h => hzero (Or.inr (Subtype.ext h))))
  have hx : 0 ≤ (z 0 : ℝ)⁻¹ - 1 := by
    have hh := one_div_le_one_div_of_le hu (z 0).property.2
    simpa only [one_div, div_one] using sub_nonneg.mpr hh
  have hy : 0 ≤ (z 1 : ℝ)⁻¹ - 1 := by
    have hh := one_div_le_one_div_of_le hv (z 1).property.2
    simpa only [one_div, div_one] using sub_nonneg.mpr hh
  have hnorm := Real.rpow_add_rpow_le hx hy (by linarith : 0 < θ) hθη
  simp only [one_div] at hnorm
  have hden : 0 < 1 + (((z 0 : ℝ)⁻¹ - 1) ^ η +
      ((z 1 : ℝ)⁻¹ - 1) ^ η) ^ η⁻¹ := by
    have hh : 0 ≤ (((z 0 : ℝ)⁻¹ - 1) ^ η +
      ((z 1 : ℝ)⁻¹ - 1) ^ η) ^ η⁻¹ := Real.rpow_nonneg
        (add_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _)) _
    linarith
  simpa only [one_div] using one_div_le_one_div_of_le hden (by linarith [hnorm])

end ProbabilityTheory.Copula
