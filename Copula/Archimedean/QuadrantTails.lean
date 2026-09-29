/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.QuadrantCriteria
import Copula.Dependence.GumbelTotalPositivity
import Copula.Dependence.Nelsen2
import Copula.Dependence.Nelsen8
import Copula.Dependence.GenestGhoudi
import Copula.Dependence.NelsenEndpoints
import Copula.Dependence.Singular
import Copula.Dependence.Examples
import Copula.TailDependence.ExtremeValue
import Copula.TailDependence.Nelsen2
import Copula.TailDependence.Nelsen12
import Copula.TailDependence.Nelsen14
import Copula.TailDependence.GenestGhoudi
import Copula.TailDependence.NelsenTable
import Copula.TailDependence.NelsenTableLower
import Copula.Archimedean.TailFamilies

/-! # Quadrant dependence of families with tail dependence

Nonzero tail coefficients exclude NQD (`isNQD_hasLowerTailDependence_zero`). This gives, for
Nelsen's Table 4.1 and Gumbel's family:

* Gumbel (#4): PQD for all `θ ≥ 1` (from the TP2 property); NQD iff `θ = 1`;
* #2 and #15: NQD iff `θ = 1` (the lower Fréchet bound `W`);
* #12, #14, #19, #20: not NQD (they are PQD by earlier results);
* #16 (`θ > 0`): not NQD; #18: not NQD; #21: NQD iff `θ = 1`.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem two_sub_two_rpow_inv_ne {θ : ℝ} (hθ : 1 < θ) : 2 - (2 : ℝ) ^ θ⁻¹ ≠ 0 := by
  have hθ0 : 0 < θ := by linarith
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    (inv_lt_one_of_one_lt₀ hθ)
  rw [Real.rpow_one] at h
  linarith

/-- Gumbel's copula is PQD for all `θ ≥ 1`. -/
theorem isPQD_gumbel (θ : ℝ) (hθ : 1 ≤ θ) : (gumbel θ hθ).IsPQD :=
  (isTP2CDF_gumbel θ hθ).isPQD

/-- Gumbel's copula is not NQD for `θ > 1`. -/
theorem not_isNQD_gumbel (θ : ℝ) (hθ : 1 < θ) : ¬ (gumbel θ hθ.le).IsNQD :=
  not_isNQD_of_hasUpperTailDependence (hasUpperTailDependence_gumbel θ hθ.le)
    (two_sub_two_rpow_inv_ne hθ)

/-- Gumbel's copula is NQD iff `θ = 1` (independence). -/
theorem isNQD_gumbel_iff (θ : ℝ) (hθ : 1 ≤ θ) : (gumbel θ hθ).IsNQD ↔ θ = 1 := by
  rcases hθ.eq_or_lt with rfl | h
  · simp only [gumbel_one, isNQD_independence]
  · exact iff_of_false (not_isNQD_gumbel θ h) h.ne'

/-- Nelsen's family 2 is not NQD for `θ > 1`. -/
theorem not_isNQD_nelsen2 (θ : ℝ) (hθ : 1 < θ) : ¬ (nelsen2 θ hθ.le).IsNQD :=
  not_isNQD_of_hasUpperTailDependence (hasUpperTailDependence_nelsen2 θ hθ.le)
    (two_sub_two_rpow_inv_ne hθ)

/-- Nelsen's family 2 is NQD iff `θ = 1` (the lower Fréchet bound). -/
theorem isNQD_nelsen2_iff (θ : ℝ) (hθ : 1 ≤ θ) : (nelsen2 θ hθ).IsNQD ↔ θ = 1 := by
  rcases hθ.eq_or_lt with rfl | h
  · simp only [nelsen2_one, isNQD_countermonotonic]
  · exact iff_of_false (not_isNQD_nelsen2 θ h) h.ne'

/-- Nelsen's family 15 (Genest–Ghoudi) is not NQD for `θ > 1`. -/
theorem not_isNQD_genestGhoudi (θ : ℝ) (hθ : 1 < θ) : ¬ (genestGhoudi θ hθ.le).IsNQD :=
  not_isNQD_of_hasUpperTailDependence (hasUpperTailDependence_genestGhoudi θ hθ.le)
    (two_sub_two_rpow_inv_ne hθ)

/-- Nelsen's family 15 is NQD iff `θ = 1` (the lower Fréchet bound). -/
theorem isNQD_genestGhoudi_iff (θ : ℝ) (hθ : 1 ≤ θ) : (genestGhoudi θ hθ).IsNQD ↔ θ = 1 := by
  rcases hθ.eq_or_lt with rfl | h
  · simp only [genestGhoudi_one, isNQD_countermonotonic]
  · exact iff_of_false (not_isNQD_genestGhoudi θ h) h.ne'

/-- Nelsen's family 12 is never NQD (`λ_L = 2^{-1/θ} > 0`). -/
theorem not_isNQD_nelsen12 (θ : ℝ) (hθ : 1 ≤ θ) : ¬ (nelsen12 θ hθ).IsNQD :=
  not_isNQD_of_hasLowerTailDependence (hasLowerTailDependence_nelsen12 θ hθ)
    (inv_ne_zero (Real.rpow_pos_of_pos (by norm_num) _).ne')

/-- Nelsen's family 14 is never NQD (`λ_L = 1/2`). -/
theorem not_isNQD_nelsen14 (θ : ℝ) (hθ : 1 ≤ θ) : ¬ (nelsen14 θ hθ).IsNQD :=
  not_isNQD_of_hasLowerTailDependence (hasLowerTailDependence_nelsen14 θ hθ) (by norm_num)

/-- Nelsen's family 16 is not NQD for `θ > 0` (`λ_L = 1/2`). -/
theorem not_isNQD_nelsen16 (θ : ℝ) (hθ : 0 < θ) : ¬ (nelsen16 θ hθ.le).IsNQD :=
  not_isNQD_of_hasLowerTailDependence (hasLowerTailDependence_nelsen16 θ hθ) (by norm_num)

/-- Nelsen's family 18 is never NQD (`λ_U = 1`). -/
theorem not_isNQD_nelsen18 (θ : ℝ) (hθ : 2 ≤ θ) : ¬ (nelsen18 θ hθ).IsNQD :=
  not_isNQD_of_hasUpperTailDependence (hasUpperTailDependence_nelsen18 θ hθ) one_ne_zero

/-- Nelsen's family 19 is never NQD (`λ_L = 1`). -/
theorem not_isNQD_nelsen19 (θ : ℝ) (hθ : 0 < θ) : ¬ (nelsen19 θ hθ).IsNQD :=
  not_isNQD_of_hasLowerTailDependence (hasLowerTailDependence_nelsen19 θ hθ) one_ne_zero

/-- Nelsen's family 20 is never NQD (`λ_L = 1`). -/
theorem not_isNQD_nelsen20 (θ : ℝ) (hθ : 0 < θ) : ¬ (nelsen20 θ hθ).IsNQD :=
  not_isNQD_of_hasLowerTailDependence (hasLowerTailDependence_nelsen20 θ hθ) one_ne_zero

/-- Nelsen's family 21 is not NQD for `θ > 1` (`λ_U = 2 - 2^{1/θ}`). -/
theorem not_isNQD_nelsen21 (θ : ℝ) (hθ : 1 < θ) : ¬ (nelsen21 θ hθ.le).IsNQD :=
  not_isNQD_of_hasUpperTailDependence (hasUpperTailDependence_nelsen21 θ hθ.le)
    (two_sub_two_rpow_inv_ne hθ)

/-- Nelsen's family 21 is NQD iff `θ = 1` (the lower Fréchet bound). -/
theorem isNQD_nelsen21_iff (θ : ℝ) (hθ : 1 ≤ θ) : (nelsen21 θ hθ).IsNQD ↔ θ = 1 := by
  rcases hθ.eq_or_lt with rfl | h
  · simp only [nelsen21_one, isNQD_countermonotonic]
  · exact iff_of_false (not_isNQD_nelsen21 θ h) h.ne'

end ProbabilityTheory.Copula
