/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Elliptical.StudentTTail.TailDependence
import Copula.Families.StudentT.Distribution

/-! # The tail-dependence coefficient of the Student-t copula

For the bivariate Student-t copula `C_{ν,r}` with `ν > 0` degrees of freedom and correlation
`r ∈ (−1, 1]`,

`λ_L = λ_U = 2 t_{ν+1}(−√((ν+1)(1−r)/(1+r)))`

where `t_{ν+1}` is the Student-t distribution function with `ν + 1` degrees of freedom
(Embrechts–McNeil–Straumann 2002, Demarta–McNeil 2005). In particular the t copula is tail
dependent for every `r > −1`, unlike the Gaussian copula
(`hasLowerTailDependence_bivariateGaussian`).
For `r = −1` the copula is countermonotonic and `λ = 0`.

## Proof
`Copula.Elliptical.StudentTTail.TailDependence` gives the angular form
`λ = ∫_a^{π/2} cos^ν / ∫_0^{π/2} cos^ν` with `a = arccos(r)/2`. With `n = ν + 1`, the tan
substitution of `Copula.Families.StudentT.Distribution` gives
`t_n(−√n tan a) = ∫_a^{π/2} cos^{n−1} / (2 ∫_0^{π/2} cos^{n−1})`, and the half-angle formula
`tan(arccos(r)/2) = √((1−r)/(1+r))` finishes the computation.

## Main results
* `studentTTailCoeff_eq_studentTCDF`: the closed form of the coefficient.
* `hasLowerTailDependence_studentT_closedForm`, `hasUpperTailDependence_studentT_closedForm`.
* `studentT_not_tailIndependent`: `λ_L ≠ 0` for `r > −1`.

## References
* P. Embrechts, A. McNeil, D. Straumann, *Correlation and dependence in risk management:
  properties and pitfalls*, CUP 2002.
* S. Demarta, A. McNeil, *The t copula and related copulas*, Int. Stat. Rev. 73 (2005).
* H. Hult, F. Lindskog, *Multivariate extremes, aggregation and dependence in elliptical
  distributions*, Adv. Appl. Probab. 34 (2002).
-/

open MeasureTheory Set Real

namespace ProbabilityTheory.Copula

/-- The half-angle formula `tan(arccos(r)/2) = √((1−r)/(1+r))` for `r ∈ (−1, 1]`. -/
theorem tan_arccos_div_two {r : ℝ} (hr : r ∈ Ioc (-1 : ℝ) 1) :
    tan (arccos r / 2) = √((1 - r) / (1 + r)) := by
  have hπ := pi_pos
  have ha0 : 0 ≤ arccos r / 2 := div_nonneg (arccos_nonneg r) zero_le_two
  have haπ : arccos r / 2 < π / 2 := by
    have : arccos r < π := arccos_lt_pi.2 hr.1
    linarith
  have hc : 0 < cos (arccos r / 2) := cos_pos_of_mem_Ioo ⟨by linarith, haπ⟩
  have hs : 0 ≤ sin (arccos r / 2) := sin_nonneg_of_nonneg_of_le_pi ha0 (by linarith)
  have hc2 : cos (arccos r / 2) ^ 2 = (1 + r) / 2 := by
    rw [cos_sq, mul_div_cancel₀ _ two_ne_zero, cos_arccos (by linarith [hr.1]) hr.2]
    ring
  have hs2 : sin (arccos r / 2) ^ 2 = (1 - r) / 2 := by
    rw [sin_sq, hc2]
    ring
  have h1r : 0 < 1 + r := by linarith [hr.1]
  rw [tan_eq_sin_div_cos, ← Real.sqrt_sq (div_nonneg hs hc.le), div_pow, hs2, hc2]
  congr 1
  field_simp

/-- **Closed form of the Student-t tail-dependence coefficient**:
`λ(ν, r) = 2 t_{ν+1}(−√((ν+1)(1−r)/(1+r)))` for `r ∈ (−1, 1]`. -/
theorem studentTTailCoeff_eq_studentTCDF {ν r : ℝ} (hν : 0 < ν) (hr : r ∈ Ioc (-1 : ℝ) 1) :
    studentTTailCoeff ν r = 2 * studentTCDF (ν + 1) (-√((ν + 1) * (1 - r) / (1 + r))) := by
  have hπ := pi_pos
  have ha0 : 0 ≤ arccos r / 2 := div_nonneg (arccos_nonneg r) zero_le_two
  have haπ : arccos r / 2 < π / 2 := by
    have : arccos r < π := arccos_lt_pi.2 hr.1
    linarith
  have hsq : √((ν + 1) * (1 - r) / (1 + r)) = √(ν + 1) * tan (arccos r / 2) := by
    rw [tan_arccos_div_two hr, mul_div_assoc, Real.sqrt_mul (by linarith)]
  have hn : (0 : ℝ) < ν + 1 := by linarith
  rw [hsq, studentTCDF_neg_sqrt_mul_tan hn ⟨by linarith, haπ⟩, add_sub_cancel_right,
    studentTTailCoeff]
  field_simp

/-- **Lower tail dependence of the Student-t copula** (Embrechts–McNeil–Straumann 2002):
`λ_L = 2 t_{ν+1}(−√((ν+1)(1−r)/(1+r)))` for `r ∈ (−1, 1]`. -/
theorem hasLowerTailDependence_studentT_closedForm {r : ℝ} (hr : r ∈ Ioc (-1 : ℝ) 1) {ν : ℝ}
    (hν : 0 < ν) :
    (studentT (corrMatrix r) (posSemidef_corrMatrix (Ioc_subset_Icc_self hr))
      (corrMatrix_diag r) ν hν).HasLowerTailDependence
        (2 * studentTCDF (ν + 1) (-√((ν + 1) * (1 - r) / (1 + r)))) := by
  rw [← studentTTailCoeff_eq_studentTCDF hν hr]
  exact hasLowerTailDependence_studentT (Ioc_subset_Icc_self hr) hν

/-- **Upper tail dependence of the Student-t copula**:
`λ_U = 2 t_{ν+1}(−√((ν+1)(1−r)/(1+r)))` for `r ∈ (−1, 1]`. -/
theorem hasUpperTailDependence_studentT_closedForm {r : ℝ} (hr : r ∈ Ioc (-1 : ℝ) 1) {ν : ℝ}
    (hν : 0 < ν) :
    (studentT (corrMatrix r) (posSemidef_corrMatrix (Ioc_subset_Icc_self hr))
      (corrMatrix_diag r) ν hν).HasUpperTailDependence
        (2 * studentTCDF (ν + 1) (-√((ν + 1) * (1 - r) / (1 + r)))) := by
  rw [← studentTTailCoeff_eq_studentTCDF hν hr]
  exact hasUpperTailDependence_studentT (Ioc_subset_Icc_self hr) hν

/-- The Student-t copula is not lower tail independent for `r > −1` (contrast with the Gaussian
copula, `hasLowerTailDependence_bivariateGaussian`). -/
theorem studentT_not_hasLowerTailDependence_zero {r : ℝ} (hr : r ∈ Ioc (-1 : ℝ) 1) {ν : ℝ}
    (hν : 0 < ν) :
    ¬ (studentT (corrMatrix r) (posSemidef_corrMatrix (Ioc_subset_Icc_self hr))
      (corrMatrix_diag r) ν hν).HasLowerTailDependence 0 := fun h =>
  (studentTTailCoeff_pos hν hr.1).ne'
    ((hasLowerTailDependence_studentT (Ioc_subset_Icc_self hr) hν).unique h)

end ProbabilityTheory.Copula
