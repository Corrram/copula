/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.StudentT.GammaSmallBall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # The Student-t distribution

For `n > 0` degrees of freedom, the Student-t density is
`t_n(x) = c_n (1 + x²/n)^{-(n+1)/2}` with the normalizing constant
`c_n = (∫ (1 + y²/n)^{-(n+1)/2} dy)⁻¹`; we write `studentTKernel`, `studentTPDF` and
`studentTCDF` for the unnormalized kernel, the density and the distribution function.

The substitution `x = √n tan θ` maps `(−π/2, π/2)` onto `ℝ` and turns the kernel into
`√n cos^{n−1} θ dθ`, so

`T_n(x) = ∫_{−π/2}^{arctan(x/√n)} cos^{n−1} θ dθ / ∫_{−π/2}^{π/2} cos^{n−1} θ dθ`

(`studentTCDF_eq_angular`). In particular, for `0 ≤ a < π/2`,
`T_n(−√n tan a) = ∫_a^{π/2} cos^{n−1} / (2 ∫_0^{π/2} cos^{n−1})` (`studentTCDF_neg_sqrt_mul_tan`),
the identity behind the closed form of the tail-dependence coefficient of the t copula.

## Main results
* `intervalIntegrable_cos_rpow`: `cos^p` is integrable on `[−π/2, π/2]` for `p > −1`.
* `integral_Iio_studentTKernel`, `integral_studentTKernel`: the tan substitution.
* `integral_studentTPDF`: the density integrates to `1`.
* `studentTCDF_eq_angular`, `studentTCDF_neg_sqrt_mul_tan`.

## References
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, Vol. 2,
  2nd ed., Wiley 1995, Ch. 28.
-/

open MeasureTheory Set Real Filter

namespace ProbabilityTheory

/-- The unnormalized Student-t kernel `(1 + x²/n)^{-(n+1)/2}`. -/
noncomputable def studentTKernel (n x : ℝ) : ℝ := (1 + x ^ 2 / n) ^ (-(n + 1) / 2)

/-- The Student-t density with `n` degrees of freedom. -/
noncomputable def studentTPDF (n x : ℝ) : ℝ := studentTKernel n x / ∫ y, studentTKernel n y

/-- The Student-t distribution function with `n` degrees of freedom. -/
noncomputable def studentTCDF (n x : ℝ) : ℝ := ∫ y in Iic x, studentTPDF n y

theorem studentTKernel_pos {n : ℝ} (hn : 0 < n) (x : ℝ) : 0 < studentTKernel n x :=
  rpow_pos_of_pos (by positivity) _

/-! ### Integrability of `cos^p` -/

private theorem intervalIntegrable_cos_rpow_zero_pi_div_two {p : ℝ} (hp : -1 < p) :
    IntervalIntegrable (fun θ => cos θ ^ p) volume 0 (π / 2) := by
  have hπ := pi_pos
  rcases le_or_gt 0 p with hp0 | hp0
  · exact (continuous_cos.rpow_const fun _ => Or.inr hp0).intervalIntegrable _ _
  -- for `p < 0` dominate by Jordan's inequality `cos θ ≥ (2/π)(π/2 − θ)`
  have hg : IntervalIntegrable (fun θ => (2 / π) ^ p * (π / 2 - θ) ^ p) volume 0 (π / 2) := by
    have h := (intervalIntegral.intervalIntegrable_rpow' hp (a := π / 2) (b := 0)).comp_sub_left
      (π / 2)
    rw [sub_self, sub_zero] at h
    exact h.const_mul _
  refine hg.mono_fun ((continuous_cos.measurable.pow_const p).aestronglyMeasurable) ?_
  rw [uIoc_of_le (by linarith)]
  refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun θ hθ => ?_)
  change ‖cos θ ^ p‖ ≤ ‖(2 / π) ^ p * (π / 2 - θ) ^ p‖
  rcases eq_or_lt_of_le hθ.2 with h | h
  · rw [h, cos_pi_div_two, zero_rpow hp0.ne, norm_zero]
    exact norm_nonneg _
  have hpos : 0 < 2 / π * (π / 2 - θ) := by
    have : 0 < π / 2 - θ := by linarith
    positivity
  have hle : 2 / π * (π / 2 - θ) ≤ cos θ := by
    rw [← sin_pi_div_two_sub]
    exact mul_le_sin (by linarith) (by linarith [hθ.1])
  rw [Real.norm_of_nonneg (rpow_nonneg (hpos.le.trans hle) _),
    Real.norm_of_nonneg (mul_nonneg (rpow_nonneg (by positivity) _)
      (rpow_nonneg (by linarith) _)),
    ← mul_rpow (by positivity) (by linarith)]
  exact rpow_le_rpow_of_nonpos hpos hle hp0.le

private theorem intervalIntegrable_cos_rpow_neg_pi_div_two_zero {p : ℝ} (hp : -1 < p) :
    IntervalIntegrable (fun θ => cos θ ^ p) volume (-(π / 2)) 0 := by
  have h' := (IntervalIntegrable.iff_comp_neg (by finiteness)).1
    (intervalIntegrable_cos_rpow_zero_pi_div_two hp)
  simp only [cos_neg, neg_zero] at h'
  exact h'.symm

/-- `cos^p` is integrable on `[−π/2, π/2]` for `p > −1`. -/
theorem intervalIntegrable_cos_rpow {p : ℝ} (hp : -1 < p) :
    IntervalIntegrable (fun θ => cos θ ^ p) volume (-(π / 2)) (π / 2) :=
  (intervalIntegrable_cos_rpow_neg_pi_div_two_zero hp).trans
    (intervalIntegrable_cos_rpow_zero_pi_div_two hp)

/-- `∫_{−π/2}^{π/2} cos^p > 0` for `p > −1`. -/
theorem integral_cos_rpow_symm_pos {p : ℝ} (hp : -1 < p) :
    0 < ∫ θ in -(π / 2)..π / 2, cos θ ^ p :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_cos_rpow hp)
    (fun _ hθ => rpow_pos_of_pos (cos_pos_of_mem_Ioo hθ) _) (by linarith [pi_pos])

/-! ### The tan substitution -/

private theorem image_sqrt_mul_tan {n : ℝ} (hn : 0 < n) {S : Set ℝ}
    (hS : S ⊆ Ioo (-(π / 2)) (π / 2)) (y : ℝ) :
    y ∈ (fun θ => √n * tan θ) '' S ↔ arctan (y / √n) ∈ S := by
  have hs : 0 < √n := Real.sqrt_pos.2 hn
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    rw [mul_div_cancel_left₀ _ hs.ne', arctan_tan (hS hθ).1 (hS hθ).2]
    exact hθ
  · intro h
    refine ⟨_, h, ?_⟩
    change √n * tan (arctan (y / √n)) = y
    rw [tan_arctan, mul_div_cancel₀ _ hs.ne']

private theorem studentTKernel_sqrt_mul_tan {n θ : ℝ} (hn : 0 < n)
    (hθ : θ ∈ Ioo (-(π / 2)) (π / 2)) :
    |√n * (1 / cos θ ^ 2)| * studentTKernel n (√n * tan θ) = √n * cos θ ^ (n - 1) := by
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo hθ
  have h1 : 0 < 1 + tan θ ^ 2 := by positivity
  have hk : studentTKernel n (√n * tan θ) = cos θ ^ (n + 1) := by
    rw [studentTKernel, mul_pow, Real.sq_sqrt hn.le, mul_div_cancel_left₀ _ hn.ne', neg_div,
      rpow_neg h1.le, ← inv_rpow h1.le, inv_one_add_tan_sq hc.ne',
      ProbabilityTheory.sq_rpow_eq_rpow_two_mul hc.le]
    congr 1
    ring
  have hs : 0 ≤ √n * (1 / cos θ ^ 2) := by positivity
  rw [abs_of_nonneg hs, hk, show n + 1 = (n - 1) + 2 by ring, rpow_add hc, rpow_two]
  field_simp

private theorem integral_image_sqrt_mul_tan {n : ℝ} (hn : 0 < n) {a b : ℝ}
    (ha : -(π / 2) ≤ a) (hb : b ≤ π / 2) :
    ∫ y in (fun θ => √n * tan θ) '' Ioo a b, studentTKernel n y =
      √n * ∫ θ in Ioo a b, cos θ ^ (n - 1) := by
  have hsub : Ioo a b ⊆ Ioo (-(π / 2)) (π / 2) := Ioo_subset_Ioo ha hb
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (f' := fun θ => √n * (1 / cos θ ^ 2))
    (fun θ hθ => ((hasDerivAt_tan (cos_pos_of_mem_Ioo (hsub hθ)).ne').const_mul
      √n).hasDerivWithinAt)
    (fun θ₁ h₁ θ₂ h₂ h => strictMonoOn_tan.injOn (hsub h₁) (hsub h₂)
      (mul_left_cancel₀ (Real.sqrt_pos.2 hn).ne' h)),
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  rw [smul_eq_mul, studentTKernel_sqrt_mul_tan hn (hsub hθ)]

/-- **The tan substitution**: `∫_{−∞}^{x} (1 + y²/n)^{-(n+1)/2} dy =
√n ∫_{−π/2}^{arctan(x/√n)} cos^{n−1} θ dθ`. -/
theorem integral_Iio_studentTKernel {n : ℝ} (hn : 0 < n) (x : ℝ) :
    ∫ y in Iio x, studentTKernel n y =
      √n * ∫ θ in -(π / 2)..arctan (x / √n), cos θ ^ (n - 1) := by
  have hs : 0 < √n := Real.sqrt_pos.2 hn
  have himg : (fun θ => √n * tan θ) '' Ioo (-(π / 2)) (arctan (x / √n)) = Iio x := by
    ext y
    rw [image_sqrt_mul_tan hn (Ioo_subset_Ioo le_rfl (arctan_lt_pi_div_two _).le)]
    simp only [mem_Ioo, mem_Iio, neg_pi_div_two_lt_arctan, true_and,
      arctan_strictMono.lt_iff_lt]
    exact div_lt_div_iff_of_pos_right hs
  rw [← himg, integral_image_sqrt_mul_tan hn le_rfl (arctan_lt_pi_div_two _).le,
    intervalIntegral.integral_of_le (neg_pi_div_two_lt_arctan _).le, integral_Ioc_eq_integral_Ioo]

/-- The total mass of the kernel: `∫ (1 + y²/n)^{-(n+1)/2} dy = √n ∫_{−π/2}^{π/2} cos^{n−1}`. -/
theorem integral_studentTKernel {n : ℝ} (hn : 0 < n) :
    ∫ y, studentTKernel n y = √n * ∫ θ in -(π / 2)..π / 2, cos θ ^ (n - 1) := by
  have himg : (fun θ => √n * tan θ) '' Ioo (-(π / 2)) (π / 2) = univ := by
    ext y
    rw [image_sqrt_mul_tan hn subset_rfl]
    simp [neg_pi_div_two_lt_arctan, arctan_lt_pi_div_two]
  rw [← setIntegral_univ, ← himg, integral_image_sqrt_mul_tan hn le_rfl le_rfl,
    intervalIntegral.integral_of_le (by linarith [pi_pos]), integral_Ioc_eq_integral_Ioo]

theorem integral_studentTKernel_pos {n : ℝ} (hn : 0 < n) : 0 < ∫ y, studentTKernel n y := by
  rw [integral_studentTKernel hn]
  exact mul_pos (Real.sqrt_pos.2 hn) (integral_cos_rpow_symm_pos (by linarith))

theorem studentTPDF_pos {n : ℝ} (hn : 0 < n) (x : ℝ) : 0 < studentTPDF n x :=
  div_pos (studentTKernel_pos hn x) (integral_studentTKernel_pos hn)

/-- The Student-t density integrates to `1`. -/
theorem integral_studentTPDF {n : ℝ} (hn : 0 < n) : ∫ x, studentTPDF n x = 1 := by
  simp_rw [studentTPDF]
  rw [integral_div]
  exact div_self (integral_studentTKernel_pos hn).ne'

/-- **Angular form of the Student-t distribution function**. -/
theorem studentTCDF_eq_angular {n : ℝ} (hn : 0 < n) (x : ℝ) :
    studentTCDF n x = (∫ θ in -(π / 2)..arctan (x / √n), cos θ ^ (n - 1)) /
      ∫ θ in -(π / 2)..π / 2, cos θ ^ (n - 1) := by
  rw [studentTCDF]
  simp_rw [studentTPDF]
  rw [integral_div, integral_Iic_eq_integral_Iio, integral_Iio_studentTKernel hn,
    integral_studentTKernel hn, mul_div_mul_left _ _ (Real.sqrt_pos.2 hn).ne']

/-- `∫_{−π/2}^{π/2} cos^p = 2 ∫_0^{π/2} cos^p` for `p > −1`. -/
theorem integral_cos_rpow_symm {p : ℝ} (hp : -1 < p) :
    ∫ θ in -(π / 2)..π / 2, cos θ ^ p = 2 * ∫ θ in (0 : ℝ)..π / 2, cos θ ^ p := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (intervalIntegrable_cos_rpow_neg_pi_div_two_zero hp)
    (intervalIntegrable_cos_rpow_zero_pi_div_two hp)]
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := π / 2) (fun θ => cos θ ^ p)
  simp only [cos_neg, neg_zero] at h
  rw [← h]
  ring

/-- `∫_{−π/2}^{−a} cos^p = ∫_a^{π/2} cos^p`. -/
theorem integral_cos_rpow_neg (p a : ℝ) :
    ∫ θ in -(π / 2)..-a, cos θ ^ p = ∫ θ in a..π / 2, cos θ ^ p := by
  have h := intervalIntegral.integral_comp_neg (a := a) (b := π / 2) (fun θ => cos θ ^ p)
  simp only [cos_neg] at h
  exact h.symm

/-- `T_n(−√n tan a) = ∫_a^{π/2} cos^{n−1} / (2 ∫_0^{π/2} cos^{n−1})` for `a ∈ (−π/2, π/2)`. -/
theorem studentTCDF_neg_sqrt_mul_tan {n a : ℝ} (hn : 0 < n) (ha : a ∈ Ioo (-(π / 2)) (π / 2)) :
    studentTCDF n (-(√n * tan a)) = (∫ θ in a..π / 2, cos θ ^ (n - 1)) /
      (2 * ∫ θ in (0 : ℝ)..π / 2, cos θ ^ (n - 1)) := by
  rw [studentTCDF_eq_angular hn, neg_div, mul_div_cancel_left₀ _ (Real.sqrt_pos.2 hn).ne',
    arctan_neg, arctan_tan ha.1 ha.2, integral_cos_rpow_neg, integral_cos_rpow_symm (by linarith)]

end ProbabilityTheory
