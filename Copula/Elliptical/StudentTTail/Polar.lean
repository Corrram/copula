/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Gaussian.Bivariate
import Mathlib.MeasureTheory.Integral.Gamma

/-! # Homogeneous Gaussian moments in polar coordinates

For a function `h` on `ℝ²` that is positively homogeneous of degree `ν` along rays,
`h(ρ cos θ, ρ sin θ) = ρ^ν g(θ)`, the integral against the standard bivariate Gaussian law splits
into a radial moment and an angular integral:

`E[h(Z₁, Z₂)] = R_ν ∫_{-π}^{π} g(θ) dθ`,  `R_ν = ∫_0^∞ ρ^{ν+1} φ(ρ) φ(0) dρ > 0`.

We apply this to the two moments that govern the tail dependence of the Student-t copula
(Hult–Lindskog 2002): for `(X, Y) ~ bivariateNormal r` and `a = arccos(r)/2`,

* `E[max(min(X, Y), 0)^ν] = 2 R_ν ∫_a^{π/2} cos^ν θ dθ`,
* `E[max(X, 0)^ν] = 2 R_ν ∫_0^{π/2} cos^ν θ dθ`.

The first identity uses the symmetric representation `(X, Y) = (c Z₁ − s Z₂, c Z₁ + s Z₂)` with
`c = cos a`, `s = sin a` (`bivariateNormal_eq_map_symmetric`), for which
`min(X, Y) = ρ cos(|θ| + a)` in polar coordinates.

## References
* H. Hult, F. Lindskog, *Multivariate extremes, aggregation and dependence in elliptical
  distributions*, Adv. Appl. Probab. 34 (2002).
-/

open MeasureTheory Set Real
open scoped ENNReal NNReal

namespace ProbabilityTheory.Copula

/-- The radial moment `R_ν = ∫_0^∞ ρ^{ν+1} φ(ρ) φ(0) dρ` of the standard bivariate Gaussian law. -/
noncomputable def gaussianRadialMoment (ν : ℝ) : ℝ :=
  ∫ ρ in Ioi (0 : ℝ), ρ ^ (ν + 1) * (gaussianPDFReal 0 1 ρ * gaussianPDFReal 0 1 0)

/-- The radial profile of the standard bivariate Gaussian density:
`φ(ρ) φ(0) = (2π)⁻¹ exp(−ρ²/2)`. -/
theorem gaussianPDFReal_mul_gaussianPDFReal_zero (ρ : ℝ) :
    gaussianPDFReal 0 1 ρ * gaussianPDFReal 0 1 0 = (2 * π)⁻¹ * exp (-(1 / 2) * ρ ^ (2 : ℝ)) := by
  have h2 : (√(2 * π))⁻¹ * (√(2 * π))⁻¹ = (2 * π)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  have e : exp (-(1 / 2) * ρ ^ (2 : ℝ)) = exp (-ρ ^ 2 / 2) := by
    rw [rpow_two]
    congr 1
    ring
  simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]
  rw [e, ← h2]
  norm_num
  ring

/-- The radial moment is positive for `ν > −2`. -/
theorem gaussianRadialMoment_pos {ν : ℝ} (hν : -2 < ν) : 0 < gaussianRadialMoment ν := by
  rw [gaussianRadialMoment]
  simp_rw [gaussianPDFReal_mul_gaussianPDFReal_zero, mul_left_comm _ (2 * π)⁻¹]
  rw [integral_const_mul, _root_.integral_rpow_mul_exp_neg_mul_rpow two_pos (by linarith)
    one_half_pos]
  have : 0 < Gamma ((ν + 1 + 1) / 2) := Gamma_pos_of_pos (by linarith)
  positivity

/-- **Polar formula** for homogeneous functions under the standard bivariate Gaussian law. -/
theorem integral_gaussianReal_prod_of_polar {ν : ℝ} (h : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hpolar : ∀ ρ θ, 0 < ρ → θ ∈ Ioo (-π) π → h (ρ * cos θ, ρ * sin θ) = ρ ^ ν * g θ) :
    ∫ p, h p ∂(gaussianReal 0 1).prod (gaussianReal 0 1) =
      gaussianRadialMoment ν * ∫ θ in Ioo (-π) π, g θ := by
  have hmeas : Measurable fun p : ℝ × ℝ => gaussianPDF 0 1 p.1 * gaussianPDF 0 1 p.2 :=
    ((measurable_gaussianPDF _ _).comp measurable_fst).mul
      ((measurable_gaussianPDF _ _).comp measurable_snd)
  rw [gaussianReal_prod_eq_withDensity one_ne_zero,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (ae_of_all _ fun p => ENNReal.mul_lt_top (by simp [gaussianPDF]) (by simp [gaussianPDF])),
    ← integral_comp_polarCoord_symm, polarCoord_target, gaussianRadialMoment,
    Measure.volume_eq_prod, ← setIntegral_prod_mul]
  refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
  obtain ⟨ρ, θ⟩ := p
  obtain ⟨hρ, hθ⟩ := hp
  have hρ0 : 0 < ρ := hρ
  simp only [polarCoord_symm_apply, smul_eq_mul]
  have hden : (gaussianPDF 0 1 (ρ * cos θ) * gaussianPDF 0 1 (ρ * sin θ)).toReal =
      gaussianPDFReal 0 1 ρ * gaussianPDFReal 0 1 0 := by
    rw [gaussianPDF_mul_polar, ENNReal.toReal_mul, gaussianPDF, gaussianPDF,
      ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
      ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  rw [hden, hpolar ρ θ hρ0 hθ, rpow_add_one hρ0.ne']
  ring

/-! ### Angular integrals -/

private theorem continuous_max_cos_rpow {ν : ℝ} (hν : 0 < ν) (a : ℝ) :
    Continuous fun θ : ℝ => max (cos (|θ| + a)) 0 ^ ν :=
  (by fun_prop : Continuous fun θ : ℝ => max (cos (|θ| + a)) 0).rpow_const
    fun _ => Or.inr hν.le

/-- The angular integral `∫_{-π}^{π} max(cos(|θ| + a), 0)^ν dθ = 2 ∫_a^{π/2} cos^ν θ dθ`. -/
theorem integral_Ioo_max_cos_abs_add_rpow {a ν : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ π / 2)
    (hν : 0 < ν) :
    ∫ θ in Ioo (-π) π, max (cos (|θ| + a)) 0 ^ ν = 2 * ∫ θ in a..π / 2, cos θ ^ ν := by
  have hπ := pi_pos
  have hc := continuous_max_cos_rpow hν a
  set f : ℝ → ℝ := fun θ => max (cos (|θ| + a)) 0 ^ ν with hf
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have heven : ∫ θ in -π..0, f θ = ∫ θ in (0 : ℝ)..π, f θ := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := π) f
    rw [neg_zero] at h
    rw [← h]
    simp only [hf, abs_neg]
  have hshift : ∫ θ in (0 : ℝ)..π, f θ = ∫ u in a..π + a, max (cos u) 0 ^ ν := by
    have h := intervalIntegral.integral_comp_add_right (a := 0) (b := π)
      (fun u => max (cos u) 0 ^ ν) a
    rw [zero_add] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le hπ.le] at hθ
    simp only [hf, abs_of_nonneg hθ.1]
  have hcos : Continuous fun u : ℝ => max (cos u) 0 ^ ν :=
    (by fun_prop : Continuous fun u : ℝ => max (cos u) 0).rpow_const fun _ => Or.inr hν.le
  have hsplit : ∫ u in a..π + a, max (cos u) 0 ^ ν = ∫ u in a..π / 2, cos u ^ ν := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2)
      (hcos.intervalIntegrable _ _) (hcos.intervalIntegrable _ _)]
    have h2 : ∫ u in π / 2..π + a, max (cos u) 0 ^ ν = 0 := by
      rw [← intervalIntegral.integral_zero (a := π / 2) (b := π + a) (μ := volume)]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le (by linarith)] at hu
      have : cos u ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le hu.1 (by linarith [hu.2])
      simp [max_eq_right this, zero_rpow hν.ne']
    rw [h2, add_zero]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le ha] at hu
    have : 0 ≤ cos u := cos_nonneg_of_mem_Icc ⟨by linarith [hu.1], hu.2⟩
    simp only [max_eq_left this]
  rw [heven, hshift, hsplit]
  ring

/-! ### The symmetric representation of the bivariate normal law -/

/-- For `a = arccos(r)/2`, `(cos a Z₁ − sin a Z₂, cos a Z₁ + sin a Z₂)` has the law
`bivariateNormal r`. -/
theorem bivariateNormal_eq_map_symmetric {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    bivariateNormal r = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun p => (cos (arccos r / 2) * p.1 - sin (arccos r / 2) * p.2,
        cos (arccos r / 2) * p.1 + sin (arccos r / 2) * p.2)) := by
  set c := cos (arccos r / 2)
  set s := sin (arccos r / 2)
  have hcs : c ^ 2 + s ^ 2 = 1 := by rw [add_comm]; exact sin_sq_add_cos_sq _
  have hc2 : c ^ 2 = 1 / 2 + r / 2 := by
    rw [cos_sq, mul_div_cancel₀ _ two_ne_zero, cos_arccos hr.1 hr.2]
  refine (eq_bivariateNormal_of_linear_laws hr fun A B => ?_).symm
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have h2 : ((fun p : ℝ × ℝ => A * p.1 + B * p.2) ∘
      fun p : ℝ × ℝ => (c * p.1 - s * p.2, c * p.1 + s * p.2)) =
      fun p => ((A + B) * c) * p.1 + ((B - A) * s) * p.2 := by
    funext p
    simp only [Function.comp_apply]
    ring
  rw [h2, map_linear_prod_gaussianReal]
  congr 2
  simp only [NNReal.coe_one, mul_one]
  linear_combination (A ^ 2 + B ^ 2) * hcs + 4 * A * B * hc2 - 2 * A * B * hcs

/-! ### The two tail moments -/

/-- The joint tail moment `E[max(min(X, Y), 0)^ν]` for `(X, Y) ~ bivariateNormal r`. -/
noncomputable def normalJointTailMoment (ν r : ℝ) : ℝ :=
  ∫ p, max (min p.1 p.2) 0 ^ ν ∂bivariateNormal r

/-- The marginal tail moment `E[max(Z, 0)^ν]` for `Z ~ N(0, 1)`. -/
noncomputable def normalTailMoment (ν : ℝ) : ℝ := ∫ x, max x 0 ^ ν ∂gaussianReal 0 1

private theorem max_mul_rpow {ρ w ν : ℝ} (hρ : 0 < ρ) :
    max (ρ * w) 0 ^ ν = ρ ^ ν * max w 0 ^ ν := by
  rw [← mul_rpow hρ.le (le_max_right _ _), mul_max_of_nonneg _ _ hρ.le, mul_zero]

/-- Polar form of the joint tail moment. -/
theorem normalJointTailMoment_eq {ν r : ℝ} (hν : 0 < ν) (hr : r ∈ Icc (-1 : ℝ) 1) :
    normalJointTailMoment ν r =
      gaussianRadialMoment ν * (2 * ∫ θ in arccos r / 2..π / 2, cos θ ^ ν) := by
  have hπ := pi_pos
  set a := arccos r / 2 with ha_def
  have ha0 : 0 ≤ a := div_nonneg (arccos_nonneg r) zero_le_two
  have haπ : a ≤ π / 2 := div_le_div_of_nonneg_right (arccos_le_pi r) zero_le_two
  have hs : 0 ≤ sin a := sin_nonneg_of_nonneg_of_le_pi ha0 (by linarith)
  rw [normalJointTailMoment, bivariateNormal_eq_map_symmetric hr,
    integral_map (by fun_prop) ((by fun_prop : Measurable fun p : ℝ × ℝ =>
      max (min p.1 p.2) 0).pow_const ν).aestronglyMeasurable,
    ← integral_Ioo_max_cos_abs_add_rpow ha0 haπ hν]
  apply integral_gaussianReal_prod_of_polar
  intro ρ θ hρ hθ
  simp only
  rw [← max_mul_rpow hρ]
  congr 2
  rcases le_total 0 θ with h0 | h0
  · have hsin : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi h0 hθ.2.le
    rw [abs_of_nonneg h0, cos_add, min_eq_left (by nlinarith [mul_nonneg hρ.le hsin])]
    ring
  · have hsin : sin θ ≤ 0 := sin_nonpos_of_nonpos_of_neg_pi_le h0 hθ.1.le
    rw [abs_of_nonpos h0, cos_add, cos_neg, sin_neg,
      min_eq_right (by nlinarith [mul_nonneg hρ.le (neg_nonneg.2 hsin)])]
    ring

/-- Polar form of the marginal tail moment. -/
theorem normalTailMoment_eq {ν : ℝ} (hν : 0 < ν) :
    normalTailMoment ν = gaussianRadialMoment ν * (2 * ∫ θ in (0 : ℝ)..π / 2, cos θ ^ ν) := by
  have hπ := pi_pos
  have h := integral_fun_fst (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    (fun x : ℝ => max x 0 ^ ν)
  rw [probReal_univ, one_smul] at h
  rw [normalTailMoment, ← h, ← integral_Ioo_max_cos_abs_add_rpow le_rfl (by linarith) hν]
  apply integral_gaussianReal_prod_of_polar
  intro ρ θ hρ _
  simp only [add_zero, cos_abs]
  exact max_mul_rpow hρ

/-- The first coordinate of `bivariateNormal r` is standard normal. -/
theorem bivariateNormal_map_fst {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateNormal r).map Prod.fst = gaussianReal 0 1 := by
  have h := map_linear_bivariateNormal hr 1 0
  have hf : (fun p : ℝ × ℝ => 1 * p.1 + 0 * p.2) = Prod.fst := by funext p; ring
  rw [hf] at h
  rw [h]
  norm_num

/-- The marginal tail moment computed under `bivariateNormal r`. -/
theorem integral_max_fst_rpow_bivariateNormal {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) (ν : ℝ) :
    ∫ p, max p.1 0 ^ ν ∂bivariateNormal r = normalTailMoment ν := by
  rw [normalTailMoment, ← bivariateNormal_map_fst hr, integral_map (by fun_prop)
    ((by fun_prop : Measurable fun x : ℝ => max x 0).pow_const ν).aestronglyMeasurable]

/-- `|X|^ν` is integrable under `bivariateNormal r` for `ν ≥ 0`. -/
theorem integrable_abs_fst_rpow_bivariateNormal {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) {ν : ℝ}
    (hν : 0 < ν) : Integrable (fun p : ℝ × ℝ => |p.1| ^ ν) (bivariateNormal r) := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) ν.toNNReal).integrable_norm_rpow
    (by simpa using hν) ENNReal.coe_ne_top
  simp only [id, Real.norm_eq_abs, ENNReal.coe_toReal, Real.coe_toNNReal _ hν.le] at h
  rw [← bivariateNormal_map_fst hr] at h
  exact h.comp_measurable measurable_fst

/-- The joint tail moment is the angular ratio times the marginal one. -/
theorem normalJointTailMoment_div_normalTailMoment {ν r : ℝ} (hν : 0 < ν)
    (hr : r ∈ Icc (-1 : ℝ) 1) :
    normalJointTailMoment ν r / normalTailMoment ν =
      (∫ θ in arccos r / 2..π / 2, cos θ ^ ν) / ∫ θ in (0 : ℝ)..π / 2, cos θ ^ ν := by
  rw [normalJointTailMoment_eq hν hr, normalTailMoment_eq hν]
  have := (gaussianRadialMoment_pos (by linarith : -2 < ν)).ne'
  rw [mul_div_mul_left _ _ this, mul_div_mul_left _ _ two_ne_zero]

end ProbabilityTheory.Copula
