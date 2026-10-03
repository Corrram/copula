/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! # Orthant probabilities of the bivariate normal law (Sheppard's formula)

For a centered bivariate normal vector `(X, Y)` with equal variances and correlation `r`,
`P(X > 0, Y > 0) = P(X ≤ 0, Y ≤ 0) = 1/4 + arcsin r / (2π)` (Sheppard 1899).

The bivariate normal law is described through its one-dimensional projections: we assume that
`aX + bY ~ N(0, (a² + 2abr + b²) v)` for all real `a, b`. By the Cramér–Wold device
(`measure_prod_eq_of_map_linear_eq`), this identifies the law of `(X, Y)` with that of
`(W₁, r W₁ + √(1 − r²) W₂)` for independent `W₁, W₂ ~ N(0, v)`. The probability of the
corresponding wedge is computed in polar coordinates: the angle of `(W₁, W₂)` is uniform.

## Main results
* `measure_prod_eq_of_map_linear_eq`: Cramér–Wold for finite measures on `ℝ × ℝ`.
* `map_linear_prod_gaussianReal`: `aW₁ + bW₂ ~ N(0, a²v + b²w)` for independent Gaussians.
* `gaussianReal_prod_wedge`: the wedge `{0 < p₁, 0 < cos α p₁ + sin α p₂}` has mass `(π − α)/(2π)`.
* `orthant_pos_of_linear_laws`, `orthant_nonpos_of_linear_laws`: Sheppard's formula.

## References
* W. F. Sheppard, *On the application of the theory of error to cases of normal distribution and
  normal correlation*, Phil. Trans. R. Soc. A 192 (1899).
* W. H. Kruskal, *Ordinal measures of association*, J. Amer. Statist. Assoc. 53 (1958).
-/

open MeasureTheory Set Real
open scoped ENNReal NNReal

namespace ProbabilityTheory.Copula

/-- **Cramér–Wold device** on `ℝ × ℝ`: two finite measures with the same laws of all linear
forms `a p₁ + b p₂` coincide. -/
theorem measure_prod_eq_of_map_linear_eq {μ ν : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ a b : ℝ, μ.map (fun p => a * p.1 + b * p.2) = ν.map (fun p => a * p.1 + b * p.2)) :
    μ = ν := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
  have hL : (L : ℝ × ℝ → ℝ) = fun p => L (1, 0) * p.1 + L (0, 1) * p.2 := by
    funext p
    have hp : p = p.1 • ((1 : ℝ), (0 : ℝ)) + p.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hp]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm p.1, mul_comm p.2]
  rw [hL, h]

/-- Gaussian laws only depend on the real value of the variance. -/
theorem gaussianReal_congr_var {m : ℝ} {v w : ℝ≥0} (h : (v : ℝ) = w) :
    gaussianReal m v = gaussianReal m w := by
  rw [NNReal.eq h]

/-- A linear combination of two independent centered Gaussians is a centered Gaussian. -/
theorem map_linear_prod_gaussianReal (v w : ℝ≥0) (a b : ℝ) :
    ((gaussianReal 0 v).prod (gaussianReal 0 w)).map (fun p => a * p.1 + b * p.2) =
      gaussianReal 0 (a ^ 2 * v + b ^ 2 * w).toNNReal := by
  have h1 : (fun p : ℝ × ℝ => a * p.1 + b * p.2) =
      (fun p : ℝ × ℝ => p.1 + p.2) ∘ Prod.map (fun x => a * x) (fun x => b * x) := rfl
  rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, gaussianReal_map_const_mul]
  change gaussianReal _ _ ∗ gaussianReal _ _ = _
  rw [gaussianReal_conv_gaussianReal]
  simp only [mul_zero, add_zero]
  apply gaussianReal_congr_var
  rw [Real.coe_toNNReal _ (by positivity)]
  simp

/-- The product of two copies of `N(0, v)` has the product Gaussian density. -/
theorem gaussianReal_prod_eq_withDensity {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal 0 v).prod (gaussianReal 0 v) =
      volume.withDensity (fun p : ℝ × ℝ => gaussianPDF 0 v p.1 * gaussianPDF 0 v p.2) := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
    Measure.volume_eq_prod]

/-- The product Gaussian density is radial. -/
theorem gaussianPDF_mul_polar (v : ℝ≥0) (ρ θ : ℝ) :
    gaussianPDF 0 v (ρ * cos θ) * gaussianPDF 0 v (ρ * sin θ) =
      gaussianPDF 0 v ρ * gaussianPDF 0 v 0 := by
  simp only [gaussianPDF, gaussianPDFReal, sub_zero]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_mul_mul_comm, mul_mul_mul_comm _ (rexp _), ← Real.exp_add, ← Real.exp_add,
    ← add_div, ← add_div]
  congr 3
  linear_combination (-ρ ^ 2) * sin_sq_add_cos_sq θ

/-- Polar-coordinate formula for the mass of a cone under the product Gaussian law. -/
theorem gaussianReal_prod_cone {v : ℝ≥0} (hv : v ≠ 0) (S : Set (ℝ × ℝ)) (A : Set ℝ)
    (hS : MeasurableSet S) (hA : MeasurableSet A)
    (hcone : ∀ ρ θ, 0 < ρ → θ ∈ Ioo (-π) π → ((ρ * cos θ, ρ * sin θ) ∈ S ↔ θ ∈ A)) :
    (gaussianReal 0 v).prod (gaussianReal 0 v) S =
      (∫⁻ ρ in Ioi 0, ENNReal.ofReal ρ * (gaussianPDF 0 v ρ * gaussianPDF 0 v 0)) *
        volume (A ∩ Ioo (-π) π) := by
  rw [gaussianReal_prod_eq_withDensity hv, withDensity_apply _ hS, ← lintegral_indicator hS,
    ← lintegral_comp_polarCoord_symm, polarCoord_target]
  rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    (g := fun p : ℝ × ℝ => (ENNReal.ofReal p.1 * (gaussianPDF 0 v p.1 * gaussianPDF 0 v 0)) *
      A.indicator 1 p.2)]
  · rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
      lintegral_prod_mul (f := fun ρ => ENNReal.ofReal ρ * (gaussianPDF 0 v ρ * gaussianPDF 0 v 0))
        (g := A.indicator 1)
        (ENNReal.measurable_ofReal.mul ((measurable_gaussianPDF _ _).mul_const _)).aemeasurable
        ((measurable_one.indicator hA).aemeasurable), lintegral_indicator_one hA,
      Measure.restrict_apply hA]
  · rintro ⟨ρ, θ⟩ ⟨hρ, hθ⟩
    simp only [polarCoord_symm_apply, smul_eq_mul]
    by_cases hθA : θ ∈ A
    · rw [indicator_of_mem ((hcone ρ θ hρ hθ).2 hθA), indicator_of_mem hθA, Pi.one_apply, mul_one,
        gaussianPDF_mul_polar]
    · rw [indicator_of_notMem (fun h => hθA ((hcone ρ θ hρ hθ).1 h)), indicator_of_notMem hθA,
        mul_zero, mul_zero]

/-- The angular description of the wedge `{0 < p₁, 0 < cos α p₁ + sin α p₂}`. -/
theorem wedge_angle_iff {α ρ θ : ℝ} (hα0 : 0 ≤ α) (hαπ : α ≤ π) (hρ : 0 < ρ)
    (hθ : θ ∈ Ioo (-π) π) :
    (0 < ρ * cos θ ∧ 0 < cos α * (ρ * cos θ) + sin α * (ρ * sin θ)) ↔
      θ ∈ Ioo (α - π / 2) (π / 2) := by
  have hc : cos α * (ρ * cos θ) + sin α * (ρ * sin θ) = ρ * cos (θ - α) := by
    rw [cos_sub]; ring
  rw [hc, mul_pos_iff_of_pos_left hρ, mul_pos_iff_of_pos_left hρ]
  obtain ⟨h1, h2⟩ := hθ
  constructor
  · rintro ⟨hc1, hc2⟩
    have hθ2 : θ < π / 2 := by
      by_contra h
      exact absurd hc1 (not_lt.2 (cos_nonpos_of_pi_div_two_le_of_le (not_lt.1 h) (by linarith)))
    have hθ1 : -(π / 2) < θ := by
      by_contra h
      have := cos_nonpos_of_pi_div_two_le_of_le (x := -θ) (by linarith [not_lt.1 h])
        (by linarith)
      rw [cos_neg] at this
      linarith
    refine ⟨?_, hθ2⟩
    by_contra h
    have := cos_nonpos_of_pi_div_two_le_of_le (x := -(θ - α)) (by linarith [not_lt.1 h])
      (by linarith)
    rw [cos_neg] at this
    linarith
  · rintro ⟨h3, h4⟩
    exact ⟨cos_pos_of_mem_Ioo ⟨by linarith, h4⟩, cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩⟩

/-- The wedge between the directions `0` and `α ∈ [0, π]` (angle `π − α`) has Gaussian mass
`(π − α)/(2π)`. -/
theorem gaussianReal_prod_wedge {v : ℝ≥0} (hv : v ≠ 0) {α : ℝ} (hα0 : 0 ≤ α) (hαπ : α ≤ π) :
    (gaussianReal 0 v).prod (gaussianReal 0 v)
        {p | 0 < p.1 ∧ 0 < cos α * p.1 + sin α * p.2} =
      ENNReal.ofReal ((π - α) / (2 * π)) := by
  have htot := gaussianReal_prod_cone hv univ univ MeasurableSet.univ MeasurableSet.univ
    (fun _ _ _ _ => by simp)
  rw [measure_univ, univ_inter, Real.volume_Ioo] at htot
  have hw := gaussianReal_prod_cone hv {p : ℝ × ℝ | 0 < p.1 ∧ 0 < cos α * p.1 + sin α * p.2}
    (Ioo (α - π / 2) (π / 2))
    ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const
        (by fun_prop : Measurable fun p : ℝ × ℝ => cos α * p.1 + sin α * p.2)))
    measurableSet_Ioo
    (fun ρ θ hρ hθ => wedge_angle_iff hα0 hαπ hρ hθ)
  have hsub : Ioo (α - π / 2) (π / 2) ∩ Ioo (-π) π = Ioo (α - π / 2) (π / 2) :=
    inter_eq_left.2 (Ioo_subset_Ioo (by linarith [pi_pos]) (by linarith [pi_pos]))
  have e1 : π / 2 - (α - π / 2) = π - α := by ring
  have e2 : π - -π = 2 * π := by ring
  rw [e2] at htot
  rw [hw, hsub, Real.volume_Ioo, e1, ENNReal.eq_inv_of_mul_eq_one_left htot.symm,
    ENNReal.ofReal_div_of_pos (by positivity), div_eq_mul_inv, mul_comm]

/-- A random variable with a nondegenerate centered Gaussian law is almost surely nonzero. -/
theorem ae_ne_zero_of_map_eq_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : Measurable X) {w : ℝ≥0} (hw : w ≠ 0) (h : μ.map X = gaussianReal 0 w) :
    ∀ᵐ ω ∂μ, X ω ≠ 0 := by
  let : NullSingletonClass (gaussianReal 0 w) := nullSingletonClass_gaussianReal hw
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have : {ω | X ω = 0} = X ⁻¹' {0} := rfl
  rw [this, ← Measure.map_apply hX (measurableSet_singleton 0), h, measure_singleton]

/-- **Sheppard's formula** (positive orthant). If every linear form `aX + bY` has law
`N(0, (a² + 2abr + b²) v)` with `v > 0`, i.e. `(X, Y)` is centered bivariate normal with equal
variances `v` and correlation `r`, then `P(X > 0, Y > 0) = 1/4 + arcsin r / (2π)`. -/
theorem orthant_pos_of_linear_laws {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    {r v : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) (hv : 0 < v)
    (hlaw : ∀ a b : ℝ, μ.map (fun ω => a * X ω + b * Y ω) =
      gaussianReal 0 ((a ^ 2 + 2 * a * b * r + b ^ 2) * v).toNNReal) :
    μ.real {ω | 0 < X ω ∧ 0 < Y ω} = 1 / 4 + arcsin r / (2 * π) := by
  set s := √(1 - r ^ 2) with hs_def
  have hs2 : s ^ 2 = 1 - r ^ 2 := Real.sq_sqrt (by nlinarith [hr.1, hr.2])
  set V : ℝ≥0 := v.toNNReal with hV_def
  have hVv : (V : ℝ) = v := Real.coe_toNNReal _ hv.le
  have hV : V ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hVv
    linarith
  have hlawXY : μ.map (fun ω => (X ω, Y ω)) =
      ((gaussianReal 0 V).prod (gaussianReal 0 V)).map (fun p => (p.1, r * p.1 + s * p.2)) := by
    apply measure_prod_eq_of_map_linear_eq
    intro a b
    rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    have h2 : ((fun p : ℝ × ℝ => a * p.1 + b * p.2) ∘ fun p : ℝ × ℝ => (p.1, r * p.1 + s * p.2)) =
        fun p => (a + b * r) * p.1 + (b * s) * p.2 := by
      funext p
      simp only [Function.comp_apply]
      ring
    rw [h2, map_linear_prod_gaussianReal]
    exact (hlaw a b).trans (by
      congr 2
      rw [hVv]
      linear_combination (-(b ^ 2) * v) * hs2)
  have hmeas : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd)
  have hpre : {ω | 0 < X ω ∧ 0 < Y ω} =
      (fun ω => (X ω, Y ω)) ⁻¹' {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} := rfl
  have hpre' : (fun p : ℝ × ℝ => (p.1, r * p.1 + s * p.2)) ⁻¹' {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} =
      {p | 0 < p.1 ∧ 0 < cos (arccos r) * p.1 + sin (arccos r) * p.2} := by
    rw [cos_arccos hr.1 hr.2, sin_arccos]
    rfl
  rw [measureReal_def, hpre, ← Measure.map_apply (by fun_prop) hmeas, hlawXY,
    Measure.map_apply (by fun_prop) hmeas, hpre',
    gaussianReal_prod_wedge hV (arccos_nonneg r) (arccos_le_pi r),
    ENNReal.toReal_ofReal (div_nonneg (by linarith [arccos_le_pi r]) (by positivity)),
    arccos_eq_pi_div_two_sub_arcsin]
  field_simp
  ring

/-- **Sheppard's formula** (negative orthant): under the hypotheses of
`orthant_pos_of_linear_laws`, `P(X ≤ 0, Y ≤ 0) = 1/4 + arcsin r / (2π)`. -/
theorem orthant_nonpos_of_linear_laws {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    {r v : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) (hv : 0 < v)
    (hlaw : ∀ a b : ℝ, μ.map (fun ω => a * X ω + b * Y ω) =
      gaussianReal 0 ((a ^ 2 + 2 * a * b * r + b ^ 2) * v).toNNReal) :
    μ.real {ω | X ω ≤ 0 ∧ Y ω ≤ 0} = 1 / 4 + arcsin r / (2 * π) := by
  have hneg := orthant_pos_of_linear_laws μ hX.neg hY.neg hr hv (fun a b => by
    have h := hlaw (-a) (-b)
    have hf : (fun ω => -a * X ω + -b * Y ω) = fun ω => a * (-X) ω + b * (-Y) ω := by
      funext ω
      simp only [Pi.neg_apply]
      ring
    rw [hf] at h
    rw [h]
    congr 2
    ring)
  have hv' : (v.toNNReal) ≠ 0 := by
    simpa [Real.toNNReal_eq_zero, not_le] using hv
  have h1 : μ.map X = gaussianReal 0 v.toNNReal := by
    have h := hlaw 1 0
    have hf : (fun ω => 1 * X ω + 0 * Y ω) = X := by funext ω; ring
    rw [hf] at h
    rw [h]
    congr 2
    ring
  have h2 : μ.map Y = gaussianReal 0 v.toNNReal := by
    have h := hlaw 0 1
    have hf : (fun ω => 0 * X ω + 1 * Y ω) = Y := by funext ω; ring
    rw [hf] at h
    rw [h]
    congr 2
    ring
  rw [← hneg]
  apply measureReal_congr
  filter_upwards [ae_ne_zero_of_map_eq_gaussianReal hX hv' h1,
    ae_ne_zero_of_map_eq_gaussianReal hY hv' h2] with ω hXω hYω
  simp only [Pi.neg_apply, neg_pos, eq_iff_iff]
  change (X ω ≤ 0 ∧ Y ω ≤ 0) ↔ (X ω < 0 ∧ Y ω < 0)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨lt_of_le_of_ne h1 hXω, lt_of_le_of_ne h2 hYω⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.le, h2.le⟩

end ProbabilityTheory.Copula
