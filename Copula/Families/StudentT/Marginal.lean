/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.StudentT
import Copula.Families.StudentT.Distribution
import Copula.Families.Gaussian.Bivariate

/-! # The margins of the multivariate Student-t law

The library constructs the Student-t copula from the scale mixture `studentTLaw R ν`, the law of
`G^{-1/2} Z` with `Z ~ N(0, R)` independent of `G ~ Gamma(ν/2, ν/2)`. Here we show that every
one-dimensional margin of this law is the classical Student-t distribution with `ν` degrees of
freedom (`R i i = 1`):

`P(G^{-1/2} Z_i ∈ dx) = t_ν(x) dx`,  `t_ν(x) = c_ν (1 + x²/ν)^{-(ν+1)/2}`.

Consequently the marginal distribution functions used in the Sklar construction of `studentT`
are the Student-t distribution function `studentTCDF ν`, and the t copula is the copula of the
multivariate t distribution with `t_ν` margins:
`C(T_ν(x₁), …, T_ν(x_d)) = P(X₁ ≤ x₁, …, X_d ≤ x_d)`.

## Proof
Conditionally on `G = g > 0`, `G^{-1/2} Z_i ~ N(0, 1/g)`, with density
`√g (2π)^{-1/2} e^{-g x²/2}`. By Tonelli, the density of the mixture is

`∫_0^∞ (ν/2)^{ν/2}/Γ(ν/2) g^{ν/2-1} e^{-νg/2} √g (2π)^{-1/2} e^{-g x²/2} dg
  = K_ν (1 + x²/ν)^{-(ν+1)/2}`

by the Gamma integral; the constant `K_ν` is identified with `1 / ∫ (1 + y²/ν)^{-(ν+1)/2} dy`
because both sides are probability densities.

## Main results
* `studentTMeasure ν`: the Student-t distribution, `volume.withDensity (studentTPDF ν)`.
* `cdf_studentTMeasure`: its distribution function is `studentTCDF ν`.
* `marginal_gaussianScaleMixtureLaw`: margins of Gaussian scale mixtures.
* `map_gaussianReal_prod_gammaMeasure`: the law of `G^{-1/2} Z` is `studentTMeasure ν`.
* `marginal_studentTLaw`, `cdf_marginal_studentTLaw`.
* `cdf_studentT_studentTCDF`, `eq_studentT_of_cdf`: the t copula is the (unique) copula of the
  t law with `t_ν` margins; `cdf_studentT_corrMatrix` is the bivariate form.

## References
* S. Kotz, S. Nadarajah, *Multivariate t Distributions and Their Applications*, CUP 2004, Ch. 1.
* S. Demarta, A. McNeil, *The t copula and related copulas*, Int. Stat. Rev. 73 (2005).
-/

open MeasureTheory Set Real Filter
open scoped unitInterval ENNReal NNReal

namespace ProbabilityTheory

/-! ### The Student-t distribution as a measure -/

/-- The Student-t distribution with `ν` degrees of freedom, as a measure on `ℝ`. -/
noncomputable def studentTMeasure (ν : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (studentTPDF ν x)

theorem integrable_studentTKernel {ν : ℝ} (hν : 0 < ν) : Integrable (studentTKernel ν) :=
  Integrable.of_integral_ne_zero (integral_studentTKernel_pos hν).ne'

theorem integrable_studentTPDF {ν : ℝ} (hν : 0 < ν) : Integrable (studentTPDF ν) :=
  (integrable_studentTKernel hν).div_const _

theorem isProbabilityMeasure_studentTMeasure {ν : ℝ} (hν : 0 < ν) :
    IsProbabilityMeasure (studentTMeasure ν) := by
  constructor
  rw [studentTMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_studentTPDF hν)
      (ae_of_all _ fun x => (studentTPDF_pos hν x).le), integral_studentTPDF hν, ENNReal.ofReal_one]

/-- `P(T ∈ S) = ∫_S t_ν` for the Student-t distribution. -/
theorem studentTMeasure_real_apply {ν : ℝ} (hν : 0 < ν) {S : Set ℝ} (hS : MeasurableSet S) :
    (studentTMeasure ν).real S = ∫ x in S, studentTPDF ν x := by
  rw [measureReal_def, studentTMeasure, withDensity_apply _ hS,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_studentTPDF hν).integrableOn
      (ae_of_all _ fun x => (studentTPDF_pos hν x).le),
    ENNReal.toReal_ofReal (setIntegral_nonneg hS fun x _ => (studentTPDF_pos hν x).le)]

/-- The distribution function of `studentTMeasure ν` is `studentTCDF ν`. -/
theorem cdf_studentTMeasure {ν : ℝ} (hν : 0 < ν) :
    cdf (studentTMeasure ν) = studentTCDF ν := by
  have := isProbabilityMeasure_studentTMeasure hν
  funext x
  rw [cdf_eq_real, studentTMeasure_real_apply hν measurableSet_Iic, studentTCDF]

theorem studentTCDF_nonneg {ν : ℝ} (hν : 0 < ν) (x : ℝ) : 0 ≤ studentTCDF ν x := by
  rw [← cdf_studentTMeasure hν]
  exact cdf_nonneg _ x

theorem studentTCDF_le_one {ν : ℝ} (hν : 0 < ν) (x : ℝ) : studentTCDF ν x ≤ 1 := by
  have := isProbabilityMeasure_studentTMeasure hν
  rw [← cdf_studentTMeasure hν]
  exact cdf_le_one _ x

/-! ### The gamma mixture of centered normal laws -/

/-- The density `√g (2π)^{-1/2} e^{-g x²/2}` of `N(0, 1/g)`. -/
private noncomputable def mixDensity (g x : ℝ) : ℝ := √g / √(2 * π) * exp (-(g * x ^ 2) / 2)

private theorem measurable_mixDensity : Measurable (Function.uncurry mixDensity) := by
  unfold mixDensity Function.uncurry
  fun_prop

private theorem map_gaussianReal_inv_sqrt_mul {g : ℝ} (hg : 0 < g) :
    (gaussianReal 0 1).map (fun z => (√g)⁻¹ * z) =
      volume.withDensity fun x => ENNReal.ofReal (mixDensity g x) := by
  have hs : 0 < √g := Real.sqrt_pos.2 hg
  have h2 : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  rw [gaussianReal_map_const_mul, mul_zero, gaussianReal_of_var_ne_zero]
  swap
  · rw [mul_one, ne_eq, ← NNReal.coe_eq_zero, NNReal.coe_mk]
    positivity
  congr 1
  funext x
  rw [gaussianPDF]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_mk, mul_one, sub_zero]
  rw [inv_pow, Real.sq_sqrt hg.le, mixDensity, Real.sqrt_mul (by positivity), Real.sqrt_inv]
  congr 1
  · field_simp
  · congr 1
    field_simp

/-- The Gamma integral behind the Student-t density. -/
private theorem integral_gammaPDFReal_mul_mixDensity {ν : ℝ} (hν : 0 < ν) (x : ℝ) :
    ∫ g in Ioi 0, gammaPDFReal (ν / 2) (ν / 2) g * mixDensity g x =
      (ν / 2) ^ (ν / 2) / Gamma (ν / 2) / √(2 * π) *
        ((1 / (ν / 2 + x ^ 2 / 2)) ^ ((ν + 1) / 2) * Gamma ((ν + 1) / 2)) := by
  have hc : 0 < ν / 2 + x ^ 2 / 2 := by positivity
  rw [← integral_rpow_mul_exp_neg_mul_Ioi (by positivity : (0 : ℝ) < (ν + 1) / 2) hc,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun g hg => ?_
  have hg : 0 < g := hg
  simp only [gammaPDFReal, hg.le, ↓reduceIte]
  rw [mixDensity, Real.sqrt_eq_rpow]
  have hpow : g ^ (ν / 2 - 1) * g ^ (1 / 2 : ℝ) = g ^ ((ν + 1) / 2 - 1) := by
    rw [← rpow_add hg]
    ring_nf
  have hexp : exp (-(ν / 2 * g)) * exp (-(g * x ^ 2) / 2) = exp (-((ν / 2 + x ^ 2 / 2) * g)) := by
    rw [← exp_add]
    ring_nf
  calc (ν / 2) ^ (ν / 2) / Gamma (ν / 2) * g ^ (ν / 2 - 1) * exp (-(ν / 2 * g)) *
        (g ^ (1 / 2 : ℝ) / √(2 * π) * exp (-(g * x ^ 2) / 2))
      = (ν / 2) ^ (ν / 2) / Gamma (ν / 2) / √(2 * π) *
          ((g ^ (ν / 2 - 1) * g ^ (1 / 2 : ℝ)) *
            (exp (-(ν / 2 * g)) * exp (-(g * x ^ 2) / 2))) := by ring
    _ = _ := by rw [hpow, hexp]

/-- The normalizing constant of the mixture density. -/
private noncomputable def mixConst (ν : ℝ) : ℝ :=
  (ν / 2) ^ (ν / 2) / Gamma (ν / 2) / √(2 * π) * Gamma ((ν + 1) / 2) *
    (1 / (ν / 2)) ^ ((ν + 1) / 2)

private theorem mixture_density_eq {ν : ℝ} (hν : 0 < ν) (x : ℝ) :
    ∫ g in Ioi 0, gammaPDFReal (ν / 2) (ν / 2) g * mixDensity g x =
      mixConst ν * studentTKernel ν x := by
  rw [integral_gammaPDFReal_mul_mixDensity hν, mixConst, studentTKernel]
  have h1 : 0 < 1 + x ^ 2 / ν := by positivity
  have hsplit : ν / 2 + x ^ 2 / 2 = ν / 2 * (1 + x ^ 2 / ν) := by field_simp
  rw [hsplit, one_div (ν / 2 * _), mul_inv, mul_rpow (by positivity) (inv_nonneg.2 h1.le),
    inv_rpow h1.le, ← rpow_neg h1.le, one_div (ν / 2), neg_div]
  ring

private theorem lintegral_gammaMeasure_mixDensity {ν : ℝ} (hν : 0 < ν) (x : ℝ) :
    ∫⁻ g, ENNReal.ofReal (mixDensity g x) ∂gammaMeasure (ν / 2) (ν / 2) =
      ENNReal.ofReal (mixConst ν * studentTKernel ν x) := by
  set F : ℝ → ℝ := fun g => gammaPDFReal (ν / 2) (ν / 2) g * mixDensity g x with hF
  have hmeas : Measurable fun g => ENNReal.ofReal (mixDensity g x) :=
    ENNReal.measurable_ofReal.comp
      (measurable_mixDensity.comp (measurable_id.prodMk measurable_const))
  have hind : F = (Ioi (0 : ℝ)).indicator F := by
    funext g
    by_cases hg : 0 < g
    · rw [indicator_of_mem (show g ∈ Ioi (0 : ℝ) from hg)]
    · rw [indicator_of_notMem (show g ∉ Ioi (0 : ℝ) from hg), hF]
      rcases lt_or_eq_of_le (not_lt.1 hg) with hg' | hg'
      · simp [gammaPDFReal, not_le.2 hg']
      · simp [hg', mixDensity]
  have hFnn : ∀ g, 0 ≤ F g := fun g => mul_nonneg
    (gammaPDFReal_nonneg (by positivity) (by positivity) g)
    (by unfold mixDensity; positivity)
  have hint : IntegrableOn F (Ioi 0) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [mixture_density_eq hν]
    have := studentTKernel_pos hν x
    have hK : 0 < mixConst ν := by unfold mixConst; positivity
    positivity
  rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ (f := gammaPDF (ν / 2) (ν / 2))
    (measurable_gammaPDFReal _ _).ennreal_ofReal hmeas]
  have hpt : ∀ g, (gammaPDF (ν / 2) (ν / 2) * fun g => ENNReal.ofReal (mixDensity g x)) g =
      ENNReal.ofReal (F g) := fun g => by
    rw [Pi.mul_apply, gammaPDF, hF, ENNReal.ofReal_mul
      (gammaPDFReal_nonneg (by positivity) (by positivity) g)]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal
      (by rw [hind]; exact (integrable_indicator_iff measurableSet_Ioi).2 hint)
      (ae_of_all _ hFnn),
    hind, integral_indicator measurableSet_Ioi, mixture_density_eq hν]

/-- **The law of `G^{-1/2} Z`** for `Z ~ N(0, 1)` independent of `G ~ Gamma(ν/2, ν/2)` is the
Student-t distribution with `ν` degrees of freedom. -/
theorem map_gaussianReal_prod_gammaMeasure {ν : ℝ} (hν : 0 < ν) :
    ((gaussianReal 0 1).prod (gammaMeasure (ν / 2) (ν / 2))).map
      (fun p => (√p.2)⁻¹ * p.1) = studentTMeasure ν := by
  have hγ : IsProbabilityMeasure (gammaMeasure (ν / 2) (ν / 2)) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by positivity)
  have hF : Measurable fun p : ℝ × ℝ => (√p.2)⁻¹ * p.1 := by fun_prop
  -- the mixture has density `mixConst ν * kernel`
  have hmix : ((gaussianReal 0 1).prod (gammaMeasure (ν / 2) (ν / 2))).map
      (fun p => (√p.2)⁻¹ * p.1) =
      volume.withDensity fun x => ENNReal.ofReal (mixConst ν * studentTKernel ν x) := by
    ext S hS
    rw [Measure.map_apply hF hS, Measure.prod_apply_symm (hF hS), withDensity_apply _ hS]
    have hsec : ∀ᵐ g ∂gammaMeasure (ν / 2) (ν / 2),
        gaussianReal 0 1 ((fun z => (z, g)) ⁻¹' ((fun p : ℝ × ℝ => (√p.2)⁻¹ * p.1) ⁻¹' S)) =
          ∫⁻ x in S, ENNReal.ofReal (mixDensity g x) := by
      filter_upwards [ae_pos_gammaMeasure (ν / 2) (ν / 2)] with g hg
      rw [← withDensity_apply _ hS, ← map_gaussianReal_inv_sqrt_mul hg,
        Measure.map_apply (by fun_prop) hS]
      rfl
    rw [lintegral_congr_ae hsec,
      lintegral_lintegral_swap (f := fun g x => ENNReal.ofReal (mixDensity g x))
        (ENNReal.measurable_ofReal.comp measurable_mixDensity).aemeasurable]
    exact lintegral_congr fun x => lintegral_gammaMeasure_mixDensity hν x
  -- identify the constant through the total mass
  have hprob : IsProbabilityMeasure (((gaussianReal 0 1).prod
      (gammaMeasure (ν / 2) (ν / 2))).map (fun p => (√p.2)⁻¹ * p.1)) :=
    inferInstance
  have hK : 0 < mixConst ν := by unfold mixConst; positivity
  have hkint := integrable_studentTKernel hν
  have hmass : mixConst ν * ∫ y, studentTKernel ν y = 1 := by
    have h := hprob.measure_univ
    rw [hmix, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hkint.const_mul _)
        (ae_of_all _ fun y => (mul_pos hK (studentTKernel_pos hν y)).le),
      integral_const_mul] at h
    exact (ENNReal.ofReal_eq_one.1 h)
  rw [hmix, studentTMeasure]
  congr 1
  funext x
  congr 1
  rw [studentTPDF, eq_div_iff (integral_studentTKernel_pos hν).ne', mul_assoc,
    mul_comm (studentTKernel ν x), ← mul_assoc, hmass, one_mul]

namespace Copula

variable {d : ℕ}

/-- **Margins of a Gaussian scale mixture**: if `R i i = 1`, the `i`th coordinate of
`s(T) · Z` has the law of `s(T) · Z₀` with `Z₀ ~ N(0, 1)` independent of `T`. -/
theorem marginal_gaussianScaleMixtureLaw (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (hdiag : ∀ i, R i i = 1) (μ : ProbabilityMeasure ℝ) {s : ℝ → ℝ} (hs : Measurable s)
    (i : Fin d) :
    marginal (gaussianScaleMixtureLaw R μ s) i =
      ((gaussianReal 0 1).prod μ.toMeasure).map (fun p => s p.2 * p.1) := by
  have hmarg : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R).map
      (fun x => x i) = gaussianReal 0 1 := by
    have h := (measurePreserving_eval_multivariateGaussian
      (μ := (0 : EuclideanSpace ℝ (Fin d))) hR (i := i)).map_eq
    have hz : (0 : EuclideanSpace ℝ (Fin d)) i = (0 : ℝ) := rfl
    rw [hz, hdiag, Real.toNNReal_one] at h
    exact h
  have he : marginal (gaussianScaleMixtureLaw R μ s) i =
      ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R).prod μ.toMeasure).map
        (fun p => s p.2 * p.1 i) :=
    Measure.map_map (measurable_pi_apply i) (Measurable.of_eval fun j => by fun_prop)
  rw [he, ← hmarg, ← Measure.map_id (μ := μ.toMeasure),
    Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_id]
  rfl

/-- **The margins of the multivariate t law are Student-t distributions**: every coordinate of
`studentTLaw R ν` (with unit diagonal) has the density `studentTPDF ν`. -/
theorem marginal_studentTLaw (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (hdiag : ∀ i, R i i = 1) {ν : ℝ} (hν : 0 < ν) (i : Fin d) :
    marginal (studentTLaw R ν hν) i = studentTMeasure ν := by
  rw [studentTLaw, marginal_gaussianScaleMixtureLaw R hR hdiag _ (by fun_prop) i]
  exact map_gaussianReal_prod_gammaMeasure hν

/-- The marginal distribution functions of the t law are `studentTCDF ν`. -/
theorem cdf_marginal_studentTLaw (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (hdiag : ∀ i, R i i = 1) {ν : ℝ} (hν : 0 < ν) (i : Fin d) :
    ProbabilityTheory.cdf (marginal (studentTLaw R ν hν) i) = studentTCDF ν := by
  rw [marginal_studentTLaw R hR hdiag hν i, cdf_studentTMeasure hν]

/-- The probability integral transform of the Sklar construction is the Student-t CDF. -/
theorem marginalTransform_studentTLaw (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (hdiag : ∀ i, R i i = 1) {ν : ℝ} (hν : 0 < ν) (x : Fin d → ℝ) :
    marginalTransform (studentTLaw R ν hν) x = fun i => cdfUnit (studentTMeasure ν) (x i) := by
  funext i
  rw [marginalTransform, marginal_studentTLaw R hR hdiag hν i]

/-- **The t copula is the copula of the multivariate t distribution with `t_ν` margins**:
`C(T_ν(x₁), …, T_ν(x_d)) = P(X ≤ x)` where `T_ν = studentTCDF ν`. -/
theorem cdf_studentT_studentTCDF (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (hdiag : ∀ i, R i i = 1) {ν : ℝ} (hν : 0 < ν) (x : Fin d → ℝ) :
    (studentT R hR hdiag ν hν).cdf (fun i => cdfUnit (studentTMeasure ν) (x i)) =
      (studentTLaw R ν hν).toMeasure.real (Iic x) := by
  rw [← marginalTransform_studentTLaw R hR hdiag hν x]
  exact isSklarCopula_studentT R hR hdiag ν hν x

/-- Uniqueness: a copula `C` with `C(T_ν(x₁), …, T_ν(x_d)) = P(X ≤ x)` for all `x` is the
t copula. -/
theorem eq_studentT_of_cdf (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (hdiag : ∀ i, R i i = 1) {ν : ℝ} (hν : 0 < ν) (C : Copula d)
    (hC : ∀ x : Fin d → ℝ, C.cdf (fun i => cdfUnit (studentTMeasure ν) (x i)) =
      (studentTLaw R ν hν).toMeasure.real (Iic x)) :
    C = studentT R hR hdiag ν hν := by
  have hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal (studentTLaw R ν hν) i)) :=
    continuous_gaussianScaleMixtureLaw_marginal R hR hdiag _ _ (by fun_prop) (by
      filter_upwards [ae_pos_gammaMeasure (ν / 2) (ν / 2)] with t ht
      exact inv_pos.mpr (Real.sqrt_pos.2 ht))
  refine IsSklarCopula.unique hc (fun x => ?_) (isSklarCopula_studentT R hR hdiag ν hν)
  rw [marginalTransform_studentTLaw R hR hdiag hν x]
  exact hC x

/-- **Bivariate form**: for the bivariate t law `(X, Y)` with correlation `r`,
`C_{ν,r}(T_ν(x), T_ν(y)) = P(X ≤ x, Y ≤ y)`. -/
theorem cdf_studentT_corrMatrix {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) {ν : ℝ} (hν : 0 < ν)
    (x y : ℝ) :
    (studentT (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r) ν hν).cdf
        ![cdfUnit (studentTMeasure ν) x, cdfUnit (studentTMeasure ν) y] =
      (studentTLaw (corrMatrix r) ν hν).toMeasure.real {z | z 0 ≤ x ∧ z 1 ≤ y} := by
  have h := cdf_studentT_studentTCDF (corrMatrix r) (posSemidef_corrMatrix hr)
    (corrMatrix_diag r) hν ![x, y]
  have hpt : (fun i => cdfUnit (studentTMeasure ν) (![x, y] i)) =
      ![cdfUnit (studentTMeasure ν) x, cdfUnit (studentTMeasure ν) y] := by
    funext i
    fin_cases i <;> rfl
  rw [hpt] at h
  rw [h]
  congr 1
  ext z
  simp [Pi.le_def, Fin.forall_fin_two]

end Copula

open Copula in
/-- The Student-t distribution function is continuous. -/
theorem continuous_studentTCDF {ν : ℝ} (hν : 0 < ν) : Continuous (studentTCDF ν) := by
  have hr : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hc := continuous_gaussianScaleMixtureLaw_marginal (corrMatrix 0)
    (posSemidef_corrMatrix hr) (corrMatrix_diag 0)
    (gammaProbability (ν / 2) (ν / 2) (by positivity) (by positivity)) (fun t => (√t)⁻¹)
    (by fun_prop) (by
      filter_upwards [ae_pos_gammaMeasure (ν / 2) (ν / 2)] with t ht
      exact inv_pos.mpr (Real.sqrt_pos.2 ht)) 0
  have h := cdf_marginal_studentTLaw _ (posSemidef_corrMatrix hr) (corrMatrix_diag 0) hν 0
  rw [studentTLaw] at h
  rwa [h] at hc

end ProbabilityTheory
