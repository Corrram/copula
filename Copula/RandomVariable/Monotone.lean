/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.RandomVariable.Invariance
import Copula.Support

/-!
# Monotone functional dependence and the Fréchet bounds

Nelsen, *An Introduction to Copulas*, second edition, Theorem 2.5.4 and Corollary 2.5.5
(random-variable version, for laws on `Fin 2 → ℝ` with continuous marginal CDFs).

For such a law `μ`, the Sklar copula is the law of `(F₀ x₀, F₁ x₁)`. It equals the comonotonic copula
`M` exactly when `F₀ x₀ = F₁ x₁` almost surely, and the countermonotonic copula `W` exactly when
`F₁ x₁ = 1 - F₀ x₀` almost surely. If the second coordinate is almost surely a strictly increasing
(respectively decreasing) function of the first, these almost-sure identities hold, so the copula
is `M` (respectively `W`).

The converse implication of Nelsen's Theorem 2.5.4, producing a strictly monotone function from
`C = M`, is not formalized here.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The Sklar copula of a bivariate law with continuous marginals is `M` if and only if the
probability integral transforms of the two coordinates agree almost surely. -/
theorem ofContinuousMarginals_eq_comonotonic_iff (μ : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) :
    ofContinuousMarginals μ hc = comonotonic 2 ↔
      ∀ᵐ x ∂μ.toMeasure, marginalTransform μ x 0 = marginalTransform μ x 1 := by
  rw [eq_comonotonic_iff_ae_eval_eq]
  change (∀ᵐ z ∂(μ.toMeasure.map (marginalTransform μ)), z 0 = z 1) ↔ _
  exact ae_map_iff (measurable_marginalTransform μ).aemeasurable
    (measurableSet_eq_fun (by fun_prop) (by fun_prop))

/-- The Sklar copula of a bivariate law with continuous marginals is `W` if and only if the
second probability integral transform is almost surely one minus the first. -/
theorem ofContinuousMarginals_eq_countermonotonic_iff (μ : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) :
    ofContinuousMarginals μ hc = countermonotonic ↔
      ∀ᵐ x ∂μ.toMeasure,
        marginalTransform μ x 1 = unitInterval.symm (marginalTransform μ x 0) := by
  rw [eq_countermonotonic_iff_ae_eval_eq_symm]
  change (∀ᵐ z ∂(μ.toMeasure.map (marginalTransform μ)), z 1 = unitInterval.symm (z 0)) ↔ _
  exact ae_map_iff (measurable_marginalTransform μ).aemeasurable
    (measurableSet_eq_fun (by fun_prop) (by fun_prop))

/-- If the second coordinate is almost surely `g` of the first, its law is the image law. -/
theorem marginal_one_eq_map_of_ae_eq (μ : ProbabilityMeasure (Fin 2 → ℝ)) {g : ℝ → ℝ}
    (hg : Measurable g) (h : ∀ᵐ x ∂μ.toMeasure, x 1 = g (x 0)) :
    marginal μ 1 = (marginal μ 0).map g := by
  have h1 : μ.toMeasure.map (fun x => x 1) = μ.toMeasure.map (g ∘ fun x => x 0) :=
    Measure.map_congr (by filter_upwards [h] with x hx; exact hx)
  exact h1.trans
    (Measure.map_map (μ := μ.toMeasure) hg (measurable_pi_apply (0 : Fin 2))).symm

theorem cdf_marginal_one_of_ae_eq_strictMono (μ : ProbabilityMeasure (Fin 2 → ℝ)) {g : ℝ → ℝ}
    (hg : StrictMono g) (h : ∀ᵐ x ∂μ.toMeasure, x 1 = g (x 0)) (y : ℝ) :
    ProbabilityTheory.cdf (marginal μ 1) (g y) = ProbabilityTheory.cdf (marginal μ 0) y := by
  have hgm : Measurable g := hg.monotone.measurable
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real,
    marginal_one_eq_map_of_ae_eq μ hgm h, map_measureReal_apply hgm measurableSet_Iic]
  have he : g ⁻¹' Iic (g y) = Iic y := by
    ext z
    simp only [mem_preimage, mem_Iic]
    exact hg.le_iff_le
  rw [he]

theorem cdf_marginal_one_of_ae_eq_strictAnti (μ : ProbabilityMeasure (Fin 2 → ℝ)) {g : ℝ → ℝ}
    (hg : StrictAnti g) (hc : Continuous (ProbabilityTheory.cdf (marginal μ 0)))
    (h : ∀ᵐ x ∂μ.toMeasure, x 1 = g (x 0)) (y : ℝ) :
    ProbabilityTheory.cdf (marginal μ 1) (g y) = 1 - ProbabilityTheory.cdf (marginal μ 0) y := by
  have hgm : Measurable g := hg.antitone.measurable
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real,
    marginal_one_eq_map_of_ae_eq μ hgm h, map_measureReal_apply hgm measurableSet_Iic]
  have he : g ⁻¹' Iic (g y) = Ici y := by
    ext z
    simp only [mem_preimage, mem_Iic]
    exact hg.le_iff_ge
  rw [he]
  exact real_Ici_eq_one_sub _ (measure_singleton_eq_zero_of_continuous_cdf _ hc y)

/-- **Nelsen, Theorem 2.5.4 (sufficiency, increasing case).** If the second coordinate is almost
surely a strictly increasing function of the first, the Sklar copula is `M`. -/
theorem eq_comonotonic_of_ae_eq_strictMono (μ : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {g : ℝ → ℝ}
    (hg : StrictMono g) (h : ∀ᵐ x ∂μ.toMeasure, x 1 = g (x 0)) :
    ofContinuousMarginals μ hc = comonotonic 2 := by
  rw [ofContinuousMarginals_eq_comonotonic_iff]
  filter_upwards [h] with x hx
  apply Subtype.ext
  change ProbabilityTheory.cdf (marginal μ 0) (x 0) = ProbabilityTheory.cdf (marginal μ 1) (x 1)
  rw [hx, cdf_marginal_one_of_ae_eq_strictMono μ hg h]

/-- **Nelsen, Theorem 2.5.4 (sufficiency, decreasing case).** If the second coordinate is almost
surely a strictly decreasing function of the first, the Sklar copula is `W`. -/
theorem eq_countermonotonic_of_ae_eq_strictAnti (μ : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {g : ℝ → ℝ}
    (hg : StrictAnti g) (h : ∀ᵐ x ∂μ.toMeasure, x 1 = g (x 0)) :
    ofContinuousMarginals μ hc = countermonotonic := by
  rw [ofContinuousMarginals_eq_countermonotonic_iff]
  filter_upwards [h] with x hx
  apply Subtype.ext
  change ProbabilityTheory.cdf (marginal μ 1) (x 1) =
    ((unitInterval.symm (cdfUnit (marginal μ 0) (x 0)) : I) : ℝ)
  rw [unitInterval.coe_symm_eq, coe_cdfUnit, hx,
    cdf_marginal_one_of_ae_eq_strictAnti μ hg (hc 0) h]

/-- Any Sklar copula of a law with continuous marginals whose second coordinate is almost surely
a strictly increasing function of the first is `M`. -/
theorem eq_comonotonic_of_isSklarCopula_of_ae_eq_strictMono {μ : ProbabilityMeasure (Fin 2 → ℝ)}
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {C : Copula 2}
    (hC : IsSklarCopula μ C) {g : ℝ → ℝ} (hg : StrictMono g)
    (h : ∀ᵐ x ∂μ.toMeasure, x 1 = g (x 0)) : C = comonotonic 2 :=
  (hC.unique hc (isSklarCopula_ofContinuousMarginals μ hc)).trans
    (eq_comonotonic_of_ae_eq_strictMono μ hc hg h)

/-- Any Sklar copula of a law with continuous marginals whose second coordinate is almost surely
a strictly decreasing function of the first is `W`. -/
theorem eq_countermonotonic_of_isSklarCopula_of_ae_eq_strictAnti {μ : ProbabilityMeasure (Fin 2 → ℝ)}
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {C : Copula 2}
    (hC : IsSklarCopula μ C) {g : ℝ → ℝ} (hg : StrictAnti g)
    (h : ∀ᵐ x ∂μ.toMeasure, x 1 = g (x 0)) : C = countermonotonic :=
  (hC.unique hc (isSklarCopula_ofContinuousMarginals μ hc)).trans
    (eq_countermonotonic_of_ae_eq_strictAnti μ hc hg h)

end ProbabilityTheory.Copula
