/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.RandomVariable.Invariance
import Copula.Support
import Copula.Distribution.RealQuantile

/-!
# Monotone functional dependence and the Fréchet bounds

Nelsen, *An Introduction to Copulas*, second edition, Theorem 2.5.4 and Corollary 2.5.5
(random-variable version, for laws on `Fin 2 → ℝ` with continuous marginal CDFs).

For such a law `μ`, the Sklar copula is the law of `(F₀ x₀, F₁ x₁)`. It equals the comonotonic copula
`M` exactly when `F₀ x₀ = F₁ x₁` almost surely, and the countermonotonic copula `W` exactly when
`F₁ x₁ = 1 - F₀ x₀` almost surely. If the second coordinate is almost surely a strictly increasing
(respectively decreasing) function of the first, these almost-sure identities hold, so the copula
is `M` (respectively `W`).

The converse implication is proved as well, which gives the full Theorem 2.5.4: the copula is
`M` if and only if `x₁ = f x₀` almost surely for a function `f` that is monotone on a set carrying
the law of `x₀` (`ofContinuousMarginals_eq_comonotonic_iff_exists_monotoneOn`), and `W` if and
only if the same holds with an antitone `f`
(`ofContinuousMarginals_eq_countermonotonic_iff_exists_antitoneOn`). The function is explicit:
`f = G₁ ∘ F₀` (respectively `f = G₁ ∘ (1 - F₀)`), with `G₁ = realQuantile` the quantile of the
second marginal, and the carrier set is `{x | 0 < F₀ x < 1}`.

Monotonicity cannot in general be required on all of `ℝ`: if `x₀` is uniform on `[0,1]` and
`x₁ = Φ⁻¹(x₀)` is standard normal, then the copula is `M`, but a monotone `f : ℝ → ℝ` with
`x₁ = f x₀` almost surely would have to be `-∞` on `(-∞, 0)`. Nor can strict monotonicity be
required, since `F₀` is constant on gaps in the support of `x₀`. For globally monotone `f` the
sufficiency direction is `eq_comonotonic_of_ae_eq_monotone`.
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

/-! ### Monotone functions on a carrier set: the full Theorem 2.5.4 -/

/-- A coordinate of a law with continuous marginal CDF takes each fixed value with probability
zero. -/
theorem measure_coord_eq_eq_zero (μ : ProbabilityMeasure (Fin 2 → ℝ)) {i : Fin 2}
    (hc : Continuous (ProbabilityTheory.cdf (marginal μ i))) (c : ℝ) :
    μ.toMeasure {z | z i = c} = 0 := by
  have h := measure_singleton_eq_zero_of_continuous_cdf (marginal μ i) hc c
  rwa [marginal, Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton c)] at h

theorem measureReal_coord_mem (μ : ProbabilityMeasure (Fin 2 → ℝ)) (i : Fin 2) {s : Set ℝ}
    (hs : MeasurableSet s) : μ.toMeasure.real {z | z i ∈ s} = (marginal μ i).real s :=
  (map_measureReal_apply (measurable_pi_apply i) hs).symm

/-- If `x₁ = f x₀` almost surely with `f` monotone on a set carrying `x₀`, the marginal CDFs are
linked by `F₁ (f y) = F₀ y` on that set. -/
theorem cdf_marginal_one_of_ae_eq_monotoneOn (μ : ProbabilityMeasure (Fin 2 → ℝ))
    (hc1 : Continuous (ProbabilityTheory.cdf (marginal μ 1))) {f : ℝ → ℝ} {S : Set ℝ}
    (hf : MonotoneOn f S) (h : ∀ᵐ x ∂μ.toMeasure, x 0 ∈ S ∧ x 1 = f (x 0)) {y : ℝ}
    (hy : y ∈ S) :
    ProbabilityTheory.cdf (marginal μ 1) (f y) = ProbabilityTheory.cdf (marginal μ 0) y := by
  have hge : μ.toMeasure {z | z 0 ≤ y} ≤ μ.toMeasure {z | z 1 ≤ f y} := by
    apply measure_mono_ae
    filter_upwards [h] with z hz
    intro hzy
    change z 0 ≤ y at hzy
    rw [hz.2]
    exact hf hz.1 hy hzy
  have hle : μ.toMeasure {z | z 1 ≤ f y} ≤ μ.toMeasure {z | z 0 ≤ y} := by
    calc
      μ.toMeasure {z | z 1 ≤ f y} ≤ μ.toMeasure ({z | z 0 ≤ y} ∪ {z | z 1 = f y}) := by
        apply measure_mono_ae
        filter_upwards [h] with z hz
        intro hzle
        change z 1 ≤ f y at hzle
        rcases le_or_gt (z 0) y with h0 | h0
        · exact Or.inl h0
        · right
          change z 1 = f y
          exact le_antisymm hzle (hz.2 ▸ hf hy hz.1 h0.le)
      _ ≤ μ.toMeasure {z | z 0 ≤ y} + μ.toMeasure {z | z 1 = f y} := measure_union_le _ _
      _ = μ.toMeasure {z | z 0 ≤ y} := by rw [measure_coord_eq_eq_zero μ hc1, add_zero]
  have he := congrArg ENNReal.toReal (le_antisymm hle hge)
  change μ.toMeasure.real {z | z 1 ∈ Iic (f y)} = μ.toMeasure.real {z | z 0 ∈ Iic y} at he
  rw [measureReal_coord_mem μ 1 measurableSet_Iic, measureReal_coord_mem μ 0 measurableSet_Iic,
    ← ProbabilityTheory.cdf_eq_real, ← ProbabilityTheory.cdf_eq_real] at he
  exact he

/-- If `x₁ = f x₀` almost surely with `f` antitone on a set carrying `x₀`, the marginal CDFs are
linked by `F₁ (f y) = 1 - F₀ y` on that set. -/
theorem cdf_marginal_one_of_ae_eq_antitoneOn (μ : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {f : ℝ → ℝ} {S : Set ℝ}
    (hf : AntitoneOn f S) (h : ∀ᵐ x ∂μ.toMeasure, x 0 ∈ S ∧ x 1 = f (x 0)) {y : ℝ}
    (hy : y ∈ S) :
    ProbabilityTheory.cdf (marginal μ 1) (f y) = 1 - ProbabilityTheory.cdf (marginal μ 0) y := by
  have hge : μ.toMeasure {z | y ≤ z 0} ≤ μ.toMeasure {z | z 1 ≤ f y} := by
    apply measure_mono_ae
    filter_upwards [h] with z hz
    intro hzy
    change y ≤ z 0 at hzy
    rw [hz.2]
    exact hf hy hz.1 hzy
  have hle : μ.toMeasure {z | z 1 ≤ f y} ≤ μ.toMeasure {z | y ≤ z 0} := by
    calc
      μ.toMeasure {z | z 1 ≤ f y} ≤ μ.toMeasure ({z | y ≤ z 0} ∪ {z | z 1 = f y}) := by
        apply measure_mono_ae
        filter_upwards [h] with z hz
        intro hzle
        change z 1 ≤ f y at hzle
        rcases le_or_gt y (z 0) with h0 | h0
        · exact Or.inl h0
        · right
          change z 1 = f y
          exact le_antisymm hzle (hz.2 ▸ hf hz.1 hy h0.le)
      _ ≤ μ.toMeasure {z | y ≤ z 0} + μ.toMeasure {z | z 1 = f y} := measure_union_le _ _
      _ = μ.toMeasure {z | y ≤ z 0} := by rw [measure_coord_eq_eq_zero μ (hc 1), add_zero]
  have he := congrArg ENNReal.toReal (le_antisymm hle hge)
  change μ.toMeasure.real {z | z 1 ∈ Iic (f y)} = μ.toMeasure.real {z | z 0 ∈ Ici y} at he
  rw [measureReal_coord_mem μ 1 measurableSet_Iic, measureReal_coord_mem μ 0 measurableSet_Ici,
    ← ProbabilityTheory.cdf_eq_real,
    real_Ici_eq_one_sub _ (measure_singleton_eq_zero_of_continuous_cdf _ (hc 0) y),
    ← ProbabilityTheory.cdf_eq_real] at he
  exact he

/-- **Nelsen, Theorem 2.5.4 (sufficiency, increasing case, general form).** If the second
coordinate is almost surely `f` of the first, with `f` nondecreasing on a set carrying the first
coordinate, the Sklar copula is `M`. -/
theorem eq_comonotonic_of_ae_eq_monotoneOn (μ : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {f : ℝ → ℝ} {S : Set ℝ}
    (hf : MonotoneOn f S) (h : ∀ᵐ x ∂μ.toMeasure, x 0 ∈ S ∧ x 1 = f (x 0)) :
    ofContinuousMarginals μ hc = comonotonic 2 := by
  rw [ofContinuousMarginals_eq_comonotonic_iff]
  filter_upwards [h] with x hx
  apply Subtype.ext
  change ProbabilityTheory.cdf (marginal μ 0) (x 0) = ProbabilityTheory.cdf (marginal μ 1) (x 1)
  rw [hx.2, cdf_marginal_one_of_ae_eq_monotoneOn μ (hc 1) hf h hx.1]

/-- **Nelsen, Theorem 2.5.4 (sufficiency, decreasing case, general form).** If the second
coordinate is almost surely `f` of the first, with `f` nonincreasing on a set carrying the first
coordinate, the Sklar copula is `W`. -/
theorem eq_countermonotonic_of_ae_eq_antitoneOn (μ : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {f : ℝ → ℝ} {S : Set ℝ}
    (hf : AntitoneOn f S) (h : ∀ᵐ x ∂μ.toMeasure, x 0 ∈ S ∧ x 1 = f (x 0)) :
    ofContinuousMarginals μ hc = countermonotonic := by
  rw [ofContinuousMarginals_eq_countermonotonic_iff]
  filter_upwards [h] with x hx
  apply Subtype.ext
  change ProbabilityTheory.cdf (marginal μ 1) (x 1) =
    ((unitInterval.symm (cdfUnit (marginal μ 0) (x 0)) : I) : ℝ)
  rw [unitInterval.coe_symm_eq, coe_cdfUnit, hx.2,
    cdf_marginal_one_of_ae_eq_antitoneOn μ hc hf h hx.1]

/-- Sufficiency with a globally nondecreasing function. -/
theorem eq_comonotonic_of_ae_eq_monotone (μ : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {f : ℝ → ℝ}
    (hf : Monotone f) (h : ∀ᵐ x ∂μ.toMeasure, x 1 = f (x 0)) :
    ofContinuousMarginals μ hc = comonotonic 2 :=
  eq_comonotonic_of_ae_eq_monotoneOn μ hc (hf.monotoneOn univ)
    (h.mono fun _ hx => ⟨mem_univ _, hx⟩)

/-- Sufficiency with a globally nonincreasing function. -/
theorem eq_countermonotonic_of_ae_eq_antitone (μ : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {f : ℝ → ℝ}
    (hf : Antitone f) (h : ∀ᵐ x ∂μ.toMeasure, x 1 = f (x 0)) :
    ofContinuousMarginals μ hc = countermonotonic :=
  eq_countermonotonic_of_ae_eq_antitoneOn μ hc (hf.antitoneOn univ)
    (h.mono fun _ hx => ⟨mem_univ _, hx⟩)

/-- Almost surely the first probability integral transform lies strictly inside `(0, 1)`. -/
theorem ae_cdf_marginal_mem_Ioo (μ : ProbabilityMeasure (Fin 2 → ℝ)) {i : Fin 2}
    (hc : Continuous (ProbabilityTheory.cdf (marginal μ i))) :
    ∀ᵐ x ∂μ.toMeasure, ProbabilityTheory.cdf (marginal μ i) (x i) ∈ Ioo 0 1 :=
  ae_of_ae_map (measurable_pi_apply i).aemeasurable (ae_cdf_mem_Ioo (marginal μ i) hc)

/-- Almost surely the quantile of the second marginal inverts its CDF. -/
theorem ae_realQuantile_cdf_marginal (μ : ProbabilityMeasure (Fin 2 → ℝ)) {i : Fin 2}
    (hc : Continuous (ProbabilityTheory.cdf (marginal μ i))) :
    ∀ᵐ x ∂μ.toMeasure,
      realQuantile (marginal μ i) (ProbabilityTheory.cdf (marginal μ i) (x i)) = x i :=
  ae_of_ae_map (measurable_pi_apply i).aemeasurable (ae_realQuantile_cdf (marginal μ i) hc)

/-- **Nelsen, Theorem 2.5.4 (necessity, increasing case).** If the Sklar copula is `M`, then
`x₁ = G₁ (F₀ x₀)` almost surely, where `G₁` is the quantile of the second marginal. -/
theorem ae_eq_realQuantile_of_eq_comonotonic (μ : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i)))
    (h : ofContinuousMarginals μ hc = comonotonic 2) :
    ∀ᵐ x ∂μ.toMeasure,
      x 1 = realQuantile (marginal μ 1) (ProbabilityTheory.cdf (marginal μ 0) (x 0)) := by
  filter_upwards [(ofContinuousMarginals_eq_comonotonic_iff μ hc).mp h,
    ae_realQuantile_cdf_marginal μ (hc 1)] with x hx hq
  have he : ProbabilityTheory.cdf (marginal μ 0) (x 0) =
      ProbabilityTheory.cdf (marginal μ 1) (x 1) := congrArg Subtype.val hx
  rw [he, hq]

/-- **Nelsen, Theorem 2.5.4 (necessity, decreasing case).** If the Sklar copula is `W`, then
`x₁ = G₁ (1 - F₀ x₀)` almost surely, where `G₁` is the quantile of the second marginal. -/
theorem ae_eq_realQuantile_of_eq_countermonotonic (μ : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i)))
    (h : ofContinuousMarginals μ hc = countermonotonic) :
    ∀ᵐ x ∂μ.toMeasure,
      x 1 = realQuantile (marginal μ 1) (1 - ProbabilityTheory.cdf (marginal μ 0) (x 0)) := by
  filter_upwards [(ofContinuousMarginals_eq_countermonotonic_iff μ hc).mp h,
    ae_realQuantile_cdf_marginal μ (hc 1)] with x hx hq
  have he : ProbabilityTheory.cdf (marginal μ 1) (x 1) =
      1 - ProbabilityTheory.cdf (marginal μ 0) (x 0) := by
    have := congrArg Subtype.val hx
    rwa [unitInterval.coe_symm_eq] at this
  rw [← he, hq]

/-- **Nelsen, Theorem 2.5.4 (increasing case).** For a law with continuous marginals, the Sklar
copula is `M` if and only if the second coordinate is almost surely a nondecreasing function of
the first, where the function need only be nondecreasing on a set carrying the first
coordinate. -/
theorem ofContinuousMarginals_eq_comonotonic_iff_exists_monotoneOn
    (μ : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) :
    ofContinuousMarginals μ hc = comonotonic 2 ↔
      ∃ (f : ℝ → ℝ) (S : Set ℝ), MonotoneOn f S ∧
        ∀ᵐ x ∂μ.toMeasure, x 0 ∈ S ∧ x 1 = f (x 0) := by
  refine ⟨fun h => ?_, fun ⟨f, S, hf, h⟩ => eq_comonotonic_of_ae_eq_monotoneOn μ hc hf h⟩
  refine ⟨fun y => realQuantile (marginal μ 1) (ProbabilityTheory.cdf (marginal μ 0) y),
    ProbabilityTheory.cdf (marginal μ 0) ⁻¹' Ioo 0 1, ?_, ?_⟩
  · intro y hy z hz hyz
    exact monotoneOn_realQuantile _ hy hz (ProbabilityTheory.monotone_cdf _ hyz)
  · filter_upwards [ae_cdf_marginal_mem_Ioo μ (hc 0),
      ae_eq_realQuantile_of_eq_comonotonic μ hc h] with x h0 h1
    exact ⟨h0, h1⟩

/-- **Nelsen, Theorem 2.5.4 (decreasing case).** For a law with continuous marginals, the Sklar
copula is `W` if and only if the second coordinate is almost surely a nonincreasing function of
the first, where the function need only be nonincreasing on a set carrying the first
coordinate. -/
theorem ofContinuousMarginals_eq_countermonotonic_iff_exists_antitoneOn
    (μ : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) :
    ofContinuousMarginals μ hc = countermonotonic ↔
      ∃ (f : ℝ → ℝ) (S : Set ℝ), AntitoneOn f S ∧
        ∀ᵐ x ∂μ.toMeasure, x 0 ∈ S ∧ x 1 = f (x 0) := by
  refine ⟨fun h => ?_, fun ⟨f, S, hf, h⟩ => eq_countermonotonic_of_ae_eq_antitoneOn μ hc hf h⟩
  refine ⟨fun y => realQuantile (marginal μ 1) (1 - ProbabilityTheory.cdf (marginal μ 0) y),
    ProbabilityTheory.cdf (marginal μ 0) ⁻¹' Ioo 0 1, ?_, ?_⟩
  · intro y hy z hz hyz
    have hy' : 1 - ProbabilityTheory.cdf (marginal μ 0) y ∈ Ioo (0 : ℝ) 1 :=
      ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hz' : 1 - ProbabilityTheory.cdf (marginal μ 0) z ∈ Ioo (0 : ℝ) 1 :=
      ⟨by linarith [hz.2], by linarith [hz.1]⟩
    exact monotoneOn_realQuantile _ hz' hy'
      (by linarith [ProbabilityTheory.monotone_cdf (marginal μ 0) hyz])
  · filter_upwards [ae_cdf_marginal_mem_Ioo μ (hc 0),
      ae_eq_realQuantile_of_eq_countermonotonic μ hc h] with x h0 h1
    exact ⟨h0, h1⟩

/-- Theorem 2.5.4 for an arbitrary Sklar copula of a law with continuous marginals
(increasing case). -/
theorem IsSklarCopula.eq_comonotonic_iff_exists_monotoneOn {μ : ProbabilityMeasure (Fin 2 → ℝ)}
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {C : Copula 2}
    (hC : IsSklarCopula μ C) :
    C = comonotonic 2 ↔ ∃ (f : ℝ → ℝ) (S : Set ℝ), MonotoneOn f S ∧
      ∀ᵐ x ∂μ.toMeasure, x 0 ∈ S ∧ x 1 = f (x 0) := by
  rw [hC.unique hc (isSklarCopula_ofContinuousMarginals μ hc)]
  exact ofContinuousMarginals_eq_comonotonic_iff_exists_monotoneOn μ hc

/-- Theorem 2.5.4 for an arbitrary Sklar copula of a law with continuous marginals
(decreasing case). -/
theorem IsSklarCopula.eq_countermonotonic_iff_exists_antitoneOn
    {μ : ProbabilityMeasure (Fin 2 → ℝ)}
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) {C : Copula 2}
    (hC : IsSklarCopula μ C) :
    C = countermonotonic ↔ ∃ (f : ℝ → ℝ) (S : Set ℝ), AntitoneOn f S ∧
      ∀ᵐ x ∂μ.toMeasure, x 0 ∈ S ∧ x 1 = f (x 0) := by
  rw [hC.unique hc (isSklarCopula_ofContinuousMarginals μ hc)]
  exact ofContinuousMarginals_eq_countermonotonic_iff_exists_antitoneOn μ hc

end ProbabilityTheory.Copula
