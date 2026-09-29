/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.KendallTauFamilies
import Copula.KendallDistribution

/-! # Kendall distribution functions of Archimedean copulas

Restatement of Nelsen, *An Introduction to Copulas*, second edition, Theorem 4.3.4 for the
library's Kendall distribution function `Copula.kendallCDF` (`K_C(t) = P(C(U) ≤ t)`):
for a generator with continuously differentiable inverse generator,
`K_C(t) = t − φ(t) ψ'(φ(t)) = t − φ(t)/φ'(t)` on `(0, 1]`
(`BivariateGenerator.IsC1.kendallCDF_eq`, `BivariateGenerator.IsC1.kendallCDF_eq_deriv`).

At zero:
* `K_C(0) = 0` for every strict generator (`BivariateGenerator.IsStrict.kendallCDF_zero`): the zero
  set of `C` is the boundary `{u = 0} ∪ {v = 0}`, a null set;
* Nelsen, Theorem 4.3.3: the mass of the zero set `{C = 0}` is
  `K_C(0) = −lim_{t → 0+} φ(t)/φ'(t) = −φ(0)/φ'(0⁺)` (`BivariateGenerator.IsC1.kendallCDF_zero`,
  `BivariateGenerator.IsC1.measureReal_cdf_eq_zero`), by right continuity of `K_C`;
* instances: `W` puts all its mass on the zero set (`kendallCDF_zero_countermonotonic`), and
  Nelsen's family 4.2.2 puts mass `1/θ` there (`kendallCDF_zero_nelsen2`).
-/

open MeasureTheory Set Filter
open scoped Topology
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace BivariateGenerator

/-- Nelsen, Theorem 4.3.4, for `Copula.kendallCDF`. -/
theorem IsC1.kendallCDF_eq {g : BivariateGenerator} {ψ' : ℝ → ℝ} (h : g.IsC1 ψ')
    {t : I} (ht : t ≠ 0) :
    g.copula.kendallCDF t = t - g.invFun t * ψ' (g.invFun t) := by
  rw [ProbabilityTheory.Copula.kendallCDF_eq]
  exact h.measureReal_cdf_le ht

/-- Nelsen, Theorem 4.3.4 in the form `K_C(t) = t − φ(t)/φ'(t)`, `0 < t < 1`. -/
theorem IsC1.kendallCDF_eq_deriv {g : BivariateGenerator} {ψ' : ℝ → ℝ}
    (h : g.IsC1 ψ') {t : I} (ht : t ≠ 0) (ht1 : t ≠ 1) :
    g.copula.kendallCDF t = t - g.invFun t / deriv g.invFunReal t := by
  rw [ProbabilityTheory.Copula.kendallCDF_eq]
  exact h.measureReal_cdf_le_deriv ht ht1

/-- For a strict generator the Kendall distribution has no atom at zero. -/
theorem IsStrict.kendallCDF_zero {g : BivariateGenerator} (hg : g.IsStrict) :
    g.copula.kendallCDF 0 = 0 := by
  rw [ProbabilityTheory.Copula.kendallCDF_eq]
  have hnull (i : Fin 2) : g.copula.toMeasure {x : Fin 2 → I | x i = 0} = 0 := by
    have h := Measure.map_apply (μ := g.copula.toMeasure) (measurable_pi_apply i)
      (measurableSet_singleton (0 : I))
    rw [g.copula.map_eval i] at h
    rw [show {x : Fin 2 → I | x i = 0} = (fun x => x i) ⁻¹' {0} from rfl, ← h]
    exact measure_singleton 0
  have hsub : {x | g.copula.cdf x ≤ 0} ⊆ {x : Fin 2 → I | x 0 = 0} ∪ {x | x 1 = 0} := by
    intro x hx
    by_contra hn
    simp only [mem_union, mem_ofPred_eq, not_or] at hn
    have hpos := hg.cdf_pos hn.1 hn.2
    rw [← cdf_copula] at hpos
    exact absurd hx (not_le.mpr hpos)
  have h0 : g.copula.toMeasure {x | g.copula.cdf x ≤ 0} = 0 :=
    measure_mono_null hsub (measure_union_null (hnull 0) (hnull 1))
  rw [Measure.real, h0, ENNReal.toReal_zero]

/-- Nelsen, Theorem 4.3.3: for a `C¹` generator, `K_C(0) = −lim_{t → 0+} φ(t) ψ'(φ(t))`,
i.e. `−φ(0)/φ'(0⁺)`, whenever this limit exists. -/
theorem IsC1.kendallCDF_zero {g : BivariateGenerator} {ψ' : ℝ → ℝ} (h : g.IsC1 ψ') {m : ℝ}
    (hm : Tendsto (fun t => g.invFunReal t * ψ' (g.invFunReal t)) (𝓝[>] 0) (𝓝 m)) :
    g.copula.kendallCDF 0 = -m := by
  have hK : Tendsto g.copula.kendallCDF (𝓝[>] 0) (𝓝 (g.copula.kendallCDF 0)) :=
    (right_continuous_kendallCDF _ 0).mono Ioi_subset_Ici_self
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hK' : Tendsto g.copula.kendallCDF (𝓝[>] 0) (𝓝 (0 - m)) := by
    refine (hid.sub hm).congr' ?_
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    let u : I := ⟨t, ht.1.le, ht.2⟩
    have hu : u ≠ 0 := fun e => ht.1.ne' (congrArg Subtype.val e)
    have hφ : g.invFunReal t = g.invFun u := g.invFunReal_coe u
    have hk := h.kendallCDF_eq hu
    change g.copula.kendallCDF t = t - g.invFun u * ψ' (g.invFun u) at hk
    rw [hk, hφ]
  rw [tendsto_nhds_unique hK hK', zero_sub]

/-- Nelsen, Theorem 4.3.3: the `C`-measure of the zero set `{C = 0}` is
`−lim_{t → 0+} φ(t) ψ'(φ(t)) = −φ(0)/φ'(0⁺)`. -/
theorem IsC1.measureReal_cdf_eq_zero {g : BivariateGenerator} {ψ' : ℝ → ℝ} (h : g.IsC1 ψ')
    {m : ℝ} (hm : Tendsto (fun t => g.invFunReal t * ψ' (g.invFunReal t)) (𝓝[>] 0) (𝓝 m)) :
    g.copula.toMeasure.real {x | g.copula.cdf x = 0} = -m := by
  have he : {x | g.copula.cdf x = 0} = {x | g.copula.cdf x ≤ 0} := by
    ext x
    simp only [mem_ofPred_eq]
    exact ⟨fun hx => hx.le, fun hx => le_antisymm hx (g.copula.cdf_nonneg x)⟩
  rw [he, ← ProbabilityTheory.Copula.kendallCDF_eq]
  exact h.kendallCDF_zero hm

end BivariateGenerator

/-- The Kendall integrand of the generator of `W` is `−(1 − t)` on `(0, 1]`. -/
private theorem truncated_integrand {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    truncatedLinearGenerator.invFunReal t * (fun _ : ℝ => (-1 : ℝ))
      (truncatedLinearGenerator.invFunReal t) = -(1 - t) := by
  have hφ : truncatedLinearGenerator.invFunReal t = 1 - t :=
    truncatedLinearGenerator.invFunReal_coe ⟨t, ht.1.le, ht.2⟩
  rw [hφ]
  ring

private theorem tendsto_neg_one_sub :
    Tendsto (fun t : ℝ => -(1 - t)) (𝓝[>] 0) (𝓝 (-1)) := by
  have h : Tendsto (fun t : ℝ => -(1 - t)) (𝓝 0) (𝓝 (-(1 - 0))) :=
    ((continuous_const.sub continuous_id).neg).tendsto 0
  rw [sub_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- The lower Fréchet bound `W` concentrates on its zero set: `K_W(0) = 1`. -/
theorem kendallCDF_zero_countermonotonic : countermonotonic.kendallCDF 0 = 1 := by
  rw [← truncatedLinearGenerator_copula, isC1_truncatedLinearGenerator.kendallCDF_zero (m := -1),
    neg_neg]
  refine tendsto_neg_one_sub.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  exact (truncated_integrand ht).symm

/-- Nelsen's family 4.2.2 puts mass `1/θ` on its zero set. -/
theorem kendallCDF_zero_nelsen2 (θ : ℝ) (hθ : 1 ≤ θ) : (nelsen2 θ hθ).kendallCDF 0 = 1 / θ := by
  have h := isC1_truncatedLinearGenerator.outerPower θ hθ
  rw [nelsen2, h.kendallCDF_zero (m := θ⁻¹ * -1), mul_neg_one, neg_neg, one_div]
  refine (tendsto_neg_one_sub.const_mul θ⁻¹).congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  have h1 := BivariateGenerator.outerPower_integrand truncatedLinearGenerator (fun _ => (-1 : ℝ))
    θ hθ ht
  have h2 := truncated_integrand ht
  beta_reduce at h1 h2
  rw [h1, h2]

end ProbabilityTheory.Copula
