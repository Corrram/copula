/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Derivative
import Copula.Archimedean.TailDependence

/-! # The Kendall distribution function of an Archimedean copula

Nelsen, *An Introduction to Copulas*, second edition, Theorem 4.3.4: for an Archimedean
copula with generator `φ`, the distribution function of `C(U, V)`, where `(U, V)` has
law `C`, is
`K_C(t) = P(C(U, V) ≤ t) = t − φ(t) / φ'(t⁺)`, `0 < t ≤ 1`.

We prove this for generators whose inverse generator `ψ = φ⁻¹` has a continuous derivative `ψ'`
where it is positive (`BivariateGenerator.IsC1`), strict or not. Since
`φ'(t) = 1 / ψ'(φ(t))`, the formula reads `K_C(t) = t − φ(t) ψ'(φ(t))`
(`BivariateGenerator.IsC1.measureReal_cdf_le`), and in Nelsen's form with the
derivative of the generator (`BivariateGenerator.IsC1.measureReal_cdf_le_deriv`).

The proof disintegrates the copula measure along the first coordinate: for `u > t` the event
`C(u, V) ≤ t` is `V ≤ L_t(u)` with the level curve `L_t(u) = ψ(φ(t) − φ(u))`, whose conditional
probability is `∂₁C(u, L_t(u)) = ψ'(φ(t)) / ψ'(φ(u)) = φ'(u) / φ'(t)`; for `u ≤ t` it is one.
Integrating gives `t + (φ(1) − φ(t)) / φ'(t)`.

For a non-strict generator `K_C` has an atom at `0`, the mass of the zero curve
`φ(u) + φ(v) = φ(0)`; its value `−φ(0) / φ'(0⁺)` (Nelsen, Theorem 4.3.3) is derived from the
formula above in `Copula.Archimedean.KendallCDF`.
-/

open MeasureTheory Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

/-- Disintegration of a bivariate copula measure along the first coordinate. -/
theorem measure_pair_preimage_eq_lintegral (C : Copula 2) {s : Set (I × I)}
    (hs : MeasurableSet s) :
    C.toMeasure ((fun x : Fin 2 → I => (x 0, x 1)) ⁻¹' s) =
      ∫⁻ u, C.conditionalKernel u (Prod.mk u ⁻¹' s) := by
  have hm := compProd_map_condDistrib (μ := C.toMeasure) (mα := inferInstance)
    (mβ := inferInstance) (X := fun x : Fin 2 → I => x 0) (Y := fun x => x 1)
    (measurable_pi_apply 0).aemeasurable (measurable_pi_apply 1).aemeasurable
  rw [C.map_eval] at hm
  change (volume : Measure I) ⊗ₘ C.conditionalKernel = _ at hm
  rw [← Measure.map_apply (by fun_prop) hs, ← hm, Measure.compProd_apply hs]

namespace BivariateGenerator

/-- `ψ(s) ≤ t` iff `φ(t) ≤ s`, for `t > 0` and `s ≥ 0`. -/
theorem toFun_le_iff (g : BivariateGenerator) {t : I} (ht : t ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    g.toFun s ≤ t ↔ g.invFun t ≤ s := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hpos : 0 < g.toFun (g.invFun t) := by rw [g.right_inv t ht]; exact coe_pos ht
    have h2 := g.toFun_lt_of_lt hs hlt hpos
    rw [g.right_inv t ht] at h2
    linarith
  · intro h
    calc g.toFun s ≤ g.toFun (g.invFun t) := g.antitone_nonneg (g.inv_nonneg t ht) hs h
      _ = t := g.right_inv t ht

/-- The sections of `{C ≤ t}` beyond `t` are lower intervals bounded by the level curve. -/
theorem cdf_le_iff_le_toI (g : BivariateGenerator) {t u : I} (ht : t ≠ 0)
    (htu : t < u) (v : I) :
    g.cdf u v ≤ t ↔ v ≤ g.toI (sub_nonneg.mpr (g.inv_antitone t u ht htu.le)) := by
  have hu : u ≠ 0 := (unitInterval.nonneg'.trans_lt htu).ne'
  have hc : 0 ≤ g.invFun t - g.invFun u := sub_nonneg.mpr (g.inv_antitone t u ht htu.le)
  by_cases hv : v = 0
  · subst hv
    simp only [cdf_zero_right]
    exact ⟨fun _ => unitInterval.nonneg', fun _ => t.property.1⟩
  rw [cdf, ite_or_of_not hu hv,
    g.toFun_le_iff ht (add_nonneg (g.inv_nonneg u hu) (g.inv_nonneg v hv))]
  have hpos : 0 < g.toFun (g.invFun t - g.invFun u) := by
    have := g.antitone_nonneg hc (g.inv_nonneg t ht) (sub_le_self _ (g.inv_nonneg u hu))
    rw [g.right_inv t ht] at this
    exact (coe_pos ht).trans_le this
  constructor
  · intro h
    change (v : ℝ) ≤ g.toFun (g.invFun t - g.invFun u)
    calc (v : ℝ) = g.toFun (g.invFun v) := (g.right_inv v hv).symm
      _ ≤ g.toFun (g.invFun t - g.invFun u) :=
        g.antitone_nonneg hc (g.inv_nonneg v hv) (by linarith)
  · intro h
    have h2 := g.inv_antitone v (g.toI hc) hv h
    rw [g.invFun_toI hc hpos] at h2
    linarith

namespace IsC1

variable {g : BivariateGenerator} {ψ' : ℝ → ℝ}

private theorem sections_measurableSet (g : BivariateGenerator) (t : ℝ) :
    MeasurableSet {p : I × I | g.cdf p.1 p.2 ≤ t} := by
  have hc : Continuous (fun p : I × I => g.copula.cdf ![p.1, p.2]) :=
    g.copula.continuous_cdf.comp (by fun_prop)
  have he : {p : I × I | g.cdf p.1 p.2 ≤ t} = {p : I × I | g.copula.cdf ![p.1, p.2] ≤ t} := by
    ext p
    simp only [mem_ofPred_eq, cdf_copula, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [he]
  exact (isClosed_le hc continuous_const).measurableSet

/-- The conditional probability of `{C(u, V) ≤ t}` given `U = u`, as an explicit function. -/
private noncomputable def kendallIntegrand (g : BivariateGenerator) (ψ' : ℝ → ℝ) (t : I)
    (x : ℝ) : ℝ :=
  if x ≤ t then 1 else ψ' (g.invFun t) * (ψ' (g.invFunReal x))⁻¹

private theorem ae_section_eq (h : g.IsC1 ψ') {t : I} (ht : t ≠ 0) :
    ∀ᵐ u : I, (g.copula.conditionalKernel u
      (Prod.mk u ⁻¹' {p : I × I | g.cdf p.1 p.2 ≤ t})).toReal = kendallIntegrand g ψ' t u := by
  filter_upwards [h.ae_conditionalCDF_eq] with u ⟨hu0, _, hcond⟩
  have hpre : Prod.mk u ⁻¹' {p : I × I | g.cdf p.1 p.2 ≤ t} = {v : I | g.cdf u v ≤ t} := rfl
  rw [hpre, kendallIntegrand]
  split_ifs with htu
  · have he : {v : I | g.cdf u v ≤ t} = univ :=
      eq_univ_of_forall fun v => (g.cdf_le_left u v).trans htu
    rw [he, measure_univ, ENNReal.toReal_one]
  · push Not at htu
    have htu' : t < u := htu
    have hc : 0 ≤ g.invFun t - g.invFun u := sub_nonneg.mpr (g.inv_antitone t u ht htu'.le)
    have he : {v : I | g.cdf u v ≤ t} = Iic (g.toI hc) := by
      ext v
      exact g.cdf_le_iff_le_toI ht htu' v
    have hpos : 0 < g.toFun (g.invFun t - g.invFun u) := by
      have := g.antitone_nonneg hc (g.inv_nonneg t ht) (sub_le_self _ (g.inv_nonneg u hu0))
      rw [g.right_inv t ht] at this
      exact (coe_pos ht).trans_le this
    have hL : g.toI hc ≠ 0 := g.toI_ne_zero hc hpos
    have hφL : g.invFun (g.toI hc) = g.invFun t - g.invFun u := g.invFun_toI hc hpos
    have hCt : 0 < g.toFun (g.invFun u + g.invFun (g.toI hc)) := by
      rw [hφL, add_sub_cancel, g.right_inv t ht]
      exact coe_pos ht
    rw [he]
    change g.copula.conditionalCDF u (g.toI hc) = _
    rw [hcond _ hL hCt, hφL, add_sub_cancel, g.invFunReal_coe]

/-- The derivative of the generator is interval integrable on `[t, 1]`. -/
private theorem intervalIntegrable_deriv (h : g.IsC1 ψ') {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) (hcont : ContinuousOn g.invFunReal (Icc t 1)) :
    IntervalIntegrable (fun x => (ψ' (g.invFunReal x))⁻¹) volume t 1 := by
  have hneg : IntegrableOn (fun x => -(ψ' (g.invFunReal x))⁻¹) (Ioc t 1) := by
    apply intervalIntegral.integrableOn_deriv_of_nonneg (g := fun x => -g.invFunReal x) hcont.neg
    · intro x hx
      exact (h.hasDerivAt_invFunReal ⟨ht0.trans hx.1, hx.2⟩).neg
    · intro x hx
      have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨ht0.trans hx.1, hx.2⟩
      have := h.deriv_neg (invFunReal_pos (g := g) hx')
        (by rw [toFun_invFunReal hx'.1 hx'.2.le]; exact hx'.1)
      exact neg_nonneg.mpr (inv_nonpos.mpr this.le)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht1.le]
  simpa using hneg.neg

/-- The generator is continuous on `[t, 1]` for `t > 0`. -/
private theorem continuousOn_invFunReal (g : BivariateGenerator) {t : ℝ} (ht0 : 0 < t) :
    ContinuousOn g.invFunReal (Icc t 1) := by
  intro x hx
  rcases hx.2.lt_or_eq with hx1 | hx1
  · exact (g.continuousAt_invFunReal (ht0.trans_le hx.1) hx1).continuousWithinAt
  · subst hx1
    have h1 : g.invFunReal 1 = 0 := by
      rw [show (1 : ℝ) = ((1 : I) : ℝ) from rfl, g.invFunReal_coe, g.inv_one]
    have hw : ContinuousWithinAt g.invFunReal (Icc 0 1 \ {1}) 1 := by
      unfold ContinuousWithinAt
      rw [h1]
      exact g.tendsto_invFunReal_one.mono_right nhdsWithin_le_nhds
    exact (continuousWithinAt_sdiff_self.mp hw).mono (Icc_subset_Icc_left ht0.le)

/-- Nelsen, Theorem 4.3.4: the Kendall distribution function of the copula of a `C¹`
generator is `K_C(t) = P(C(U, V) ≤ t) = t − φ(t) ψ'(φ(t))` for `0 < t ≤ 1`. -/
theorem measureReal_cdf_le (h : g.IsC1 ψ') {t : I} (ht : t ≠ 0) :
    g.copula.toMeasure.real {x | g.copula.cdf x ≤ t} =
      t - g.invFun t * ψ' (g.invFun t) := by
  by_cases ht1 : t = 1
  · subst ht1
    have he : {x | g.copula.cdf x ≤ ((1 : I) : ℝ)} = univ :=
      eq_univ_of_forall fun x => g.copula.cdf_le_one x
    rw [he, probReal_univ, g.inv_one, zero_mul, sub_zero]
    rfl
  have ht0 : 0 < (t : ℝ) := coe_pos ht
  have ht1' : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 (fun e => ht1 (Subtype.ext e))
  let s : Set (I × I) := {p | g.cdf p.1 p.2 ≤ t}
  have hs : MeasurableSet s := sections_measurableSet g t
  have hset : {x | g.copula.cdf x ≤ t} = (fun x : Fin 2 → I => (x 0, x 1)) ⁻¹' s := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, s, cdf_copula]
  -- Disintegration.
  have hK : g.copula.toMeasure.real {x | g.copula.cdf x ≤ t} =
      ∫ u : I, kendallIntegrand g ψ' t u := by
    rw [Measure.real, hset, measure_pair_preimage_eq_lintegral _ hs,
      ← integral_toReal (Kernel.measurable_kernel_prodMk_left hs).aemeasurable
        (Eventually.of_forall fun _ => measure_lt_top _ _)]
    exact integral_congr_ae (ae_section_eq h ht)
  rw [hK]
  -- Pass to an interval integral on `[0, 1]`.
  have hI : (∫ u : I, kendallIntegrand g ψ' t u) = ∫ x in (0 : ℝ)..1, kendallIntegrand g ψ' t x := by
    have h1 := integral_Iic_unit_eq_interval (fun u : I => kendallIntegrand g ψ' t u) 1
    rw [show Iic (1 : I) = univ from eq_univ_of_forall fun x => mem_Iic.mpr unitInterval.le_one',
      Measure.restrict_univ, Set.Icc.coe_one] at h1
    rw [h1]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    simp only [projIcc_of_mem zero_le_one hx]
  rw [hI]
  -- Split at `t`.
  have hcont := continuousOn_invFunReal g ht0
  have hderiv := intervalIntegrable_deriv h ht0 ht1' hcont
  have hleft : EqOn (kendallIntegrand g ψ' t) (fun _ => 1) (uIoc 0 t) := by
    intro x hx
    rw [uIoc_of_le ht0.le] at hx
    simp [kendallIntegrand, hx.2]
  have hright : EqOn (fun x => ψ' (g.invFun t) * (ψ' (g.invFunReal x))⁻¹)
      (kendallIntegrand g ψ' t) (uIoc t 1) := by
    intro x hx
    rw [uIoc_of_le ht1'.le] at hx
    simp [kendallIntegrand, not_le.mpr hx.1]
  have hi1 : IntervalIntegrable (kendallIntegrand g ψ' t) volume 0 t :=
    (intervalIntegrable_const (c := (1 : ℝ))).congr (fun x hx => (hleft hx).symm)
  have hi2 : IntervalIntegrable (kendallIntegrand g ψ' t) volume t 1 :=
    (hderiv.const_mul (ψ' (g.invFun t))).congr hright
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hA : (∫ x in (0 : ℝ)..t, kendallIntegrand g ψ' t x) = t := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (1 : ℝ))
      (Eventually.of_forall fun x hx => hleft hx)]
    simp
  have hB : (∫ x in (t : ℝ)..1, kendallIntegrand g ψ' t x) =
      ψ' (g.invFun t) * (0 - g.invFun t) := by
    rw [← intervalIntegral.integral_congr_ae (f := fun x => ψ' (g.invFun t) * (ψ' (g.invFunReal x))⁻¹)
      (Eventually.of_forall fun x hx => hright hx), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht1'.le hcont
        (fun x hx => h.hasDerivAt_invFunReal ⟨ht0.trans hx.1, hx.2⟩) hderiv]
    rw [show (1 : ℝ) = ((1 : I) : ℝ) from rfl, g.invFunReal_coe, g.invFunReal_coe, g.inv_one]
  rw [hA, hB]
  ring

/-- Nelsen, Theorem 4.3.4 in the original form `K_C(t) = t − φ(t) / φ'(t)`, `0 < t < 1`,
with `φ'` the derivative of the generator. -/
theorem measureReal_cdf_le_deriv (h : g.IsC1 ψ') {t : I} (ht : t ≠ 0) (ht1 : t ≠ 1) :
    g.copula.toMeasure.real {x | g.copula.cdf x ≤ t} =
      t - g.invFun t / deriv g.invFunReal t := by
  have hx : (t : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨coe_pos ht, lt_of_le_of_ne t.property.2 (fun e => ht1 (Subtype.ext e))⟩
  rw [h.measureReal_cdf_le ht, (h.hasDerivAt_invFunReal hx).deriv, g.invFunReal_coe, div_inv_eq_mul]

end IsC1

end BivariateGenerator

end ProbabilityTheory.Copula
