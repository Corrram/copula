/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.KendallDistribution
import Copula.Archimedean.Power
import Copula.Rank.Basic
import Mathlib.MeasureTheory.Integral.Layercake

/-! # Kendall's tau of an Archimedean copula via its generator

Nelsen, *An Introduction to Copulas*, second edition, Corollary 5.1.4: for an Archimedean
copula with generator `φ`,
`τ_C = 1 + 4 ∫₀¹ φ(t) / φ'(t) dt`.

We prove this for generators whose inverse generator `ψ` has a continuous derivative where it is
positive (`BivariateGenerator.IsC1`; strict and non-strict generators alike), in the form
`τ_C = 1 + 4 ∫₀¹ φ(t) ψ'(φ(t)) dt` (`BivariateGenerator.IsC1.kendallTau_eq`) and in Nelsen's
form with the derivative of the generator (`BivariateGenerator.IsC1.kendallTau_eq_deriv`).

As in Nelsen's proof, `τ_C = 4 E[C(U, V)] − 1` with `E[C(U, V)] = ∫₀¹ (1 − K_C(t)) dt`
(layer-cake formula), and the Kendall distribution function `K_C(t) = t − φ(t) / φ'(t)` of
`Copula.Archimedean.KendallDistribution` (Nelsen, Theorem 4.3.4).

For the outer power `φ^δ`, `δ ≥ 1` (Nelsen, Section 4.5, the family `C_{φ^δ}`), the integrand
scales by `1/δ`, so `τ_{φ^δ} = 1 + (τ_φ − 1) / δ`
(`BivariateGenerator.IsC1.kendallTau_outerPower`).
-/

open MeasureTheory Set Filter
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace BivariateGenerator

namespace IsC1

variable {g : BivariateGenerator} {ψ' : ℝ → ℝ}

/-- Nelsen, Corollary 5.1.4: `τ_C = 1 + 4 ∫₀¹ φ(t) ψ'(φ(t)) dt` for a `C¹` generator,
where `φ(t) ψ'(φ(t)) = φ(t) / φ'(t)`. -/
theorem kendallTau_eq (h : g.IsC1 ψ') :
    g.copula.kendallTau = 1 + 4 * ∫ t in (0 : ℝ)..1, g.invFunReal t * ψ' (g.invFunReal t) := by
  set μ := g.copula.toMeasure
  let G : ℝ → ℝ := fun t => μ.real {x | t < g.copula.cdf x}
  have hG_anti : Antitone G := by
    intro a b hab
    exact measureReal_mono (fun x hx => lt_of_le_of_lt hab hx)
  -- Layer cake.
  have hlayer : (∫ x, g.copula.cdf x ∂μ) = ∫ t in (0 : ℝ)..1, G t := by
    rw [Integrable.integral_eq_integral_meas_lt (integrable_cdf _ _)
      (Eventually.of_forall fun x => g.copula.cdf_nonneg x),
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self,
      ← intervalIntegral.integral_of_le zero_le_one]
    intro t ht
    have ht1 : 1 < t := by
      rcases ht with ⟨ht0, htn⟩
      simp only [mem_Ioi] at ht0
      simp only [mem_Ioc, not_and, not_le] at htn
      exact htn ht0
    have he : {x | t < g.copula.cdf x} = ∅ :=
      eq_empty_of_forall_notMem fun x hx => absurd ((g.copula.cdf_le_one x).trans_lt ht1)
        (not_lt.mpr (le_of_lt hx))
    change μ.real {x | t < g.copula.cdf x} = 0
    rw [he, measureReal_empty]
  -- The survival function of the Kendall law on `(0, 1]`.
  have hGK : ∀ t ∈ Ioc (0 : ℝ) 1, G t - (1 - t) = g.invFunReal t * ψ' (g.invFunReal t) := by
    intro t ht
    let u : I := ⟨t, ht.1.le, ht.2⟩
    have hu : u ≠ 0 := fun e => ht.1.ne' (congrArg Subtype.val e)
    have hc : {x | t < g.copula.cdf x} = {x | g.copula.cdf x ≤ (u : ℝ)}ᶜ := by
      ext x
      simp only [mem_ofPred_eq, mem_compl_iff, not_le]
      rfl
    have hmeas : MeasurableSet {x | g.copula.cdf x ≤ (u : ℝ)} :=
      measurableSet_le g.copula.continuous_cdf.measurable measurable_const
    change μ.real {x | t < g.copula.cdf x} - (1 - t) = _
    rw [hc, measureReal_compl hmeas, probReal_univ, h.measureReal_cdf_le hu,
      show g.invFunReal t = g.invFun u from g.invFunReal_coe u]
    change 1 - (t - g.invFun u * ψ' (g.invFun u)) - (1 - t) = _
    ring
  have hGi : IntervalIntegrable G volume 0 1 := hG_anti.intervalIntegrable
  have hlin : IntervalIntegrable (fun t : ℝ => 1 - t) volume 0 1 :=
    intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_id
  have hJ : (∫ t in (0 : ℝ)..1, g.invFunReal t * ψ' (g.invFunReal t)) =
      (∫ t in (0 : ℝ)..1, G t) - 1 / 2 := by
    rw [← intervalIntegral.integral_congr_ae (f := fun t => G t - (1 - t))
      (Eventually.of_forall fun t ht => by
        rw [uIoc_of_le zero_le_one] at ht
        exact hGK t ht),
      intervalIntegral.integral_sub hGi hlin, intervalIntegral.integral_sub intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id, integral_id]
    norm_num
  rw [kendallTau, hlayer, hJ]
  ring

/-- Nelsen, Corollary 5.1.4 in its original form `τ_C = 1 + 4 ∫₀¹ φ(t) / φ'(t) dt`, with `φ'`
the derivative of the generator. -/
theorem kendallTau_eq_deriv (h : g.IsC1 ψ') :
    g.copula.kendallTau = 1 + 4 * ∫ t in (0 : ℝ)..1, g.invFunReal t / deriv g.invFunReal t := by
  rw [h.kendallTau_eq]
  congr 2
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le zero_le_one] at ht
  rcases ht.2.lt_or_eq with ht1 | ht1
  · rw [(h.hasDerivAt_invFunReal ⟨ht.1, ht1⟩).deriv, div_inv_eq_mul]
  · subst ht1
    have h1 : g.invFunReal 1 = 0 := by
      rw [show (1 : ℝ) = ((1 : I) : ℝ) from rfl, g.invFunReal_coe, g.inv_one]
    rw [h1, zero_mul, zero_div]

/-- The outer power `φ^δ` of a `C¹` generator is `C¹`, with
`(ψ(s^{1/δ}))' = ψ'(s^{1/δ}) · s^{1/δ - 1} / δ`. -/
theorem outerPower (h : g.IsC1 ψ') (δ : ℝ) (hδ : 1 ≤ δ) :
    (g.outerPower δ hδ).IsC1 (fun s => ψ' (s ^ δ⁻¹) * (δ⁻¹ * s ^ (δ⁻¹ - 1))) where
  hasDerivAt s hs hpos := by
    have h1 : HasDerivAt (fun x : ℝ => x ^ δ⁻¹) (δ⁻¹ * s ^ (δ⁻¹ - 1)) s :=
      Real.hasDerivAt_rpow_const (Or.inl hs.ne')
    have h2 : HasDerivAt g.toFun (ψ' (s ^ δ⁻¹)) ((fun x : ℝ => x ^ δ⁻¹) s) :=
      h.hasDerivAt _ (Real.rpow_pos_of_pos hs δ⁻¹) hpos
    have h3 := h2.comp s h1
    exact h3
  continuousAt s hs hpos := by
    have h1 : ContinuousAt (fun x : ℝ => x ^ δ⁻¹) s :=
      Real.continuousAt_rpow_const _ _ (Or.inl hs.ne')
    have h2 : ContinuousAt (fun x : ℝ => x ^ (δ⁻¹ - 1)) s :=
      Real.continuousAt_rpow_const _ _ (Or.inl hs.ne')
    have h3 : ContinuousAt (fun x : ℝ => ψ' (x ^ δ⁻¹)) s :=
      ContinuousAt.comp (f := fun x : ℝ => x ^ δ⁻¹) (g := ψ')
        (h.continuousAt _ (Real.rpow_pos_of_pos hs δ⁻¹) hpos) h1
    exact h3.mul (continuousAt_const.mul h2)

end IsC1

/-- The Kendall integrand `φ ψ'(φ)` of the outer power `φ^δ` is `1/δ` times that of `φ`. -/
theorem outerPower_integrand (g : BivariateGenerator) (ψ' : ℝ → ℝ) (δ : ℝ) (hδ : 1 ≤ δ) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    (g.outerPower δ hδ).invFunReal t *
        (ψ' ((g.outerPower δ hδ).invFunReal t ^ δ⁻¹) *
          (δ⁻¹ * (g.outerPower δ hδ).invFunReal t ^ (δ⁻¹ - 1))) =
      δ⁻¹ * (g.invFunReal t * ψ' (g.invFunReal t)) := by
  have hδ0 : δ ≠ 0 := by linarith
  let u : I := ⟨t, ht.1.le, ht.2⟩
  have hu : u ≠ 0 := fun e => ht.1.ne' (congrArg Subtype.val e)
  have hφ : (g.outerPower δ hδ).invFunReal t = g.invFunReal t ^ δ :=
    ((g.outerPower δ hδ).invFunReal_coe u).trans (by rw [g.invFunReal_coe u]; rfl)
  have hL : 0 ≤ g.invFunReal t := by
    rw [show g.invFunReal t = g.invFun u from g.invFunReal_coe u]
    exact g.inv_nonneg u hu
  rw [hφ, Real.rpow_rpow_inv hL hδ0, ← Real.rpow_mul hL,
    show δ * (δ⁻¹ - 1) = 1 - δ by field_simp]
  have hmul : g.invFunReal t ^ δ * g.invFunReal t ^ (1 - δ) = g.invFunReal t := by
    rw [← Real.rpow_add' hL (by ring_nf; norm_num), show δ + (1 - δ) = 1 by ring,
      Real.rpow_one]
  linear_combination (δ⁻¹ * ψ' (g.invFunReal t)) * hmul

namespace IsC1

variable {g : BivariateGenerator} {ψ' : ℝ → ℝ}

/-- Kendall's tau of the outer power `φ^δ`: `τ_{φ^δ} = 1 + (τ_φ − 1) / δ`. -/
theorem kendallTau_outerPower (h : g.IsC1 ψ') (δ : ℝ) (hδ : 1 ≤ δ) :
    (g.outerPower δ hδ).copula.kendallTau = 1 + (g.copula.kendallTau - 1) / δ := by
  have hδ0 : δ ≠ 0 := by linarith
  rw [(h.outerPower δ hδ).kendallTau_eq, h.kendallTau_eq]
  have hint : ∀ t ∈ uIoc (0 : ℝ) 1,
      (g.outerPower δ hδ).invFunReal t *
        (ψ' ((g.outerPower δ hδ).invFunReal t ^ δ⁻¹) *
          (δ⁻¹ * (g.outerPower δ hδ).invFunReal t ^ (δ⁻¹ - 1))) =
      δ⁻¹ * (g.invFunReal t * ψ' (g.invFunReal t)) := by
    intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    exact outerPower_integrand g ψ' δ hδ ht
  rw [intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => hint t ht),
    intervalIntegral.integral_const_mul]
  field_simp
  ring

end IsC1

end BivariateGenerator

end ProbabilityTheory.Copula
