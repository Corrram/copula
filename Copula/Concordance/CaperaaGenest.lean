/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.Common.StochasticRho
import Copula.Dependence.HierarchyCorner

/-!
# Spearman's rho dominates Kendall's tau under positive tail monotonicity

Capéraà and Genest (1993), *Spearman's ρ is larger than Kendall's τ for positively dependent
random variables*, J. Nonparametric Statistics 2, 183–194; see also Nelsen,
*An Introduction to Copulas*, 2nd ed., §5.2.3: if `V` is left tail decreasing and right tail
increasing in `U`, then

`0 ≤ τ ≤ ρ`.

In particular this holds for stochastically increasing copulas, for LCSD ∧ RCSI copulas and
for copulas with an MTP2 density (via `Dependence.HierarchyDensity`). Combined with the PQD bound
`ρ ≤ 3τ` this gives `τ ≤ ρ ≤ 3τ`.

## Proof

Write `D(u,v) = C(u,v) - uv`. LTD says `D(u,v)/u` decreases in `u`, and RTI says
`D(u,v)/(1-u)` increases in `u`. Hence, for every fixed `v` and `u₀ ∈ (0,1)`, the section
`D(·,v)` dominates the tent `D(u₀,v) · min(u/u₀, (1-u)/(1-u₀))`, whose integral is `D(u₀,v)/2`.
So every value of `D(·,v)` is at most twice its mean:

`D(u₀,v) ≤ 2 ∫₀¹ D(u,v) du`.

Integrating this pointwise bound with respect to `C` (whose second marginal is uniform) gives
`∫ D dC ≤ 2 ∫∫ D`, which is exactly `τ ≤ ρ` since `ρ - τ = 8 ∫∫ D - 4 ∫ D dC`.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The tent `min(t/a, (1-t)/(1-a))` has integral `1/2` over `[0,1]`. -/
private theorem integral_tent {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (∫ t in (0 : ℝ)..1, min (t / a) ((1 - t) / (1 - a))) = 1 / 2 := by
  have hc : Continuous (fun t : ℝ => min (t / a) ((1 - t) / (1 - a))) := by fun_prop
  have h1a : (0 : ℝ) < 1 - a := by linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a)
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a 1)]
  have hl : (∫ t in (0 : ℝ)..a, min (t / a) ((1 - t) / (1 - a))) =
      ∫ t in (0 : ℝ)..a, t / a := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le ha0.le] at ht
    apply min_eq_left
    rw [div_le_div_iff₀ ha0 h1a]
    nlinarith [ht.1, ht.2]
  have hr : (∫ t in a..1, min (t / a) ((1 - t) / (1 - a))) =
      ∫ t in a..1, (1 - t) / (1 - a) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le ha1.le] at ht
    apply min_eq_right
    rw [div_le_div_iff₀ h1a ha0]
    nlinarith [ht.1, ht.2]
  rw [hl, hr, intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    integral_id, integral_id, intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

/-- Under LTD and RTI every value of a section of `C - Π` is at most twice its mean. -/
theorem IsLTD.cdf_sub_mul_le_two_mul_integral {C : Copula 2} (hL : C.IsLTD) (hR : C.IsRTI)
    (u₀ v : I) :
    C.cdf ![u₀, v] - (u₀ : ℝ) * v ≤ 2 * ∫ u : I, (C.cdf ![u, v] - (u : ℝ) * v) := by
  have hpqd := hL.isPQD
  have hint : 0 ≤ ∫ u : I, (C.cdf ![u, v] - (u : ℝ) * v) :=
    integral_nonneg fun u => sub_nonneg.mpr (hpqd u v)
  by_cases h0 : (u₀ : ℝ) = 0
  · have : u₀ = 0 := Subtype.ext h0
    subst this
    simp only [cdf_two_zero_left, Set.Icc.coe_zero, zero_mul, sub_zero]
    linarith
  by_cases h1 : (u₀ : ℝ) = 1
  · have : u₀ = 1 := Subtype.ext h1
    subst this
    simp only [cdf_two_one_left, Set.Icc.coe_one, one_mul, sub_self]
    linarith
  have hu0 : 0 < (u₀ : ℝ) := lt_of_le_of_ne u₀.2.1 (Ne.symm h0)
  have hu1 : (u₀ : ℝ) < 1 := lt_of_le_of_ne u₀.2.2 h1
  set d := C.cdf ![u₀, v] - (u₀ : ℝ) * v with hd
  have hd0 : 0 ≤ d := sub_nonneg.mpr (hpqd u₀ v)
  let T : ℝ → ℝ := fun t => min (t / u₀) ((1 - t) / (1 - u₀))
  have hpoint : ∀ u : I, d * T u ≤ C.cdf ![u, v] - (u : ℝ) * v := by
    intro u
    rcases le_total u u₀ with hu | hu
    · have hT : T u ≤ (u : ℝ) / u₀ := min_le_left _ _
      have hl := hL u u₀ v hu
      calc d * T u ≤ d * ((u : ℝ) / u₀) := mul_le_mul_of_nonneg_left hT hd0
        _ ≤ _ := by
          rw [mul_div_assoc', div_le_iff₀ hu0]
          rw [hd]
          nlinarith
    · have hT : T u ≤ (1 - (u : ℝ)) / (1 - u₀) := min_le_right _ _
      have hr := hR u₀ u v hu
      have h1u0 : 0 < 1 - (u₀ : ℝ) := by linarith
      calc d * T u ≤ d * ((1 - (u : ℝ)) / (1 - u₀)) := mul_le_mul_of_nonneg_left hT hd0
        _ ≤ _ := by
          rw [mul_div_assoc', div_le_iff₀ h1u0]
          rw [hd]
          nlinarith
  have hTint : Integrable (fun u : I => d * T u) :=
    integrable_continuous_unit volume (by fun_prop)
  have hDint : Integrable (fun u : I => C.cdf ![u, v] - (u : ℝ) * v) :=
    integrable_continuous_unit volume (by fun_prop)
  have hmono := integral_mono hTint hDint hpoint
  rw [integral_const_mul, integral_unitInterval T, integral_tent hu0 hu1] at hmono
  linarith

/-- **Capéraà–Genest.** If `V` is left tail decreasing and right tail increasing in `U`, then
Kendall's tau is at most Spearman's rho (Capéraà–Genest 1993; Nelsen, §5.2.3). -/
theorem IsLTD.kendallTau_le_spearmanRho {C : Copula 2} (hL : C.IsLTD) (hR : C.IsRTI) :
    C.kendallTau ≤ C.spearmanRho := by
  have hi : Integrable (fun p : I × I => C.cdf ![p.1, p.2])
      ((volume : Measure I).prod volume) :=
    (C.continuous_cdf.comp (by fun_prop)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let g : I → ℝ := fun v => 2 * (∫ u : I, C.cdf ![u, v]) - (v : ℝ)
  have hv : Integrable (fun v : I => (v : ℝ)) :=
    integrable_continuous_unit volume continuous_subtype_val
  have hg : Integrable g := (hi.integral_prod_right.const_mul 2).sub hv
  -- pointwise bound `D(x) ≤ g(x 1)`
  have hpoint : ∀ x : Fin 2 → I, C.cdf x - (x 0 : ℝ) * (x 1 : ℝ) ≤ g (x 1) := by
    intro x
    have hx : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
    have h := hL.cdf_sub_mul_le_two_mul_integral hR (x 0) (x 1)
    rw [hx] at h
    have hsplit : (∫ u : I, (C.cdf ![u, x 1] - (u : ℝ) * (x 1 : ℝ))) =
        (∫ u : I, C.cdf ![u, x 1]) - (x 1 : ℝ) / 2 := by
      rw [integral_sub (integrable_continuous_unit volume (by fun_prop))
        (integrable_continuous_unit volume (by fun_prop)), integral_mul_const, integral_unit_id]
      ring
    rw [hsplit] at h
    simp only [g]
    linarith
  -- integrate against `C`
  have hmap : C.toMeasure.map (fun x : Fin 2 → I => x 1) = volume := C.map_eval 1
  have hgC : Integrable (fun x : Fin 2 → I => g (x 1)) C.toMeasure := by
    have := hg
    rw [← hmap] at this
    exact this.comp_measurable (measurable_pi_apply 1)
  have hgint : (∫ x, g (x 1) ∂C.toMeasure) = ∫ v : I, g v := by
    rw [← integral_map (measurable_pi_apply 1).aemeasurable
      (by rw [hmap]; exact hg.aestronglyMeasurable), hmap]
  have hprod : Integrable (fun x : Fin 2 → I => (x 0 : ℝ) * (x 1 : ℝ)) C.toMeasure :=
    integrable_continuous_cube C.toMeasure (by fun_prop)
  have hmono := integral_mono ((C.integrable_cdf C.toMeasure).sub hprod) hgC hpoint
  simp only [Pi.sub_apply] at hmono
  rw [integral_sub (C.integrable_cdf C.toMeasure) hprod, hgint,
    integral_sub (hi.integral_prod_right.const_mul 2) hv, integral_const_mul,
    integral_unit_id] at hmono
  have h1 := RankRegion.Common.spearmanRho_eq_iterated_cdf C
  have h2 : C.spearmanRho = 12 * (∫ x, (x 0 : ℝ) * (x 1 : ℝ) ∂C.toMeasure) - 3 := rfl
  unfold kendallTau
  linarith

/-- **Capéraà–Genest.** If `V` is left tail decreasing and right tail increasing in `U`,
then `0 ≤ τ ≤ ρ`. -/
theorem IsLTD.kendallTau_mem_Icc_spearmanRho {C : Copula 2} (hL : C.IsLTD) (hR : C.IsRTI) :
    0 ≤ C.kendallTau ∧ C.kendallTau ≤ C.spearmanRho :=
  ⟨hL.isPQD.kendallTau_nonneg, hL.kendallTau_le_spearmanRho hR⟩

/-- The transposed Capéraà–Genest condition (`U` LTD and RTI in `V`) also gives `τ ≤ ρ`. -/
theorem kendallTau_le_spearmanRho_of_transpose {C : Copula 2} (hL : C.transpose.IsLTD)
    (hR : C.transpose.IsRTI) : C.kendallTau ≤ C.spearmanRho := by
  simpa using hL.kendallTau_le_spearmanRho hR

/-- Stochastically increasing copulas satisfy `0 ≤ τ ≤ ρ` (Capéraà–Genest). -/
theorem IsSI.kendallTau_le_spearmanRho {C : Copula 2} (h : C.IsSI) :
    C.kendallTau ≤ C.spearmanRho :=
  h.isLTD.kendallTau_le_spearmanRho h.isRTI

/-- LCSD and RCSI together give `τ ≤ ρ`. -/
theorem IsLCSD.kendallTau_le_spearmanRho {C : Copula 2} (hL : C.IsLCSD) (hR : C.IsRCSI) :
    C.kendallTau ≤ C.spearmanRho :=
  hL.isLTD.kendallTau_le_spearmanRho hR.isRTI

/-- Under LTD and RTI, `τ ≤ ρ ≤ 3τ`. -/
theorem IsLTD.kendallTau_le_spearmanRho_le {C : Copula 2} (hL : C.IsLTD) (hR : C.IsRTI) :
    C.kendallTau ≤ C.spearmanRho ∧ C.spearmanRho ≤ 3 * C.kendallTau :=
  ⟨hL.kendallTau_le_spearmanRho hR, hL.isPQD.spearmanRho_le_three_mul_kendallTau⟩

end ProbabilityTheory.Copula
