/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Nelsen
import Copula.TailDependence.Basic

open Filter
open scoped unitInterval Topology
namespace ProbabilityTheory.Copula

private theorem nelsen12_diagonal (θ : ℝ) (hθ : 1 ≤ θ) (t : I)
    (ht : 0 < (t : ℝ)) :
    (nelsen12 θ hθ).diagonal t =
      (1 + (2 : ℝ) ^ θ⁻¹ * ((t : ℝ)⁻¹ - 1))⁻¹ := by
  have htn : t ≠ 0 := ne_of_gt ht
  have hx : 0 ≤ (t : ℝ)⁻¹ - 1 := by
    have hh := one_div_le_one_div_of_le ht t.property.2
    simpa only [one_div, div_one] using sub_nonneg.mpr hh
  have hpow : (((t : ℝ)⁻¹ - 1) ^ θ + ((t : ℝ)⁻¹ - 1) ^ θ) ^ θ⁻¹ =
      (2 : ℝ) ^ θ⁻¹ * ((t : ℝ)⁻¹ - 1) := by
    rw [← two_mul, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hx _),
      Real.rpow_rpow_inv hx (by linarith : θ ≠ 0)]
  rw [diagonal, nelsen12_cdf_full]
  simp only [htn, or_self, ↓reduceIte]
  rw [hpow]

private theorem nelsen12_lower_ratio (θ : ℝ) (hθ : 1 ≤ θ) (t : I)
    (ht : 0 < (t : ℝ)) :
    (nelsen12 θ hθ).lowerTailRatio t =
      (t + (2 : ℝ) ^ θ⁻¹ * (1 - (t : ℝ)))⁻¹ := by
  have htn : (t : ℝ) ≠ 0 := ne_of_gt ht
  rw [lowerTailRatio, nelsen12_diagonal θ hθ t ht]
  have hden : 0 < (t : ℝ) + (2 : ℝ) ^ θ⁻¹ * (1 - (t : ℝ)) := by
    have hp : 0 < (2 : ℝ) ^ θ⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
    have ht1 : 0 ≤ 1 - (t : ℝ) := by linarith [t.property.2]
    have hh := mul_nonneg hp.le ht1
    linarith
  have heq : (1 + (2 : ℝ) ^ θ⁻¹ * ((t : ℝ)⁻¹ - 1)) * (t : ℝ) =
      (t : ℝ) + (2 : ℝ) ^ θ⁻¹ * (1 - (t : ℝ)) := by
    field_simp
  rw [← heq]
  rw [mul_inv_rev]
  field_simp

/-- The Nelsen 12 lower-tail coefficient for every finite parameter. -/
theorem hasLowerTailDependence_nelsen12 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen12 θ hθ).HasLowerTailDependence ((2 : ℝ) ^ θ⁻¹)⁻¹ := by
  let a : ℝ := (2 : ℝ) ^ θ⁻¹
  have ha : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  have hco : Tendsto (fun t : I => (t : ℝ)) (𝓝[>] (0 : I)) (𝓝 (0 : ℝ)) :=
    (continuous_subtype_val.tendsto (0 : I)).mono_left nhdsWithin_le_nhds
  have hc : ContinuousAt (fun x : ℝ => (x + a * (1 - x))⁻¹) 0 := by
    have hden : ContinuousAt (fun x : ℝ => x + a * (1 - x)) 0 := by fun_prop
    exact hden.inv₀ (by simpa using ha.ne')
  have hlim := hc.tendsto.comp hco
  have hpos : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < (t : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  have heq : ∀ᶠ t : I in 𝓝[>] (0 : I),
      (nelsen12 θ hθ).lowerTailRatio t =
        ((t : ℝ) + a * (1 - (t : ℝ)))⁻¹ := by
    filter_upwards [hpos] with t ht
    exact nelsen12_lower_ratio θ hθ t ht
  change Tendsto (nelsen12 θ hθ).lowerTailRatio (𝓝[>] (0 : I)) (𝓝 (((2 : ℝ) ^ θ⁻¹)⁻¹))
  simpa only [Function.comp_def, zero_add, sub_zero, one_mul, mul_one, a] using
    hlim.congr' (heq.mono fun t ht => ht.symm)
private theorem nelsen12_upper_ratio (θ : ℝ) (hθ : 1 ≤ θ) (t : I)
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    (nelsen12 θ hθ).upperTailRatio t =
      (2 - (2 : ℝ) ^ θ⁻¹ + 2 * ((2 : ℝ) ^ θ⁻¹ - 1) * (t : ℝ)) /
        (1 + ((2 : ℝ) ^ θ⁻¹ - 1) * (t : ℝ)) := by
  let a : ℝ := (2 : ℝ) ^ θ⁻¹
  have ha : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  have hs : 0 < (unitInterval.symm t : ℝ) := by
    rw [unitInterval.coe_symm_eq]
    linarith
  have hst : 0 < 1 - (t : ℝ) := by linarith
  have hden : 0 < 1 + (a - 1) * (t : ℝ) := by
    have hh := mul_nonneg ha.le ht0.le
    dsimp [a] at hh ⊢
    linarith
  have hbase : 0 < 1 + a * ((1 - (t : ℝ))⁻¹ - 1) := by
    have hsmall : 0 ≤ (1 - (t : ℝ))⁻¹ - 1 := by
      have hh := one_div_le_one_div_of_le hst (by linarith [ht0] : 1 - (t : ℝ) ≤ 1)
      simpa only [one_div, div_one] using sub_nonneg.mpr hh
    have hh := mul_nonneg ha.le hsmall
    linarith
  have hb : 1 + a * ((1 - (t : ℝ))⁻¹ - 1) =
      (1 + (a - 1) * (t : ℝ)) / (1 - (t : ℝ)) := by
    field_simp
    ring
  rw [upperTailRatio_eq, nelsen12_diagonal θ hθ (unitInterval.symm t) hs]
  rw [unitInterval.coe_symm_eq, ← show a = (2 : ℝ) ^ θ⁻¹ from rfl, hb, inv_div]
  have hden' : 0 < 1 - (t : ℝ) + (t : ℝ) * a := by nlinarith [hden]
  field_simp [hden'.ne', ht0.ne', hst.ne']
  have hcancel : (1 - (t : ℝ) + (t : ℝ) * a) * (1 - (t : ℝ) + (t : ℝ) * a)⁻¹ = 1 :=
    mul_inv_cancel₀ hden'.ne'
  linear_combination -(2 * (t : ℝ) - 1) * hcancel
/-- The Nelsen 12 upper-tail coefficient for every finite parameter. -/
theorem hasUpperTailDependence_nelsen12 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen12 θ hθ).HasUpperTailDependence (2 - (2 : ℝ) ^ θ⁻¹) := by
  let a : ℝ := (2 : ℝ) ^ θ⁻¹
  have hco : Tendsto (fun t : I => (t : ℝ)) (𝓝[>] (0 : I)) (𝓝 (0 : ℝ)) :=
    (continuous_subtype_val.tendsto (0 : I)).mono_left nhdsWithin_le_nhds
  have hc : ContinuousAt (fun x : ℝ =>
      (2 - a + 2 * (a - 1) * x) / (1 + (a - 1) * x)) 0 := by
    have hn : ContinuousAt (fun x : ℝ => 2 - a + 2 * (a - 1) * x) 0 := by fun_prop
    have hd : ContinuousAt (fun x : ℝ => 1 + (a - 1) * x) 0 := by fun_prop
    exact hn.div hd (by norm_num)
  have hlim := hc.tendsto.comp hco
  have hpos : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < (t : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  have hlt : ∀ᶠ t : I in 𝓝[>] (0 : I), (t : ℝ) < 1 :=
    hco.eventually (eventually_lt_nhds (by norm_num))
  have heq : ∀ᶠ t : I in 𝓝[>] (0 : I),
      (nelsen12 θ hθ).upperTailRatio t =
        (2 - a + 2 * (a - 1) * (t : ℝ)) / (1 + (a - 1) * (t : ℝ)) := by
    filter_upwards [hpos, hlt] with t ht0 ht1
    exact nelsen12_upper_ratio θ hθ t ht0 ht1
  change Tendsto (nelsen12 θ hθ).upperTailRatio (𝓝[>] (0 : I))
    (𝓝 (2 - (2 : ℝ) ^ θ⁻¹))
  simpa only [Function.comp_def, mul_zero, add_zero, div_one, a] using
    hlim.congr' (heq.mono fun t ht => ht.symm)
end ProbabilityTheory.Copula
