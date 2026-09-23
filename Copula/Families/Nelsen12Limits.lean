/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/import Copula.Families.Nelsen
import Copula.Families.Nelsen2Limits
import Copula.Rank.Integration


/-! # Nelsen 12 infinite-parameter endpoint

The positive-coordinate CDF is a reciprocal of a two-coordinate power norm.
Its pointwise limit is comonotonicity, including the grounded axes.
-/
open Filter
open scoped unitInterval Topology
namespace ProbabilityTheory.Copula

private theorem twoTermPowerNorm_ge (p a b : ℝ) (hp : 0 < p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max a b ≤ (a ^ p + b ^ p) ^ p⁻¹ := by
  have hpa : a ^ p ≤ a ^ p + b ^ p := le_add_of_nonneg_right (Real.rpow_nonneg hb _)
  have hpb : b ^ p ≤ a ^ p + b ^ p := le_add_of_nonneg_left (Real.rpow_nonneg ha _)
  have hia := Real.rpow_le_rpow (Real.rpow_nonneg ha _) hpa (inv_nonneg.mpr hp.le)
  have hib := Real.rpow_le_rpow (Real.rpow_nonneg hb _) hpb (inv_nonneg.mpr hp.le)
  rw [Real.rpow_rpow_inv ha hp.ne'] at hia
  rw [Real.rpow_rpow_inv hb hp.ne'] at hib
  exact max_le hia hib

theorem tendsto_twoTermPowerNorm {α : Type*} {l : Filter α}
    (θ : α → ℝ) (hθ : ∀ z, 1 ≤ θ z) (hlim : Tendsto θ l atTop)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (fun z => (a ^ θ z + b ^ θ z) ^ (θ z)⁻¹) l (𝓝 (max a b)) := by
  have hq : Tendsto (fun z => (2 : ℝ) ^ (θ z)⁻¹) l (𝓝 1) := by
    have hi := tendsto_inv_atTop_zero.comp hlim
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : α => (2 : ℝ)) l (𝓝 2)).rpow hi
      (Or.inl (by norm_num : (2 : ℝ) ≠ 0)))
  have hupper : Tendsto (fun z => (2 : ℝ) ^ (θ z)⁻¹ * max a b) l (𝓝 (max a b)) := by
    simpa only [one_mul] using hq.mul (tendsto_const_nhds : Tendsto (fun _ : α => max a b) l (𝓝 (max a b)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro z
    exact twoTermPowerNorm_ge (θ z) a b (by linarith [hθ z]) ha hb
  · intro z
    exact twoTermPowerNorm_le (θ z) a b (by linarith [hθ z]) ha hb

/-- Nelsen 12 converges pointwise to the upper Fréchet bound. -/
theorem tendsto_nelsen12_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 1 ≤ θ z) (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun z => (nelsen12 (θ z) (hθ z)).cdf u) l
      (𝓝 ((comonotonic 2).cdf u)) := by
  by_cases hu : u 0 = 0
  · have hzero (z : α) : (nelsen12 (θ z) (hθ z)).cdf u = 0 :=
      (nelsen12 (θ z) (hθ z)).cdf_eq_zero_of_coord_eq_zero u 0 hu
    have htarget : (comonotonic 2).cdf u = 0 :=
      (comonotonic 2).cdf_eq_zero_of_coord_eq_zero u 0 hu
    simpa only [hzero, htarget] using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 0))
  by_cases hv : u 1 = 0
  · have hzero (z : α) : (nelsen12 (θ z) (hθ z)).cdf u = 0 :=
      (nelsen12 (θ z) (hθ z)).cdf_eq_zero_of_coord_eq_zero u 1 hv
    have htarget : (comonotonic 2).cdf u = 0 :=
      (comonotonic 2).cdf_eq_zero_of_coord_eq_zero u 1 hv
    simpa only [hzero, htarget] using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 0))
  let x : ℝ := (u 0 : ℝ)⁻¹ - 1
  let y : ℝ := (u 1 : ℝ)⁻¹ - 1
  have hu' : 0 < (u 0 : ℝ) := lt_of_le_of_ne (u 0).property.1
    (Ne.symm (fun h => hu (Subtype.ext h)))
  have hv' : 0 < (u 1 : ℝ) := lt_of_le_of_ne (u 1).property.1
    (Ne.symm (fun h => hv (Subtype.ext h)))
  have hx : 0 ≤ x := by
    have hh := one_div_le_one_div_of_le hu' (u 0).property.2
    dsimp [x]
    simpa only [one_div, div_one] using sub_nonneg.mpr hh
  have hy : 0 ≤ y := by
    have hh := one_div_le_one_div_of_le hv' (u 1).property.2
    dsimp [y]
    simpa only [one_div, div_one] using sub_nonneg.mpr hh
  have hp := tendsto_twoTermPowerNorm θ hθ hlim x y hx hy
  have hpos : 0 < 1 + max x y := by
    have hm : 0 ≤ max x y := hx.trans (le_max_left x y)
    linarith
  have hc : ContinuousAt (fun t : ℝ => (1+t)⁻¹) (max x y) :=
    (continuousAt_const.add continuousAt_id).inv₀ hpos.ne'
  have hlimit := hc.tendsto.comp hp
  have htarget : (1+max x y)⁻¹ = (comonotonic 2).cdf u := by
    rw [cdf_comonotonic_two]
    rcases le_total (u 0 : ℝ) (u 1 : ℝ) with h | h
    · have hxy : y ≤ x := by
        have hh := one_div_le_one_div_of_le hu' h
        dsimp [x, y]
        simpa only [one_div] using sub_le_sub_right hh 1
      rw [max_eq_left hxy, min_eq_left h]
      simp [x]
    · have hxy : x ≤ y := by
        have hh := one_div_le_one_div_of_le hv' h
        dsimp [x, y]
        simpa only [one_div] using sub_le_sub_right hh 1
      rw [max_eq_right hxy, min_eq_right h]
      simp [y]
  have hformula (z : α) : (nelsen12 (θ z) (hθ z)).cdf u =
      (1 + (x ^ θ z + y ^ θ z) ^ (θ z)⁻¹)⁻¹ := by
    have hz : u = ![u 0, u 1] := by funext i; fin_cases i <;> rfl
    rw [hz, nelsen12_cdf_full]
    simp only [hu, hv, or_self, ↓reduceIte]
    rfl
  simpa only [Function.comp_def, hformula, htarget] using hlimit
end ProbabilityTheory.Copula
