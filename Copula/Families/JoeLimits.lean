/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/import Copula.Families.Joe
import Copula.Families.Nelsen12Limits
import Copula.Rank.Integration


/-! # Joe infinite-parameter endpoint

The power-sum-minus-product CDF base is squeezed between the maximum term
and the two-term power sum. Its pointwise limit is comonotonicity.
-/
open Filter
open scoped unitInterval Topology
namespace ProbabilityTheory.Copula

private theorem joePower_bounds (p a b : ℝ) (hp : 0 < p)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    max a b ≤ (a ^ p + b ^ p - a ^ p * b ^ p) ^ p⁻¹ ∧
      (a ^ p + b ^ p - a ^ p * b ^ p) ^ p⁻¹ ≤
        (a ^ p + b ^ p) ^ p⁻¹ := by
  have hap : 0 ≤ a ^ p := Real.rpow_nonneg ha _
  have hbp : 0 ≤ b ^ p := Real.rpow_nonneg hb _
  have hap1 : a ^ p ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow ha ha1 hp.le
  have hbp1 : b ^ p ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow hb hb1 hp.le
  have habase : 0 ≤ a ^ p + b ^ p - a ^ p * b ^ p := by
    nlinarith [mul_nonneg hbp (sub_nonneg.mpr hap1)]
  have hpa : a ^ p ≤ a ^ p + b ^ p - a ^ p * b ^ p := by
    nlinarith [mul_nonneg hbp (sub_nonneg.mpr hap1)]
  have hpb : b ^ p ≤ a ^ p + b ^ p - a ^ p * b ^ p := by
    nlinarith [mul_nonneg hap (sub_nonneg.mpr hbp1)]
  have hia := Real.rpow_le_rpow hap hpa (inv_nonneg.mpr hp.le)
  have hib := Real.rpow_le_rpow hbp hpb (inv_nonneg.mpr hp.le)
  rw [Real.rpow_rpow_inv ha hp.ne'] at hia
  rw [Real.rpow_rpow_inv hb hp.ne'] at hib
  constructor
  · exact max_le hia hib
  · exact Real.rpow_le_rpow habase (by nlinarith [mul_nonneg hap hbp])
      (inv_nonneg.mpr hp.le)

/-- Joe converges pointwise to the upper Fréchet bound. -/
theorem tendsto_joe_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 1 ≤ θ z) (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun z => (joe (θ z) (hθ z)).cdf u) l
      (𝓝 ((comonotonic 2).cdf u)) := by
  by_cases hu : u 0 = 0
  · have hzero (z : α) : (joe (θ z) (hθ z)).cdf u = 0 :=
      (joe (θ z) (hθ z)).cdf_eq_zero_of_coord_eq_zero u 0 hu
    have htarget : (comonotonic 2).cdf u = 0 :=
      (comonotonic 2).cdf_eq_zero_of_coord_eq_zero u 0 hu
    simpa only [hzero, htarget] using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 0))
  by_cases hv : u 1 = 0
  · have hzero (z : α) : (joe (θ z) (hθ z)).cdf u = 0 :=
      (joe (θ z) (hθ z)).cdf_eq_zero_of_coord_eq_zero u 1 hv
    have htarget : (comonotonic 2).cdf u = 0 :=
      (comonotonic 2).cdf_eq_zero_of_coord_eq_zero u 1 hv
    simpa only [hzero, htarget] using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 0))
  let a : ℝ := 1 - (u 0 : ℝ)
  let b : ℝ := 1 - (u 1 : ℝ)
  have ha : 0 ≤ a := by dsimp [a]; linarith [(u 0).property.2]
  have hb : 0 ≤ b := by dsimp [b]; linarith [(u 1).property.2]
  have ha1 : a ≤ 1 := by dsimp [a]; linarith [(u 0).property.1]
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [(u 1).property.1]
  have hupper := tendsto_twoTermPowerNorm θ hθ hlim a b ha hb
  have hnorm : Tendsto
      (fun z => (a ^ θ z + b ^ θ z - a ^ θ z * b ^ θ z) ^ (θ z)⁻¹)
      l (𝓝 (max a b)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro z
      exact (joePower_bounds (θ z) a b (by linarith [hθ z]) ha ha1 hb hb1).1
    · intro z
      exact (joePower_bounds (θ z) a b (by linarith [hθ z]) ha ha1 hb hb1).2
  have hc : Continuous (fun t : ℝ => 1 - t) := by fun_prop
  have hlimit := hc.continuousAt.tendsto.comp hnorm
  have htarget : 1 - max a b = (comonotonic 2).cdf u := by
    rw [cdf_comonotonic_two]
    rcases le_total (u 0 : ℝ) (u 1 : ℝ) with h | h
    · have hab : b ≤ a := by dsimp [a,b]; linarith
      rw [max_eq_left hab, min_eq_left h]
      dsimp [a]
      ring
    · have hab : a ≤ b := by dsimp [a,b]; linarith
      rw [max_eq_right hab, min_eq_right h]
      dsimp [b]
      ring
  have hformula (z : α) : (joe (θ z) (hθ z)).cdf u =
      1 - (a ^ θ z + b ^ θ z - a ^ θ z * b ^ θ z) ^ (θ z)⁻¹ := by
    have hz : u = ![u 0, u 1] := by funext i; fin_cases i <;> rfl
    rw [hz, joe_cdf_full]
    simp only [hu, hv, or_self, ↓reduceIte]
    rfl
  simpa only [Function.comp_def, hformula, htarget] using hlimit

end ProbabilityTheory.Copula
