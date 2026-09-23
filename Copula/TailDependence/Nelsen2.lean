/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/

import Copula.Families.Nelsen
import Copula.TailDependence.Basic

/-! # Exact Nelsen 2 tail dependence

Both tail limits hold for every finite parameter θ ≥ 1, including the
countermonotonic endpoint θ = 1.
-/

open Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

private theorem nelsen2_tail_ratio (θ : ℝ) (hθ : 1 ≤ θ) (t : I)
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (htsmall : (2 : ℝ) ^ θ⁻¹ * (t : ℝ) ≤ 1) :
    (nelsen2 θ hθ).upperTailRatio t = 2 - (2 : ℝ) ^ θ⁻¹ := by
  have hsymm : unitInterval.symm t ≠ 0 := by
    intro hz
    have h := congrArg (fun x : I => (x : ℝ)) hz
    simp only [unitInterval.coe_symm_eq] at h
    norm_num at h
    linarith
  have hpow : ((t : ℝ) ^ θ + (t : ℝ) ^ θ) ^ θ⁻¹ =
      (2 : ℝ) ^ θ⁻¹ * (t : ℝ) := by
    rw [← two_mul, Real.mul_rpow (by norm_num) (Real.rpow_nonneg t.property.1 _),
      Real.rpow_rpow_inv t.property.1 (by linarith : θ ≠ 0)]
  rw [Copula.upperTailRatio_eq, diagonal, nelsen2_cdf_full]
  simp only [hsymm, or_self, ↓reduceIte, unitInterval.coe_symm_eq]
  rw [show 1 - (1 - (t : ℝ)) = (t : ℝ) by ring]
  rw [hpow, max_eq_right (by linarith)]
  have hne : (t : ℝ) ≠ 0 := ne_of_gt ht0
  field_simp
  ring

/-- The Nelsen 2 upper-tail coefficient, including the countermonotonic endpoint. -/
theorem hasUpperTailDependence_nelsen2 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen2 θ hθ).HasUpperTailDependence (2 - (2 : ℝ) ^ θ⁻¹) := by
  have hp : 0 < (2 : ℝ) ^ θ⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
  have hcut : 0 < min (1 : ℝ) (1 / (2 : ℝ) ^ θ⁻¹) :=
    lt_min (by norm_num) (div_pos (by norm_num) hp)
  have hlim : Tendsto (fun t : I => (t : ℝ)) (𝓝[>] (0 : I)) (𝓝 (0 : ℝ)) :=
    (continuous_subtype_val.tendsto (0 : I)).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ t : I in 𝓝[>] (0 : I),
      (t : ℝ) < min 1 (1 / (2 : ℝ) ^ θ⁻¹) :=
    hlim.eventually (eventually_lt_nhds hcut)
  have hpos : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < (t : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  have heq : ∀ᶠ t : I in 𝓝[>] (0 : I),
      (nelsen2 θ hθ).upperTailRatio t = 2 - (2 : ℝ) ^ θ⁻¹ := by
    filter_upwards [hsmall, hpos] with t ht hp0
    have ht1 : (t : ℝ) < 1 := lt_of_lt_of_le ht (min_le_left _ _)
    have htdiv : (t : ℝ) ≤ 1 / (2 : ℝ) ^ θ⁻¹ :=
      le_of_lt (lt_of_lt_of_le ht (min_le_right _ _))
    have hbound : (2 : ℝ) ^ θ⁻¹ * (t : ℝ) ≤ 1 := by
      have hh := (le_div_iff₀ hp).mp htdiv
      nlinarith
    exact nelsen2_tail_ratio θ hθ t hp0 ht1 hbound
  exact tendsto_const_nhds.congr' (heq.mono fun t ht => ht.symm)

/-- The Nelsen 2 lower-tail coefficient vanishes for every admissible parameter. -/
theorem hasLowerTailDependence_nelsen2 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen2 θ hθ).HasLowerTailDependence 0 := by
  let f : I → ℝ := fun t =>
    1 - (((1 - (t : ℝ)) ^ θ + (1 - (t : ℝ)) ^ θ) ^ θ⁻¹)
  have hval : f 0 < 0 := by
    have hθp : 0 < θ⁻¹ := inv_pos.mpr (by linarith)
    have hp : (1 : ℝ) < (2 : ℝ) ^ θ⁻¹ :=
      Real.one_lt_rpow (by norm_num) hθp
    dsimp [f]
    norm_num
    linarith
  have hcont : ContinuousAt f (0 : I) := by
    dsimp [f]
    fun_prop (disch := positivity)
  have hlim : Tendsto f (𝓝[>] (0 : I)) (𝓝 (f 0)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hneg : ∀ᶠ t : I in 𝓝[>] (0 : I), f t < 0 :=
    hlim.eventually (eventually_lt_nhds hval)
  have heq : ∀ᶠ t : I in 𝓝[>] (0 : I),
      (nelsen2 θ hθ).lowerTailRatio t = 0 := by
    filter_upwards [hneg, self_mem_nhdsWithin] with t ht ht0
    have htn : t ≠ 0 := ne_of_gt ht0
    simp only [lowerTailRatio, diagonal, nelsen2_cdf_full, htn, or_self,
      ↓reduceIte]
    change max 0 (f t) / (t : ℝ) = 0
    rw [max_eq_left (le_of_lt ht)]
    simp
  exact tendsto_const_nhds.congr' (heq.mono fun t ht => ht.symm)
end ProbabilityTheory.Copula