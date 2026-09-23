/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Nelsen
import Copula.TailDependence.Derivative

open Filter
open scoped unitInterval Topology

/-! # Exact lower and upper tail dependence of Genest–Ghoudi -/

namespace ProbabilityTheory.Copula

private theorem genestGhoudi_diagonal (θ : ℝ) (hθ : 1 ≤ θ) (t : I) :
    (genestGhoudi θ hθ).diagonal t =
      (max 0 (1 - (2 : ℝ) ^ θ⁻¹ * (1 - (t : ℝ) ^ θ⁻¹))) ^ θ := by
  have hθpos : 0 < θ := by linarith
  have hinv : 0 < θ⁻¹ := inv_pos.mpr hθpos
  have ha : 1 < (2 : ℝ) ^ θ⁻¹ :=
    Real.one_lt_rpow (by norm_num) hinv
  by_cases ht : t = 0
  · subst t
    rw [diagonal, genestGhoudi_cdf_full]
    simp [Real.zero_rpow hinv.ne', Real.zero_rpow hθpos.ne', max_eq_left (by linarith : 1 - (2 : ℝ) ^ θ⁻¹ ≤ 0)]
  · have hpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1
      (Ne.symm (fun h => ht (Subtype.ext h)))
    have hp : 0 ≤ 1 - (t : ℝ) ^ θ⁻¹ := by
      have hle : (t : ℝ) ^ θ⁻¹ ≤ 1 :=
        Real.rpow_le_one hpos.le t.property.2 hinv.le
      linarith
    have hnorm : (((1 - (t : ℝ) ^ θ⁻¹) ^ θ +
        (1 - (t : ℝ) ^ θ⁻¹) ^ θ) ^ θ⁻¹) =
        (2 : ℝ) ^ θ⁻¹ * (1 - (t : ℝ) ^ θ⁻¹) := by
      rw [← two_mul, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hp _),
        Real.rpow_rpow_inv hp hθpos.ne']
    rw [diagonal, genestGhoudi_cdf_full]
    simp only [ht, or_self, ↓reduceIte]
    rw [hnorm]


/-- The Genest–Ghoudi lower-tail coefficient vanishes for all finite θ≥1. -/
theorem hasLowerTailDependence_genestGhoudi (θ : ℝ) (hθ : 1 ≤ θ) :
    (genestGhoudi θ hθ).HasLowerTailDependence 0 := by
  let a : ℝ := (2 : ℝ) ^ θ⁻¹
  let f : I → ℝ := fun t => 1 - a * (1 - (t : ℝ) ^ θ⁻¹)
  have hθpos : 0 < θ := by linarith
  have hinv : 0 < θ⁻¹ := inv_pos.mpr hθpos
  have ha : 1 < a := Real.one_lt_rpow (by norm_num) hinv
  have hval : f 0 < 0 := by
    dsimp [f]
    simp only [Real.zero_rpow hinv.ne']
    linarith
  have hcont : ContinuousAt f (0 : I) := by
    dsimp [f]
    fun_prop (disch := positivity)
  have hlim : Tendsto f (𝓝[>] (0 : I)) (𝓝 (f 0)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hneg : ∀ᶠ t : I in 𝓝[>] (0 : I), f t < 0 :=
    hlim.eventually (eventually_lt_nhds hval)
  have heq : ∀ᶠ t : I in 𝓝[>] (0 : I),
      (genestGhoudi θ hθ).lowerTailRatio t = 0 := by
    filter_upwards [hneg] with t ht
    rw [lowerTailRatio, genestGhoudi_diagonal θ hθ t]
    change (max 0 (f t)) ^ θ / (t : ℝ) = 0
    rw [max_eq_left (le_of_lt ht)]
    simp [Real.zero_rpow hθpos.ne']
  exact tendsto_const_nhds.congr' (heq.mono fun t ht => ht.symm)


private theorem genestGhoudi_diagonal_smooth_hasDerivAt_one (θ : ℝ) (hθ : 1 ≤ θ) :
    HasDerivAt (fun x : ℝ =>
      (1 - (2 : ℝ) ^ θ⁻¹ * (1 - x ^ θ⁻¹)) ^ θ)
      ((2 : ℝ) ^ θ⁻¹) 1 := by
  let a : ℝ := (2 : ℝ) ^ θ⁻¹
  have hθpos : 0 < θ := by linarith
  have hp : HasDerivAt (fun x : ℝ => x ^ θ⁻¹) θ⁻¹ 1 := by
    convert Real.hasDerivAt_rpow_const (p := θ⁻¹) (Or.inl (by norm_num : (1 : ℝ) ≠ 0)) using 1
    norm_num
  have hb : HasDerivAt (fun x : ℝ => 1 - a * (1 - x ^ θ⁻¹))
      (a * θ⁻¹) 1 := by
    convert (hasDerivAt_const 1 (1 : ℝ)).sub
      ((hp.const_sub 1).const_mul a) using 1
    ring
  have hbase : (1 - a * (1 - (1 : ℝ) ^ θ⁻¹)) ≠ 0 := by norm_num
  have hr := hb.rpow_const (p := θ) (Or.inl hbase)
  convert hr using 1
  dsimp [a]
  simp only [Real.one_rpow, sub_self, mul_zero, sub_zero]
  have hn : θ ≠ 0 := ne_of_gt hθpos
  field_simp

/-- The Genest–Ghoudi upper-tail coefficient for all finite θ≥1. -/
theorem hasUpperTailDependence_genestGhoudi (θ : ℝ) (hθ : 1 ≤ θ) :
    (genestGhoudi θ hθ).HasUpperTailDependence (2 - (2 : ℝ) ^ θ⁻¹) := by
  let a : ℝ := (2 : ℝ) ^ θ⁻¹
  let f : ℝ → ℝ := fun x =>
    (max 0 (1 - a * (1 - x ^ θ⁻¹))) ^ θ
  let g : ℝ → ℝ := fun x =>
    (1 - a * (1 - x ^ θ⁻¹)) ^ θ
  have hf : ∀ t : I, f t = (genestGhoudi θ hθ).diagonal t := by
    intro t
    exact (genestGhoudi_diagonal θ hθ t).symm
  have hcont : ContinuousAt (fun x : ℝ => 1 - a * (1 - x ^ θ⁻¹)) 1 := by
    fun_prop (disch := positivity)
  have hpos : ∀ᶠ x : ℝ in 𝓝 (1 : ℝ), 0 < 1 - a * (1 - x ^ θ⁻¹) := by
    have hlim : Tendsto (fun x : ℝ => 1 - a * (1 - x ^ θ⁻¹)) (𝓝 1) (𝓝 1) := by
      simpa using hcont.tendsto
    exact hlim.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  have hevent : f =ᶠ[𝓝 (1 : ℝ)] g := by
    filter_upwards [hpos] with x hx
    simp [f, g, max_eq_right hx.le]
  have hd : HasDerivWithinAt f ((2 : ℝ) ^ θ⁻¹) (Set.Icc 0 1) 1 :=
    ((genestGhoudi_diagonal_smooth_hasDerivAt_one θ hθ).congr_of_eventuallyEq hevent).hasDerivWithinAt
  exact hasUpperTailDependence_of_hasDerivWithinAt hf hd

end ProbabilityTheory.Copula
