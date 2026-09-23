/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Joe
import Copula.TailDependence.Derivative

/-! # Exact Joe tail dependence

Both limits hold for every finite θ ≥ 1, including the independence endpoint.
-/

open Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

private noncomputable def joeDiag (θ : ℝ) (t : ℝ) : ℝ :=
  1 - (((1 - t) ^ θ + (1 - t) ^ θ) - (1 - t) ^ θ * (1 - t) ^ θ) ^ θ⁻¹

private theorem joeDiag_eq (θ : ℝ) (hθ : 1 ≤ θ) (t : I) :
    joeDiag θ t = (joe θ hθ).diagonal t := by
  by_cases ht : t = 0
  · subst t
    simp [joeDiag, diagonal]
  rw [diagonal, joe_cdf_full]
  simp [joeDiag, ht]

private theorem joeDiag_hasDerivAt_zero (θ : ℝ) :
    HasDerivAt (joeDiag θ) 0 0 := by
  let g : ℝ → ℝ := fun t => (1 - t) ^ θ
  have hsub : HasDerivAt (fun t : ℝ => 1 - t) (-1) 0 := by
    convert (hasDerivAt_const 0 (1 : ℝ)).sub (hasDerivAt_id 0) using 1
    · ext t; rfl
    · norm_num
  have hg : HasDerivAt g (-θ) 0 := by
    have h := hsub.rpow_const (p := θ) (Or.inl (by norm_num : (1 - (0:ℝ)) ≠ 0))
    convert h using 1; norm_num [g]
  have hb : HasDerivAt (fun t => (g t + g t) - g t * g t) 0 0 := by
    have h := (hg.add hg).sub (hg.mul hg)
    convert h using 1
    dsimp [g]
    norm_num
  have hbase : (g 0 + g 0) - g 0 * g 0 ≠ 0 := by norm_num [g]
  have hp := hb.rpow_const (p := θ⁻¹) (Or.inl hbase)
  have hf := (hasDerivAt_const 0 (1 : ℝ)).sub hp
  convert hf using 1
  · ext t; simp [joeDiag, g]
  · norm_num

theorem hasLowerTailDependence_joe (θ : ℝ) (hθ : 1 ≤ θ) :
    (joe θ hθ).HasLowerTailDependence 0 := by
  exact hasLowerTailDependence_of_hasDerivWithinAt
    (joeDiag_eq θ hθ) (joeDiag_hasDerivAt_zero θ).hasDerivWithinAt


private theorem joe_upperTailRatio (θ : ℝ) (hθ : 1 ≤ θ) (t : I)
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    (joe θ hθ).upperTailRatio t =
      2 - (2 - (t : ℝ) ^ θ) ^ θ⁻¹ := by
  have hsymm : unitInterval.symm t ≠ 0 := by
    intro hz
    have h := congrArg (fun x : I => (x : ℝ)) hz
    simp only [unitInterval.coe_symm_eq] at h
    norm_num at h
    linarith
  have hθpos : 0 ≤ θ := by linarith
  have hpowle : (t : ℝ) ^ θ ≤ 1 := by
    simpa using Real.rpow_le_rpow t.property.1 t.property.2 hθpos
  have hbase : 0 ≤ 2 - (t : ℝ) ^ θ := by linarith
  have hpow : (((t : ℝ) ^ θ + (t : ℝ) ^ θ) -
      (t : ℝ) ^ θ * (t : ℝ) ^ θ) ^ θ⁻¹ =
      (t : ℝ) * (2 - (t : ℝ) ^ θ) ^ θ⁻¹ := by
    rw [show ((t : ℝ) ^ θ + (t : ℝ) ^ θ) -
        (t : ℝ) ^ θ * (t : ℝ) ^ θ =
        (t : ℝ) ^ θ * (2 - (t : ℝ) ^ θ) by ring,
      Real.mul_rpow (Real.rpow_nonneg t.property.1 _) hbase,
      Real.rpow_rpow_inv t.property.1 (by linarith : θ ≠ 0)]
  rw [upperTailRatio_eq, diagonal, joe_cdf_full]
  simp only [hsymm, or_self, ↓reduceIte, unitInterval.coe_symm_eq]
  rw [show 1 - (1 - (t : ℝ)) = (t : ℝ) by ring, hpow]
  have hne : (t : ℝ) ≠ 0 := ne_of_gt ht0
  field_simp
  ring

/-- Joe's upper-tail coefficient for every parameter, including θ = 1. -/
theorem hasUpperTailDependence_joe (θ : ℝ) (hθ : 1 ≤ θ) :
    (joe θ hθ).HasUpperTailDependence (2 - (2 : ℝ) ^ θ⁻¹) := by
  let f : I → ℝ := fun t => 2 - (2 - (t : ℝ) ^ θ) ^ θ⁻¹
  have hθpos : 0 < θ := by linarith
  have hcont : ContinuousAt f (0 : I) := by
    dsimp [f]
    fun_prop (disch := positivity)
  have hval : f 0 = 2 - (2 : ℝ) ^ θ⁻¹ := by
    simp [f, Real.zero_rpow hθpos.ne']
  have hlim : Tendsto f (𝓝[>] (0 : I)) (𝓝 (2 - (2 : ℝ) ^ θ⁻¹)) := by
    rw [← hval]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hco : Tendsto (fun t : I => (t : ℝ)) (𝓝[>] (0 : I)) (𝓝 (0 : ℝ)) :=
    (continuous_subtype_val.tendsto (0 : I)).mono_left nhdsWithin_le_nhds
  have hlt : ∀ᶠ t : I in 𝓝[>] (0 : I), (t : ℝ) < 1 :=
    hco.eventually (eventually_lt_nhds (by norm_num))
  have hpos : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < (t : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  have heq : ∀ᶠ t : I in 𝓝[>] (0 : I),
      (joe θ hθ).upperTailRatio t = f t := by
    filter_upwards [hlt, hpos] with t ht hp
    exact joe_upperTailRatio θ hθ t hp ht
  exact hlim.congr' (heq.mono fun t ht => ht.symm)
end ProbabilityTheory.Copula