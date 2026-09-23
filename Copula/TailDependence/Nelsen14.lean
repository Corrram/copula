/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Nelsen
import Copula.TailDependence.Derivative

open Filter
open scoped unitInterval Topology

/-! # Exact lower and upper tail dependence of Nelsen 14 -/

namespace ProbabilityTheory.Copula

private theorem nelsen14_diagonal (θ : ℝ) (hθ : 1 ≤ θ) (t : I)
    (ht : 0 < (t : ℝ)) :
    (nelsen14 θ hθ).diagonal t =
      (1 + (2 : ℝ) ^ θ⁻¹ * ((t : ℝ) ^ (-θ⁻¹) - 1)) ^ (-θ) := by
  have htn : t ≠ 0 := ne_of_gt ht
  have hpow0 : 0 ≤ (t : ℝ) ^ (-θ⁻¹) - 1 := by
    have hneg : -θ⁻¹ ≤ 0 := by
      have hh : 0 < θ := by linarith
      exact neg_nonpos.mpr (inv_nonneg.mpr hh.le)
    have hh : 1 ≤ (t : ℝ) ^ (-θ⁻¹) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht t.property.2 hneg
    linarith
  have hpow : (((t : ℝ) ^ (-θ⁻¹) - 1) ^ θ +
      ((t : ℝ) ^ (-θ⁻¹) - 1) ^ θ) ^ θ⁻¹ =
      (2 : ℝ) ^ θ⁻¹ * ((t : ℝ) ^ (-θ⁻¹) - 1) := by
    rw [← two_mul, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hpow0 _),
      Real.rpow_rpow_inv hpow0 (by linarith : θ ≠ 0)]
  rw [diagonal, nelsen14_cdf_full]
  simp only [htn, or_self, ↓reduceIte]
  rw [hpow]




private theorem nelsen14_lower_ratio (θ : ℝ) (hθ : 1 ≤ θ) (t : I)
    (ht : 0 < (t : ℝ)) :
    (nelsen14 θ hθ).lowerTailRatio t =
      ((2 : ℝ) ^ θ⁻¹ + (1 - (2 : ℝ) ^ θ⁻¹) * (t : ℝ) ^ θ⁻¹) ^ (-θ) := by
  let a : ℝ := (2 : ℝ) ^ θ⁻¹
  let x : ℝ := (t : ℝ) ^ θ⁻¹
  have hx : 0 < x := Real.rpow_pos_of_pos ht _
  have hbase : 0 ≤ (t : ℝ) ^ (-θ⁻¹) - 1 := by
    have hneg : -θ⁻¹ ≤ 0 := by
      have hh : 0 < θ := by linarith
      exact neg_nonpos.mpr (inv_nonneg.mpr hh.le)
    have hh : 1 ≤ (t : ℝ) ^ (-θ⁻¹) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht t.property.2 hneg
    linarith
  have ha : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  have hb : 0 ≤ 1 + a * ((t : ℝ) ^ (-θ⁻¹) - 1) := by
    have hh := mul_nonneg ha.le hbase
    linarith
  have hc : 0 ≤ a + (1 - a) * x := by
    have he : 1 + a * ((t : ℝ) ^ (-θ⁻¹) - 1) =
        x⁻¹ * (a + (1 - a) * x) := by
      rw [show (t : ℝ) ^ (-θ⁻¹) = x⁻¹ by
        dsimp [x]; rw [← Real.rpow_neg ht.le]]
      field_simp
      ring
    have hh : 0 ≤ x * (1 + a * ((t : ℝ) ^ (-θ⁻¹) - 1)) :=
      mul_nonneg hx.le hb
    rw [he] at hh
    simpa [hx.ne'] using hh
  have he : 1 + a * ((t : ℝ) ^ (-θ⁻¹) - 1) =
      (t : ℝ) ^ (-θ⁻¹) * (a + (1 - a) * x) := by
    rw [show (t : ℝ) ^ (-θ⁻¹) = x⁻¹ by
      dsimp [x]; rw [← Real.rpow_neg ht.le]]
    field_simp
    ring
  rw [lowerTailRatio, nelsen14_diagonal θ hθ t ht]
  rw [← show a = (2 : ℝ) ^ θ⁻¹ from rfl, ← show x = (t : ℝ) ^ θ⁻¹ from rfl, he]
  rw [Real.mul_rpow (Real.rpow_nonneg ht.le _) hc]
  have htpow : ((t : ℝ) ^ (-θ⁻¹)) ^ (-θ) = (t : ℝ) := by
    rw [← Real.rpow_mul ht.le]
    have hh : (-θ⁻¹) * (-θ) = 1 := by
      have hne : θ ≠ 0 := by linarith
      field_simp
    rw [hh, Real.rpow_one]
  rw [htpow]
  field_simp




/-- Nelsen 14 has lower-tail coefficient one half for every finite parameter. -/
theorem hasLowerTailDependence_nelsen14 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen14 θ hθ).HasLowerTailDependence (1 / 2) := by
  let a : ℝ := (2 : ℝ) ^ θ⁻¹
  have hθpos : 0 < θ := by linarith
  have hinv : 0 < θ⁻¹ := inv_pos.mpr hθpos
  have ha : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  have hcoe : ContinuousAt (fun t : I => (t : ℝ)) (0 : I) :=
    continuous_subtype_val.continuousAt
  have hpow : ContinuousAt (fun t : I => (t : ℝ) ^ θ⁻¹) (0 : I) := by
    have hr : ContinuousAt (fun z : ℝ => z ^ θ⁻¹) 0 :=
      Real.continuousAt_rpow_const 0 θ⁻¹ (Or.inr hinv.le)
    exact @ContinuousAt.comp I ℝ ℝ _ _ _ (fun t : I => (t : ℝ)) (0 : I)
      (fun z : ℝ => z ^ θ⁻¹) hr hcoe
  have hb : ContinuousAt (fun t : I => a + (1 - a) * (t : ℝ) ^ θ⁻¹) (0 : I) := by
    fun_prop
  have hr : ContinuousAt (fun z : ℝ => z ^ (-θ)) a :=
    Real.continuousAt_rpow_const a (-θ) (Or.inl ha.ne')
  have hc : ContinuousAt (fun t : I =>
      (a + (1 - a) * (t : ℝ) ^ θ⁻¹) ^ (-θ)) (0 : I) := by
    have hr' : ContinuousAt (fun z : ℝ => z ^ (-θ))
        (a + (1 - a) * ((0 : I) : ℝ) ^ θ⁻¹) := by
      simpa [Real.zero_rpow hinv.ne'] using hr
    exact @ContinuousAt.comp I ℝ ℝ _ _ _
      (fun t : I => a + (1 - a) * (t : ℝ) ^ θ⁻¹) (0 : I)
      (fun z : ℝ => z ^ (-θ)) hr' hb
  have hlim : Tendsto (fun t : I =>
      (a + (1 - a) * (t : ℝ) ^ θ⁻¹) ^ (-θ))
      (𝓝[>] (0 : I)) (𝓝 (1 / 2)) := by
    have he : a ^ (-θ) = 1 / 2 := by
      dsimp [a]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hexp : θ⁻¹ * (-θ) = -1 := by
        field_simp
      rw [hexp, Real.rpow_neg_one]
      norm_num
    simpa [Real.zero_rpow hinv.ne', he] using hc.tendsto.mono_left nhdsWithin_le_nhds
  change Tendsto (nelsen14 θ hθ).lowerTailRatio (𝓝[>] (0 : I)) (𝓝 (1 / 2))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (nelsen14_lower_ratio θ hθ t ht).symm


private theorem nelsen14_diagonal_smooth_hasDerivAt_one (θ : ℝ) (hθ : 1 ≤ θ) :
    HasDerivAt (fun x : ℝ =>
      (1 + (2 : ℝ) ^ θ⁻¹ * (x ^ (-θ⁻¹) - 1)) ^ (-θ))
      ((2 : ℝ) ^ θ⁻¹) 1 := by
  let a : ℝ := (2 : ℝ) ^ θ⁻¹
  have hθpos : 0 < θ := by linarith
  have hp : HasDerivAt (fun x : ℝ => x ^ (-θ⁻¹)) (-θ⁻¹) 1 := by
    convert Real.hasDerivAt_rpow_const (p := -θ⁻¹) (Or.inl (by norm_num : (1 : ℝ) ≠ 0)) using 1; norm_num
  have hb : HasDerivAt (fun x : ℝ =>
      1 + a * (x ^ (-θ⁻¹) - 1)) (a * (-θ⁻¹)) 1 := by
    convert (hasDerivAt_const 1 (1 : ℝ)).add
      ((hp.sub_const 1).const_mul a) using 1; simp
  have hbase : (1 + a * ((1 : ℝ) ^ (-θ⁻¹) - 1)) ≠ 0 := by norm_num
  have hr := hb.rpow_const (p := -θ) (Or.inl hbase)
  convert hr using 1
  dsimp [a]
  simp only [Real.one_rpow, sub_self, mul_zero, add_zero]
  have hn : θ ≠ 0 := ne_of_gt hθpos
  field_simp

/-- Nelsen 14 has upper-tail coefficient 2−2^(1/θ) for every finite parameter. -/
theorem hasUpperTailDependence_nelsen14 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen14 θ hθ).HasUpperTailDependence (2 - (2 : ℝ) ^ θ⁻¹) := by
  let g : ℝ → ℝ := fun x =>
    (1 + (2 : ℝ) ^ θ⁻¹ * (x ^ (-θ⁻¹) - 1)) ^ (-θ)
  let f : ℝ → ℝ := fun x => if x = 0 then 0 else g x
  have hf : ∀ t : I, f t = (nelsen14 θ hθ).diagonal t := by
    intro t
    by_cases ht : t = 0
    · subst t
      simp [f, diagonal]
    · have htp : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1
        (Ne.symm (fun h => ht (Subtype.ext h)))
      simpa [f, g, ht] using (nelsen14_diagonal θ hθ t htp).symm
  have hevent : f =ᶠ[𝓝 (1 : ℝ)] g := by
    filter_upwards [eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0)] with x hx
    simp [f, hx]
  have hd : HasDerivWithinAt f ((2 : ℝ) ^ θ⁻¹) (Set.Icc 0 1) 1 :=
    ((nelsen14_diagonal_smooth_hasDerivAt_one θ hθ).congr_of_eventuallyEq hevent).hasDerivWithinAt
  exact hasUpperTailDependence_of_hasDerivWithinAt hf hd

end ProbabilityTheory.Copula
