/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.TailDependence.Quadrant
import Copula.TailDependence.Derivative
import Copula.Dependence.ClaytonClassification

/-! # Exact lower and upper tail dependence of the signed Clayton family -/

open Real Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

private theorem clayton_lower_ratio_eq (θ : ℝ) (hθ : 0 < θ) (t : I)
    (ht : 0 < (t : ℝ)) :
    (clayton 2 θ hθ).lowerTailRatio t = (2 - (t : ℝ) ^ θ) ^ (-1 / θ) := by
  have htpow : 0 < (t : ℝ) ^ (-θ) := Real.rpow_pos_of_pos ht _
  have hθpow : (t : ℝ) ^ θ ≤ 1 :=
    Real.rpow_le_one ht.le t.property.2 hθ.le
  have hb : 0 ≤ 2 - (t : ℝ) ^ θ := by linarith
  have hi : (t : ℝ) ^ (-θ) * (t : ℝ) ^ θ = 1 := by
    rw [← Real.rpow_add ht]
    simp
  have hmul : (t : ℝ) ^ (-θ) * (2 - (t : ℝ) ^ θ) =
      (t : ℝ) ^ (-θ) + (t : ℝ) ^ (-θ) - 1 := by
    nlinarith
  have hpow : ((t : ℝ) ^ (-θ)) ^ (-1 / θ) = (t : ℝ) := by
    rw [← Real.rpow_mul ht.le]
    have he : (-θ) * (-1 / θ) = 1 := by field_simp
    rw [he, Real.rpow_one]
  rw [lowerTailRatio, diagonal, cdf_clayton_two_pos θ hθ t t ht ht]
  rw [← hmul, Real.mul_rpow htpow.le hb, hpow]
  field_simp [ht.ne']
/-- The lower-tail coefficient of positive Clayton is `2 ^ (-1 / θ)`. -/
theorem hasLowerTailDependence_clayton_positive (θ : ℝ) (hθ : 0 < θ) :
    (clayton 2 θ hθ).HasLowerTailDependence (2 ^ (-1 / θ)) := by
  have hcoe : ContinuousAt (fun t : I => (t : ℝ)) (0 : I) :=
    continuous_subtype_val.continuousAt
  have hpow : ContinuousAt (fun t : I => (t : ℝ) ^ θ) (0 : I) := by
    have hr : ContinuousAt (fun z : ℝ => z ^ θ) 0 :=
      Real.continuousAt_rpow_const 0 θ (Or.inr hθ.le)
    exact @ContinuousAt.comp I ℝ ℝ _ _ _ (fun t : I => (t : ℝ)) (0 : I)
      (fun z : ℝ => z ^ θ) hr hcoe
  have hb : ContinuousAt (fun t : I => 2 - (t : ℝ) ^ θ) (0 : I) := by
    fun_prop
  have hroot : ContinuousAt (fun z : ℝ => z ^ (-1 / θ)) (2 - ((0 : I) : ℝ) ^ θ) := by
    simpa [Real.zero_rpow hθ.ne'] using
      (Real.continuousAt_rpow_const 2 (-1 / θ) (Or.inl (by norm_num)))
  have hc : ContinuousAt (fun t : I => (2 - (t : ℝ) ^ θ) ^ (-1 / θ)) (0 : I) := by
    exact @ContinuousAt.comp I ℝ ℝ _ _ _ (fun t : I => 2 - (t : ℝ) ^ θ) (0 : I)
      (fun z : ℝ => z ^ (-1 / θ)) hroot hb
  have htend : Tendsto (fun t : I => (2 - (t : ℝ) ^ θ) ^ (-1 / θ))
      (𝓝[>] (0 : I)) (𝓝 (2 ^ (-1 / θ))) := by
    simpa [Real.zero_rpow hθ.ne'] using hc.tendsto.mono_left nhdsWithin_le_nhds
  unfold HasLowerTailDependence
  apply htend.congr'
  filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < t)] with t ht
  exact (clayton_lower_ratio_eq θ hθ t (show 0 < (t : ℝ) from ht)).symm
/-- Every admissible negative Clayton copula has zero lower-tail dependence. -/
theorem hasLowerTailDependence_clayton_negative (θ : ℝ) (hθ : -1 ≤ θ)
    (hn : θ < 0) : (claytonNegative θ hθ hn).HasLowerTailDependence 0 :=
  isNQD_hasLowerTailDependence_zero (isNQD_clayton_negative θ hθ hn)

/-- Every admissible negative Clayton copula has zero upper-tail dependence. -/
theorem hasUpperTailDependence_clayton_negative (θ : ℝ) (hθ : -1 ≤ θ)
    (hn : θ < 0) : (claytonNegative θ hθ hn).HasUpperTailDependence 0 :=
  isNQD_hasUpperTailDependence_zero (isNQD_clayton_negative θ hθ hn)
private theorem clayton_diagonal_eq (θ : ℝ) (hθ : 0 < θ) (t : I) :
    (t : ℝ) * (2 - (t : ℝ) ^ θ) ^ (-1 / θ) = (clayton 2 θ hθ).diagonal t := by
  by_cases ht0 : t = 0
  · subst t
    simp [diagonal]
  have ht : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1
    (Ne.symm (fun h => ht0 (Subtype.ext h)))
  have hr := clayton_lower_ratio_eq θ hθ t ht
  unfold lowerTailRatio at hr
  calc
    (t : ℝ) * (2 - (t : ℝ) ^ θ) ^ (-1 / θ) =
        (2 - (t : ℝ) ^ θ) ^ (-1 / θ) * (t : ℝ) := mul_comm _ _
    _ = (clayton 2 θ hθ).diagonal t := ((div_eq_iff ht.ne').mp hr).symm

private theorem clayton_diagonal_smooth_hasDerivAt_one (θ : ℝ) (hθ : 0 < θ) :
    HasDerivAt (fun t : ℝ => t * (2 - t ^ θ) ^ (-1 / θ)) 2 1 := by
  have hp : HasDerivAt (fun t : ℝ => t ^ θ) (θ * (1 : ℝ) ^ (θ - 1)) 1 :=
    Real.hasDerivAt_rpow_const (Or.inl (by norm_num))
  have hb : HasDerivAt (fun t : ℝ => 2 - t ^ θ)
      (-(θ * (1 : ℝ) ^ (θ - 1))) 1 := by
    convert (hasDerivAt_const 1 (2 : ℝ)).sub hp using 1; ring
  have hbase : 0 < 2 - (1 : ℝ) ^ θ := by norm_num
  have hr := hb.rpow_const (p := -1 / θ) (Or.inl hbase.ne')
  have hm := (hasDerivAt_id 1).mul hr
  convert hm using 1
  · ext t; rfl
  · norm_num
    field_simp [hθ.ne']
    ring

/-- Positive Clayton has no upper-tail dependence. -/
theorem hasUpperTailDependence_clayton_positive (θ : ℝ) (hθ : 0 < θ) :
    (clayton 2 θ hθ).HasUpperTailDependence 0 := by
  have hd : HasDerivWithinAt (fun t : ℝ => t * (2 - t ^ θ) ^ (-1 / θ)) 2
      (Set.Icc 0 1) 1 :=
    (clayton_diagonal_smooth_hasDerivAt_one θ hθ).hasDerivWithinAt
  simpa using hasUpperTailDependence_of_hasDerivWithinAt
    (clayton_diagonal_eq θ hθ) hd
end ProbabilityTheory.Copula
