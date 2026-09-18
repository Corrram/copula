/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.Properties
import Copula.Dependence.Examples

/-! # Positive quadrant dependence of ordinal sums -/

open scoped unitInterval

namespace ProbabilityTheory.Copula

open OrdinalSum

theorem IsPQD.ordinalSum {C D : Copula 2} (hC : C.IsPQD) (hD : D.IsPQD) (a : I) :
    (C.ordinalSum D a).IsPQD := by
  intro u v
  rcases le_total u a with hu | hu <;> rcases le_total v a with hv | hv
  · rw [cdf_ordinalSum_lower C D a u v hu hv]
    have heU : (a : ℝ) * lowerCoord a u = u := by
      rw [weight_lowerCoord, min_eq_right (show (u : ℝ) ≤ a from hu)]
    have heV : (a : ℝ) * lowerCoord a v = v := by
      rw [weight_lowerCoord, min_eq_right (show (v : ℝ) ≤ a from hv)]
    have hv' : (v : ℝ) ≤ lowerCoord a v := by
      rw [← heV]
      exact mul_le_of_le_one_left (lowerCoord a v).property.1 a.property.2
    calc
      (u : ℝ) * v ≤ (u : ℝ) * lowerCoord a v := mul_le_mul_of_nonneg_left hv' u.property.1
      _ = (a : ℝ) * ((lowerCoord a u : ℝ) * lowerCoord a v) := by rw [← heU]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC _ _) a.property.1
  · rw [cdf_ordinalSum_lower_upper C D a u v hu hv]
    exact mul_le_of_le_one_right u.property.1 v.property.2
  · rw [cdf_ordinalSum_upper_lower C D a u v hu hv]
    exact mul_le_of_le_one_left v.property.1 u.property.2
  · rw [cdf_ordinalSum_upper C D a u v hu hv]
    have heU : (u : ℝ) = a + (1 - (a : ℝ)) * upperCoord a u := by
      rw [weight_upperCoord, max_eq_right (sub_nonneg.mpr (show (a : ℝ) ≤ u from hu))]
      ring
    have heV : (v : ℝ) = a + (1 - (a : ℝ)) * upperCoord a v := by
      rw [weight_upperCoord, max_eq_right (sub_nonneg.mpr (show (a : ℝ) ≤ v from hv))]
      ring
    have hn := mul_nonneg (mul_nonneg a.property.1 (sub_nonneg.mpr a.property.2))
      (mul_nonneg (sub_nonneg.mpr (upperCoord a u).property.2)
        (sub_nonneg.mpr (upperCoord a v).property.2))
    calc
      (u : ℝ) * v ≤ a + (1 - (a : ℝ)) * ((upperCoord a u : ℝ) * upperCoord a v) := by
        rw [heU, heV]
        nlinarith only [hn]
      _ ≤ _ := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (hD _ _) (sub_nonneg.mpr a.property.2))

theorem isPQD_ordinalSum_independence (a : I) :
    ((independence 2).ordinalSum (independence 2) a).IsPQD :=
  isPQD_independence.ordinalSum isPQD_independence a

end ProbabilityTheory.Copula
