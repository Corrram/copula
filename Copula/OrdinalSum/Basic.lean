/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.Rescale
import Copula.Dependence.Basic

/-! # Binary ordinal sums of bivariate copulas

The first copula occupies `[0,a]²`, the second occupies `[a,1]²`, and the
CDF on the two off-diagonal rectangles is `min(u,v)`. The construction
includes `a=0` and `a=1`. See Nelsen, second edition, §3.2.2.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

open OrdinalSum

@[simp] theorem cdf_two_zero_right (C : Copula 2) (u : I) : C.cdf ![u, 0] = 0 :=
  C.cdf_eq_zero_of_coord_eq_zero _ 1 rfl

/-- An endpoint-safe expression for the ordinal-sum CDF. -/
noncomputable def ordinalSumCDF (C D : Copula 2) (a u v : I) : ℝ :=
  (a : ℝ) * C.cdf ![lowerCoord a u, lowerCoord a v] +
    (1 - (a : ℝ)) * D.cdf ![upperCoord a u, upperCoord a v]

theorem isClassical_ordinalSumCDF (C D : Copula 2) (a : I) :
    IsClassical (fun u : Fin 2 → I => ordinalSumCDF C D a (u 0) (u 1)) := by
  apply IsClassical.ofBivariate _ (by intro v; simp [ordinalSumCDF])
    (by intro u; simp [ordinalSumCDF])
  · intro v
    by_cases ha0 : a = 0
    · simp [ordinalSumCDF, ha0]
    by_cases ha1 : a = 1
    · simp [ordinalSumCDF, ha1]
    have hp : 0 < a := lt_of_le_of_ne a.property.1 (Ne.symm ha0)
    have hl : a < 1 := lt_of_le_of_ne a.property.2 ha1
    simpa [ordinalSumCDF, lowerCoord_one a hp, upperCoord_one a hl] using weighted_coords a v
  · intro u
    by_cases ha0 : a = 0
    · simp [ordinalSumCDF, ha0]
    by_cases ha1 : a = 1
    · simp [ordinalSumCDF, ha1]
    have hp : 0 < a := lt_of_le_of_ne a.property.1 (Ne.symm ha0)
    have hl : a < 1 := lt_of_le_of_ne a.property.2 ha1
    simpa [ordinalSumCDF, lowerCoord_one a hp, upperCoord_one a hl] using weighted_coords a u
  · intro u v s t huv hst
    have hc := C.rectangleIncrement_cdf_nonneg ![lowerCoord a u, lowerCoord a s]
      ![lowerCoord a v, lowerCoord a t] (by
        intro i; fin_cases i
        · exact lowerCoord_mono a huv
        · exact lowerCoord_mono a hst)
    have hd := D.rectangleIncrement_cdf_nonneg ![upperCoord a u, upperCoord a s]
      ![upperCoord a v, upperCoord a t] (by
        intro i; fin_cases i
        · exact upperCoord_mono a huv
        · exact upperCoord_mono a hst)
    simp only [rectangleIncrement_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hc hd
    have he := add_nonneg (mul_nonneg a.property.1 hc)
      (mul_nonneg (sub_nonneg.mpr a.property.2) hd)
    unfold ordinalSumCDF
    nlinarith only [he]

/-- Place `C` below the split `a` and `D` above it, with perfectly ordered block labels. -/
noncomputable def ordinalSum (C D : Copula 2) (a : I) : Copula 2 :=
  ofClassical _ (isClassical_ordinalSumCDF C D a)

@[simp] theorem cdf_ordinalSum (C D : Copula 2) (a : I) (u : Fin 2 → I) :
    (C.ordinalSum D a).cdf u = ordinalSumCDF C D a (u 0) (u 1) :=
  congrFun (cdf_ofClassical _ _) u

@[simp] theorem ordinalSum_zero (C D : Copula 2) : C.ordinalSum D 0 = D := by
  apply ext_cdf
  intro u
  simp only [cdf_ordinalSum, ordinalSumCDF, lowerCoord_zero_left, upperCoord_zero_left]
  have he : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
  simp [he]

@[simp] theorem ordinalSum_one (C D : Copula 2) : C.ordinalSum D 1 = C := by
  apply ext_cdf
  intro u
  simp only [cdf_ordinalSum, ordinalSumCDF, lowerCoord_one_left, upperCoord_one_left]
  have he : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
  simp [he]

theorem cdf_ordinalSum_lower (C D : Copula 2) (a u v : I) (hu : u ≤ a) (hv : v ≤ a) :
    (C.ordinalSum D a).cdf ![u, v] = (a : ℝ) * C.cdf ![lowerCoord a u, lowerCoord a v] := by
  simp [ordinalSumCDF, upperCoord_of_le a u hu, upperCoord_of_le a v hv]

theorem cdf_ordinalSum_upper (C D : Copula 2) (a u v : I) (hu : a ≤ u) (hv : a ≤ v) :
    (C.ordinalSum D a).cdf ![u, v] =
      (a : ℝ) + (1 - (a : ℝ)) * D.cdf ![upperCoord a u, upperCoord a v] := by
  by_cases hz : a = 0
  · simp [hz]
  have ha : 0 < a := lt_of_le_of_ne a.property.1 (Ne.symm hz)
  simp [ordinalSumCDF, lowerCoord_of_ge a u ha hu, lowerCoord_of_ge a v ha hv]

theorem cdf_ordinalSum_lower_upper (C D : Copula 2) (a u v : I) (hu : u ≤ a) (hv : a ≤ v) :
    (C.ordinalSum D a).cdf ![u, v] = u := by
  by_cases hz : a = 0
  · have hu0 : u = 0 := le_antisymm (hu.trans_eq hz) u.property.1
    simp [hu0]
  have ha : 0 < a := lt_of_le_of_ne a.property.1 (Ne.symm hz)
  simp [ordinalSumCDF, lowerCoord_of_ge a v ha hv, upperCoord_of_le a u hu,
    weight_lowerCoord, min_eq_right (show (u : ℝ) ≤ a from hu)]

theorem cdf_ordinalSum_upper_lower (C D : Copula 2) (a u v : I) (hu : a ≤ u) (hv : v ≤ a) :
    (C.ordinalSum D a).cdf ![u, v] = v := by
  by_cases hz : a = 0
  · have hv0 : v = 0 := le_antisymm (hv.trans_eq hz) v.property.1
    simp [hv0]
  have ha : 0 < a := lt_of_le_of_ne a.property.1 (Ne.symm hz)
  simp [ordinalSumCDF, lowerCoord_of_ge a u ha hu, upperCoord_of_le a v hv,
    weight_lowerCoord, min_eq_right (show (v : ℝ) ≤ a from hv)]

@[simp] theorem cdf_ordinalSum_split (C D : Copula 2) (a : I) :
    (C.ordinalSum D a).cdf ![a, a] = a := by
  rw [cdf_ordinalSum_upper C D a a a le_rfl le_rfl]
  simp

theorem cdf_ordinalSum_lowerEmbed (C D : Copula 2) (a u v : I) (ha : 0 < a) :
    (C.ordinalSum D a).cdf ![lowerEmbed a u, lowerEmbed a v] = (a : ℝ) * C.cdf ![u, v] := by
  rw [cdf_ordinalSum_lower C D a _ _ (lowerEmbed_le a u) (lowerEmbed_le a v),
    lowerCoord_lowerEmbed a u ha, lowerCoord_lowerEmbed a v ha]

theorem cdf_ordinalSum_upperEmbed (C D : Copula 2) (a u v : I) (ha : a < 1) :
    (C.ordinalSum D a).cdf ![upperEmbed a u, upperEmbed a v] =
      (a : ℝ) + (1 - (a : ℝ)) * D.cdf ![u, v] := by
  rw [cdf_ordinalSum_upper C D a _ _ (le_upperEmbed a u) (le_upperEmbed a v),
    upperCoord_upperEmbed a u ha, upperCoord_upperEmbed a v ha]

end ProbabilityTheory.Copula
