/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Classical.Bivariate
import Mathlib.Topology.Order.ProjIcc

/-! # Coordinates for two-block ordinal sums

The clipped inverse affine maps are defined even when a block has zero
length. Its weight is then zero in the ordinal-sum CDF.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.OrdinalSum

/-- Rescale the lower interval `[0,a]`, clipping values above it. -/
noncomputable def lowerCoord (a u : I) : I := projIcc 0 1 zero_le_one ((u : ℝ) / a)

/-- Rescale the upper interval `[a,1]`, clipping values below it. -/
noncomputable def upperCoord (a u : I) : I := projIcc 0 1 zero_le_one (((u : ℝ) - a) / (1 - a))

theorem lowerCoord_mono (a : I) : Monotone (lowerCoord a) := by
  intro u v huv
  exact monotone_projIcc zero_le_one (div_le_div_of_nonneg_right huv a.property.1)

theorem upperCoord_mono (a : I) : Monotone (upperCoord a) := by
  intro u v huv
  change (u : ℝ) ≤ v at huv
  exact monotone_projIcc zero_le_one
    (div_le_div_of_nonneg_right (sub_le_sub_right huv _) (sub_nonneg.mpr a.property.2))

theorem continuous_lowerCoord (a : I) : Continuous (lowerCoord a) := by
  unfold lowerCoord
  exact continuous_projIcc.comp (continuous_subtype_val.div_const _)

theorem continuous_upperCoord (a : I) : Continuous (upperCoord a) := by
  unfold upperCoord
  exact continuous_projIcc.comp ((continuous_subtype_val.sub continuous_const).div_const _)

@[simp] theorem lowerCoord_zero (a : I) : lowerCoord a 0 = 0 := by
  simp [lowerCoord]

@[simp] theorem upperCoord_of_le (a u : I) (hu : u ≤ a) : upperCoord a u = 0 := by
  exact projIcc_of_le_left zero_le_one
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu) (sub_nonneg.mpr a.property.2))

@[simp] theorem upperCoord_zero (a : I) : upperCoord a 0 = 0 := upperCoord_of_le a 0 a.property.1

theorem lowerCoord_of_ge (a u : I) (ha : 0 < a) (hu : a ≤ u) : lowerCoord a u = 1 := by
  exact projIcc_of_right_le zero_le_one ((one_le_div ha).2 hu)

theorem coe_lowerCoord_of_le (a u : I) (ha : 0 < a) (hu : u ≤ a) :
    (lowerCoord a u : ℝ) = (u : ℝ) / a := by
  rw [lowerCoord, projIcc_of_mem zero_le_one ⟨div_nonneg u.property.1 ha.le, (div_le_one ha).2 hu⟩]

theorem coe_upperCoord_of_ge (a u : I) (ha : a < 1) (hu : a ≤ u) :
    (upperCoord a u : ℝ) = ((u : ℝ) - a) / (1 - a) := by
  change (a : ℝ) ≤ u at hu
  have hp : 0 < 1 - (a : ℝ) := sub_pos.mpr ha
  rw [upperCoord, projIcc_of_mem zero_le_one ⟨div_nonneg (sub_nonneg.mpr hu) hp.le,
    (div_le_one hp).2 (sub_le_sub_right u.property.2 _)⟩]

@[simp] theorem lowerCoord_zero_left (u : I) : lowerCoord 0 u = 0 := by simp [lowerCoord]

@[simp] theorem upperCoord_one_left (u : I) : upperCoord 1 u = 0 := by simp [upperCoord]

@[simp] theorem lowerCoord_one_left (u : I) : lowerCoord 1 u = u := by simp [lowerCoord]

@[simp] theorem upperCoord_zero_left (u : I) : upperCoord 0 u = u := by simp [upperCoord]

theorem lowerCoord_one (a : I) (ha : 0 < a) : lowerCoord a 1 = 1 :=
  lowerCoord_of_ge a 1 ha a.property.2

theorem upperCoord_one (a : I) (ha : a < 1) : upperCoord a 1 = 1 := by
  apply Subtype.ext
  rw [coe_upperCoord_of_ge a 1 ha a.property.2]
  simp [ne_of_gt (sub_pos.mpr ha : 0 < 1 - (a : ℝ))]

theorem weight_lowerCoord (a u : I) : (a : ℝ) * lowerCoord a u = min (a : ℝ) u := by
  by_cases hz : a = 0
  · subst a
    simp [u.property.1]
  have ha : 0 < a := lt_of_le_of_ne a.property.1 (Ne.symm hz)
  have ha' : (0 : ℝ) < a := ha
  rcases le_total u a with hu | hu
  · rw [coe_lowerCoord_of_le a u ha hu, min_eq_right (show (u : ℝ) ≤ a from hu)]
    field_simp [ha'.ne']
  · rw [lowerCoord_of_ge a u ha hu, min_eq_left (show (a : ℝ) ≤ u from hu)]
    simp

theorem weight_upperCoord (a u : I) :
    (1 - (a : ℝ)) * upperCoord a u = max 0 ((u : ℝ) - a) := by
  by_cases hz : a = 1
  · subst a
    simp [sub_nonpos.mpr u.property.2]
  have ha : a < 1 := lt_of_le_of_ne a.property.2 hz
  have hp : (0 : ℝ) < 1 - a := sub_pos.mpr ha
  rcases le_total u a with hu | hu
  · rw [upperCoord_of_le a u hu, max_eq_left (sub_nonpos.mpr (show (u : ℝ) ≤ a from hu))]
    simp
  · rw [coe_upperCoord_of_ge a u ha hu,
      max_eq_right (sub_nonneg.mpr (show (a : ℝ) ≤ u from hu))]
    field_simp [hp.ne']

theorem weighted_coords (a u : I) :
    (a : ℝ) * lowerCoord a u + (1 - (a : ℝ)) * upperCoord a u = u := by
  rw [weight_lowerCoord, weight_upperCoord]
  rcases le_total (u : ℝ) (a : ℝ) with hu | hu
  · rw [min_eq_right hu, max_eq_left (sub_nonpos.mpr hu), add_zero]
  · rw [min_eq_left hu, max_eq_right (sub_nonneg.mpr hu)]
    ring

/-- Embed a unit coordinate into the lower interval. -/
def lowerEmbed (a u : I) : I := ⟨(a : ℝ) * u, mul_nonneg a.property.1 u.property.1,
  (mul_le_mul_of_nonneg_left u.property.2 a.property.1).trans (by simpa using a.property.2)⟩

/-- Embed a unit coordinate into the upper interval. -/
def upperEmbed (a u : I) : I := ⟨(a : ℝ) + (1 - (a : ℝ)) * u, by
  have h := mul_nonneg (sub_nonneg.mpr a.property.2) u.property.1
  constructor
  · linarith [a.property.1]
  · nlinarith [mul_le_mul_of_nonneg_left u.property.2 (sub_nonneg.mpr a.property.2)]⟩

theorem lowerEmbed_le (a u : I) : lowerEmbed a u ≤ a := by
  exact (mul_le_mul_of_nonneg_left u.property.2 a.property.1).trans_eq (mul_one _)

theorem le_upperEmbed (a u : I) : a ≤ upperEmbed a u := by
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr a.property.2) u.property.1)

theorem lowerCoord_lowerEmbed (a u : I) (ha : 0 < a) : lowerCoord a (lowerEmbed a u) = u := by
  apply Subtype.ext
  rw [coe_lowerCoord_of_le a _ ha (lowerEmbed_le a u)]
  change (a : ℝ) * u / a = u
  have hp : (0 : ℝ) < a := ha
  field_simp [hp.ne']

theorem upperCoord_upperEmbed (a u : I) (ha : a < 1) : upperCoord a (upperEmbed a u) = u := by
  apply Subtype.ext
  rw [coe_upperCoord_of_ge a _ ha (le_upperEmbed a u)]
  change ((a : ℝ) + (1 - (a : ℝ)) * u - a) / (1 - a) = u
  have hp : (0 : ℝ) < 1 - a := sub_pos.mpr ha
  field_simp [hp.ne']
  ring

end ProbabilityTheory.Copula.OrdinalSum
