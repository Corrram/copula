/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.Cut

/-! # Extracting the copulas below and above a diagonal cut

At a diagonal fixed point, restriction to either positive-length square
and affine rescaling gives a copula. The lower and upper constructions
only require their own block to have positive length.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace OrdinalSum

theorem lowerEmbed_mono (a : I) : Monotone (lowerEmbed a) := by
  intro u v h
  exact mul_le_mul_of_nonneg_left h a.property.1

theorem upperEmbed_mono (a : I) : Monotone (upperEmbed a) := by
  intro u v h
  change (u : ℝ) ≤ v at h
  change (a : ℝ) + (1 - (a : ℝ)) * u ≤ (a : ℝ) + (1 - (a : ℝ)) * v
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h (sub_nonneg.mpr a.property.2))

@[simp] theorem lowerEmbed_zero (a : I) : lowerEmbed a 0 = 0 := by
  apply Subtype.ext
  simp [lowerEmbed]

@[simp] theorem lowerEmbed_one (a : I) : lowerEmbed a 1 = a := by
  apply Subtype.ext
  simp [lowerEmbed]

@[simp] theorem upperEmbed_zero (a : I) : upperEmbed a 0 = a := by
  apply Subtype.ext
  simp [upperEmbed]

@[simp] theorem upperEmbed_one (a : I) : upperEmbed a 1 = 1 := by
  apply Subtype.ext
  simp [upperEmbed]

theorem lowerEmbed_lowerCoord (a u : I) (hu : u ≤ a) : lowerEmbed a (lowerCoord a u) = u := by
  apply Subtype.ext
  exact (weight_lowerCoord a u).trans (min_eq_right (show (u : ℝ) ≤ a from hu))

theorem upperEmbed_upperCoord (a u : I) (hu : a ≤ u) : upperEmbed a (upperCoord a u) = u := by
  apply Subtype.ext
  change (a : ℝ) + (1 - (a : ℝ)) * upperCoord a u = u
  rw [weight_upperCoord, max_eq_right (sub_nonneg.mpr (show (a : ℝ) ≤ u from hu))]
  ring

end OrdinalSum

open OrdinalSum

theorem isClassical_lowerOrdinalComponent (C : Copula 2) (a : I) (ha0 : 0 < a)
    (ha : C.diagonal a = a) :
    IsClassical (fun u : Fin 2 → I => C.cdf ![lowerEmbed a (u 0), lowerEmbed a (u 1)] / a) := by
  have hp : (0 : ℝ) < a := ha0
  apply IsClassical.ofBivariate (fun u v => C.cdf ![lowerEmbed a u, lowerEmbed a v] / a)
    (by intro v; simp) (by intro u; simp)
  · intro v
    rw [lowerEmbed_one, C.cdf_left_cut_of_le a _ ha (lowerEmbed_le a v)]
    change (a : ℝ) * v / a = v
    field_simp [hp.ne']
  · intro u
    rw [lowerEmbed_one, C.cdf_right_cut_of_le a _ ha (lowerEmbed_le a u)]
    change (a : ℝ) * u / a = u
    field_simp [hp.ne']
  · intro u v s t huv hst
    have hi := C.rectangleIncrement_cdf_nonneg ![lowerEmbed a u, lowerEmbed a s]
      ![lowerEmbed a v, lowerEmbed a t] (by
        intro i; fin_cases i
        · exact lowerEmbed_mono a huv
        · exact lowerEmbed_mono a hst)
    simp only [rectangleIncrement_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hi
    convert div_nonneg hi hp.le using 1
    ring

theorem isClassical_upperOrdinalComponent (C : Copula 2) (a : I) (ha1 : a < 1)
    (ha : C.diagonal a = a) :
    IsClassical (fun u : Fin 2 → I =>
      (C.cdf ![upperEmbed a (u 0), upperEmbed a (u 1)] - a) / (1 - a)) := by
  have hp : 0 < 1 - (a : ℝ) := sub_pos.mpr ha1
  apply IsClassical.ofBivariate (fun u v => (C.cdf ![upperEmbed a u, upperEmbed a v] - a) / (1 - a))
  · intro v
    rw [upperEmbed_zero, C.cdf_left_cut_of_ge a _ ha (le_upperEmbed a v)]
    simp
  · intro u
    rw [upperEmbed_zero, C.cdf_right_cut_of_ge a _ ha (le_upperEmbed a u)]
    simp
  · intro v
    rw [upperEmbed_one, C.cdf_two_one_left]
    change ((a : ℝ) + (1 - (a : ℝ)) * v - a) / (1 - a) = v
    field_simp [hp.ne']
    ring
  · intro u
    rw [upperEmbed_one, C.cdf_two_one_right]
    change ((a : ℝ) + (1 - (a : ℝ)) * u - a) / (1 - a) = u
    field_simp [hp.ne']
    ring
  · intro u v s t huv hst
    have hi := C.rectangleIncrement_cdf_nonneg ![upperEmbed a u, upperEmbed a s]
      ![upperEmbed a v, upperEmbed a t] (by
        intro i; fin_cases i
        · exact upperEmbed_mono a huv
        · exact upperEmbed_mono a hst)
    simp only [rectangleIncrement_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hi
    convert div_nonneg hi hp.le using 1
    ring

/-- Restrict to the lower square at a diagonal cut, then rescale it to the unit square. -/
noncomputable def lowerOrdinalComponent (C : Copula 2) (a : I) (ha0 : 0 < a)
    (ha : C.diagonal a = a) : Copula 2 :=
  ofClassical _ (isClassical_lowerOrdinalComponent C a ha0 ha)

/-- Restrict to the upper square at a diagonal cut, then rescale it to the unit square. -/
noncomputable def upperOrdinalComponent (C : Copula 2) (a : I) (ha1 : a < 1)
    (ha : C.diagonal a = a) : Copula 2 :=
  ofClassical _ (isClassical_upperOrdinalComponent C a ha1 ha)

@[simp] theorem cdf_lowerOrdinalComponent (C : Copula 2) (a : I) (ha0 : 0 < a)
    (ha : C.diagonal a = a) (u : Fin 2 → I) :
    (C.lowerOrdinalComponent a ha0 ha).cdf u =
      C.cdf ![lowerEmbed a (u 0), lowerEmbed a (u 1)] / a :=
  congrFun (cdf_ofClassical _ _) u

@[simp] theorem cdf_upperOrdinalComponent (C : Copula 2) (a : I) (ha1 : a < 1)
    (ha : C.diagonal a = a) (u : Fin 2 → I) :
    (C.upperOrdinalComponent a ha1 ha).cdf u =
      (C.cdf ![upperEmbed a (u 0), upperEmbed a (u 1)] - a) / (1 - a) :=
  congrFun (cdf_ofClassical _ _) u

end ProbabilityTheory.Copula
