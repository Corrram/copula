/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Power
import Copula.Countermonotonic

/-! # A non-strict Archimedean generator

The finite-zero inverse generator `max 0 (1-t)` represents the lower Fréchet
bound. Outer and inner powers give further non-strict bivariate families.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The inverse generator of the lower Fréchet bound. -/
noncomputable def truncatedLinearGenerator : BivariateGenerator where
  toFun t := max 0 (1 - t)
  invFun u := 1 - (u : ℝ)
  nonneg _ _ := le_max_left _ _
  antitone _ _ _ _ h := max_le_max le_rfl (sub_le_sub_left h _)
  convex := by
    refine ⟨convex_Ici _, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul]
    apply max_le
    · positivity
    · nlinarith [mul_le_mul_of_nonneg_left (le_max_right 0 (1 - x)) ha,
        mul_le_mul_of_nonneg_left (le_max_right 0 (1 - y)) hb]
  inv_nonneg u _ := sub_nonneg.mpr u.property.2
  inv_antitone u v _ h := sub_le_sub_left (show (u : ℝ) ≤ (v : ℝ) from h) _
  inv_one := by norm_num
  right_inv u _ := by simpa using max_eq_right u.property.1

@[simp] theorem truncatedLinearGenerator_copula :
    truncatedLinearGenerator.copula = countermonotonic := by
  apply ext_cdf
  intro u
  by_cases hz : u 0 = 0 ∨ u 1 = 0
  · rcases hz with h | h <;>
      rw [cdf_eq_zero_of_coord_eq_zero _ _ _ h, cdf_eq_zero_of_coord_eq_zero _ _ _ h]
  rw [BivariateGenerator.cdf_copula, BivariateGenerator.cdf, ite_eq_right hz,
    cdf_countermonotonic]
  change max 0 (1 - (1 - (u 0 : ℝ) + (1 - (u 1 : ℝ)))) = _
  congr 1
  ring

end ProbabilityTheory.Copula
