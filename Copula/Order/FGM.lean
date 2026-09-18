/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Order.Rank
import Copula.Families.FGM

/-! # Exact parameter ordering of the FGM family -/

open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem lowerOrthantLE_fgm_iff {θ η : ℝ} (hθ : |θ| ≤ 1) (hη : |η| ≤ 1) :
    (fgm θ hθ).LowerOrthantLE (fgm η hη) ↔ θ ≤ η := by
  constructor
  · intro h
    have hh := h ![unitHalf, unitHalf]
    simp only [cdf_fgm, fgmCDF, Matrix.cons_val_zero, Matrix.cons_val_one,
      unitHalf] at hh
    norm_num at hh
    linarith
  · intro h u
    simp only [cdf_fgm, fgmCDF]
    gcongr
    · exact mul_nonneg (u 0).property.1 (u 1).property.1
    · exact sub_nonneg.mpr (u 1).property.2
    · exact sub_nonneg.mpr (u 0).property.2

theorem concordanceLE_fgm_iff {θ η : ℝ} (hθ : |θ| ≤ 1) (hη : |η| ≤ 1) :
    (fgm θ hθ).ConcordanceLE (fgm η hη) ↔ θ ≤ η := by
  rw [concordanceLE_iff_lowerOrthantLE, lowerOrthantLE_fgm_iff]

end ProbabilityTheory.Copula
