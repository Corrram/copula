/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.ChatterjeeCross

/-! # Affinity of the polarized conditional-CDF functional -/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem chatterjeeCross_mix_right (C D E : Copula 2) (a : I) :
    C.chatterjeeCross (D.mix E a) =
      (a : ℝ) * C.chatterjeeCross D + (1 - (a : ℝ)) * C.chatterjeeCross E := by
  have he (v : I) :
      (∫ u : I, C.conditionalCDF u v * (D.mix E a).conditionalCDF u v) =
        (a : ℝ) * (∫ u : I, C.conditionalCDF u v * D.conditionalCDF u v) +
        (1 - (a : ℝ)) * (∫ u : I, C.conditionalCDF u v * E.conditionalCDF u v) := by
    calc
      _ = ∫ u : I, (a : ℝ) * (C.conditionalCDF u v * D.conditionalCDF u v) +
          (1 - (a : ℝ)) * (C.conditionalCDF u v * E.conditionalCDF u v) :=
        integral_congr_ae (by
          filter_upwards [Copula.conditionalCDF_mix D E a v] with u hu
          rw [hu]
          ring)
      _ = _ := by
        rw [integral_add ((C.integrable_conditionalCDF_mul D v).const_mul _)
          ((C.integrable_conditionalCDF_mul E v).const_mul _)]
        simp only [integral_const_mul]
  unfold Copula.chatterjeeCross
  simp_rw [he]
  rw [integral_add ((C.integrable_integral_conditionalCDF_mul D).const_mul _)
    ((C.integrable_integral_conditionalCDF_mul E).const_mul _)]
  simp only [integral_const_mul]
  ring

end ProbabilityTheory.Copula
