/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Blest

/-! # Sharp bounds for directional and symmetrized Blest correlation -/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem integral_unit_one_sub_pow (n : ℕ) :
    (∫ u : I, (1 - (u : ℝ)) ^ n) = 1 / (n + 1 : ℝ) := by
  have h := unitInterval.measurePreserving_symm.integral_comp
    unitInterval.symmMeasurableEquiv.measurableEmbedding (fun u : I => (u : ℝ) ^ n)
  simpa only [unitInterval.coe_symm_eq, integral_unit_pow] using h

theorem blestNu_mem_Icc (C : Copula 2) : C.blestNu ∈ Set.Icc (-1) 1 := by
  have hf : Integrable (fun x : Fin 2 → I => (1 - (x 0 : ℝ)) ^ 2 * (x 1 : ℝ)) C.toMeasure :=
    integrable_continuous_cube _ (by fun_prop)
  have hupper := integral_mono hf (integrable_continuous_cube C.toMeasure (show Continuous
    (fun x : Fin 2 → I => (2 / 3 : ℝ) * (1 - (x 0 : ℝ)) ^ 3 + (1 / 3 : ℝ) * (x 1 : ℝ) ^ 3)
    by fun_prop)) (fun x => show (1 - (x 0 : ℝ)) ^ 2 * (x 1 : ℝ) ≤
      (2 / 3 : ℝ) * (1 - (x 0 : ℝ)) ^ 3 + (1 / 3 : ℝ) * (x 1 : ℝ) ^ 3 by
    have hn := mul_nonneg (sq_nonneg ((1 - (x 0 : ℝ)) - (x 1 : ℝ)))
      (show 0 ≤ 2 * (1 - (x 0 : ℝ)) + (x 1 : ℝ) by linarith [(x 0).property.2, (x 1).property.1])
    nlinarith)
  rw [integral_add (integrable_continuous_cube _ (by fun_prop))
    (integrable_continuous_cube _ (by fun_prop)), integral_const_mul, integral_const_mul,
    C.integral_eval 0 (fun u : I => (1 - (u : ℝ)) ^ 3) (by fun_prop),
    C.integral_eval 1 (fun u : I => (u : ℝ) ^ 3) (by fun_prop),
    integral_unit_one_sub_pow, integral_unit_pow] at hupper
  have hlower := integral_mono (integrable_continuous_cube C.toMeasure (show Continuous
    (fun x : Fin 2 → I => (1 - (x 0 : ℝ)) ^ 2 - (2 / 3 : ℝ) * (1 - (x 0 : ℝ)) ^ 3 -
      (1 / 3 : ℝ) * (1 - (x 1 : ℝ)) ^ 3) by fun_prop)) hf
    (fun x => show (1 - (x 0 : ℝ)) ^ 2 - (2 / 3 : ℝ) * (1 - (x 0 : ℝ)) ^ 3 -
      (1 / 3 : ℝ) * (1 - (x 1 : ℝ)) ^ 3 ≤ (1 - (x 0 : ℝ)) ^ 2 * (x 1 : ℝ) by
    have hn := mul_nonneg (sq_nonneg ((1 - (x 0 : ℝ)) - (1 - (x 1 : ℝ))))
      (show 0 ≤ 2 * (1 - (x 0 : ℝ)) + (1 - (x 1 : ℝ)) by
        linarith [(x 0).property.2, (x 1).property.2])
    nlinarith)
  rw [integral_sub (integrable_continuous_cube _ (by fun_prop))
    (integrable_continuous_cube _ (by fun_prop)),
    integral_sub (integrable_continuous_cube _ (by fun_prop))
      (integrable_continuous_cube _ (by fun_prop)), integral_const_mul, integral_const_mul,
    C.integral_eval 0 (fun u : I => (1 - (u : ℝ)) ^ 2) (by fun_prop),
    C.integral_eval 0 (fun u : I => (1 - (u : ℝ)) ^ 3) (by fun_prop),
    C.integral_eval 1 (fun u : I => (1 - (u : ℝ)) ^ 3) (by fun_prop),
    integral_unit_one_sub_pow, integral_unit_one_sub_pow] at hlower
  unfold blestNu
  constructor <;> norm_num at hupper hlower ⊢ <;> linarith

theorem symmetrizedBlest_mem_Icc (C : Copula 2) : C.symmetrizedBlest ∈ Set.Icc (-1) 1 := by
  have h := C.blestNu_mem_Icc
  have ht := C.transpose.blestNu_mem_Icc
  unfold symmetrizedBlest
  constructor <;> linarith [h.1, h.2, ht.1, ht.2]

end ProbabilityTheory.Copula
