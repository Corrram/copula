/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Symmetry
import Copula.Rank.MixtureMeasure

/-! # Blest's rank correlation and its symmetrization

The directional coefficient weights discrepancies in the top ranks. Averaging
it with its transpose gives the symmetrized coefficient of Genest and Plante.
These are population copula functionals, not finite-sample estimators.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Blest's directional population rank correlation. -/
noncomputable def blestNu (C : Copula 2) : ℝ :=
  2 - 12 * ∫ x, (1 - (x 0 : ℝ)) ^ 2 * (x 1 : ℝ) ∂C.toMeasure

/-- Symmetrized Blest rank correlation: the average of both coordinate directions. -/
noncomputable def symmetrizedBlest (C : Copula 2) : ℝ :=
  (C.blestNu + C.transpose.blestNu) / 2

@[simp] theorem symmetrizedBlest_transpose (C : Copula 2) :
    C.transpose.symmetrizedBlest = C.symmetrizedBlest := by
  simp [symmetrizedBlest, add_comm]

/-- The symmetric mixed-moment formula fixes the normalization independently
of the directional representation. -/
theorem symmetrizedBlest_eq_integral (C : Copula 2) :
    C.symmetrizedBlest =
      -4 + 6 * ∫ x, (x 0 : ℝ) * (x 1 : ℝ) * (4 - (x 0 : ℝ) - (x 1 : ℝ)) ∂C.toMeasure := by
  unfold symmetrizedBlest blestNu
  rw [C.integral_transpose _ (by fun_prop)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have he : (fun x : Fin 2 → I => (1 - (x 0 : ℝ)) ^ 2 * (x 1 : ℝ) +
      (1 - (x 1 : ℝ)) ^ 2 * (x 0 : ℝ)) =
      fun x => (x 0 : ℝ) + (x 1 : ℝ) -
        (x 0 : ℝ) * (x 1 : ℝ) * (4 - (x 0 : ℝ) - (x 1 : ℝ)) := by
    funext x
    ring
  have hi := congrArg (fun f => ∫ x, f x ∂C.toMeasure) he
  rw [integral_add, integral_sub, integral_add, C.integral_coe_eval, C.integral_coe_eval] at hi
  · linarith
  all_goals exact integrable_continuous_cube C.toMeasure (by fun_prop)

private theorem integral_one_sub_sq : (∫ u : I, (1 - (u : ℝ)) ^ 2) = 1 / 3 := by
  have he : (fun u : I => (1 - (u : ℝ)) ^ 2) = fun u : I => 1 - 2 * (u : ℝ) + (u : ℝ) ^ 2 := by
    funext u; ring
  rw [he, integral_add, integral_sub, integral_const_mul, integral_unit_id, integral_unit_pow]
  · norm_num
  all_goals exact integrable_continuous_unit volume (by fun_prop)

@[simp] theorem blestNu_independence : (independence 2).blestNu = 0 := by
  rw [blestNu, integral_independence_mul (fun u : I => (1 - (u : ℝ)) ^ 2)
    (fun v : I => (v : ℝ)), integral_one_sub_sq, integral_unit_id]
  norm_num

@[simp] theorem blestNu_comonotonic : (comonotonic 2).blestNu = 1 := by
  rw [blestNu, integral_comonotonic _ (by fun_prop)]
  have he : (fun u : I => (1 - (u : ℝ)) ^ 2 * (u : ℝ)) =
      fun u : I => (u : ℝ) - 2 * (u : ℝ) ^ 2 + (u : ℝ) ^ 3 := by funext u; ring
  rw [he, integral_add, integral_sub, integral_const_mul, integral_unit_id, integral_unit_pow,
    integral_unit_pow]
  · norm_num
  all_goals exact integrable_continuous_unit volume (by fun_prop)

@[simp] theorem blestNu_countermonotonic : countermonotonic.blestNu = -1 := by
  rw [blestNu, integral_countermonotonic _ (by fun_prop)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, unitInterval.coe_symm_eq]
  have he : (fun u : I => (1 - (u : ℝ)) ^ 2 * (1 - (u : ℝ))) =
      fun u : I => 1 - 3 * (u : ℝ) + 3 * (u : ℝ) ^ 2 - (u : ℝ) ^ 3 := by funext u; ring
  rw [he, integral_sub, integral_add, integral_sub, integral_const_mul, integral_const_mul,
    integral_unit_id, integral_unit_pow, integral_unit_pow]
  · norm_num
  all_goals exact integrable_continuous_unit volume (by fun_prop)

@[simp] theorem symmetrizedBlest_independence : (independence 2).symmetrizedBlest = 0 := by
  rw [symmetrizedBlest, show (independence 2).transpose = independence 2 from isExchangeable_independence]
  norm_num

@[simp] theorem symmetrizedBlest_comonotonic : (comonotonic 2).symmetrizedBlest = 1 := by
  rw [symmetrizedBlest, show (comonotonic 2).transpose = comonotonic 2 from isExchangeable_comonotonic]
  norm_num

@[simp] theorem symmetrizedBlest_countermonotonic : countermonotonic.symmetrizedBlest = -1 := by
  rw [symmetrizedBlest, show countermonotonic.transpose = countermonotonic from isExchangeable_countermonotonic]
  norm_num

theorem blestNu_mix (C D : Copula 2) (a : I) :
    (C.mix D a).blestNu = (a : ℝ) * C.blestNu + (1 - (a : ℝ)) * D.blestNu := by
  unfold blestNu
  rw [integral_mix C D a (by fun_prop)]
  ring

theorem symmetrizedBlest_mix (C D : Copula 2) (a : I) :
    (C.mix D a).symmetrizedBlest =
      (a : ℝ) * C.symmetrizedBlest + (1 - (a : ℝ)) * D.symmetrizedBlest := by
  simp only [symmetrizedBlest, transpose_mix, blestNu_mix]
  ring

end ProbabilityTheory.Copula
