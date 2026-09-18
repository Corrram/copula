/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Basic

/-! # Spearman's rho: distance formulas, bounds and benchmark copulas -/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem spearmanRho_eq_one_sub (C : Copula 2) :
    C.spearmanRho = 1 - 6 * (∫ x, ((x 0 : ℝ) - (x 1 : ℝ)) ^ 2 ∂C.toMeasure) := by
  have he : (fun x : Fin 2 → I => ((x 0 : ℝ) - (x 1 : ℝ)) ^ 2) =
      fun x => (x 0 : ℝ) ^ 2 + (x 1 : ℝ) ^ 2 - 2 * ((x 0 : ℝ) * (x 1 : ℝ)) := by
    funext x; ring
  rw [he, integral_sub, integral_add, integral_const_mul, C.integral_sq_eval, C.integral_sq_eval]
  · unfold spearmanRho; ring
  all_goals exact integrable_continuous_cube C.toMeasure (by fun_prop)

theorem spearmanRho_eq_neg_one_add (C : Copula 2) :
    C.spearmanRho = -1 + 6 * (∫ x, ((x 0 : ℝ) + (x 1 : ℝ) - 1) ^ 2 ∂C.toMeasure) := by
  have he : (fun x : Fin 2 → I => ((x 0 : ℝ) + (x 1 : ℝ) - 1) ^ 2) =
      fun x => (x 0 : ℝ) ^ 2 + (x 1 : ℝ) ^ 2 + 2 * ((x 0 : ℝ) * (x 1 : ℝ)) -
        2 * (x 0 : ℝ) - 2 * (x 1 : ℝ) + 1 := by
    funext x; ring
  rw [he, integral_add, integral_sub, integral_sub, integral_add, integral_add,
    integral_const_mul, integral_const_mul, integral_const_mul,
    C.integral_sq_eval, C.integral_sq_eval, C.integral_coe_eval, C.integral_coe_eval]
  · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    unfold spearmanRho; ring
  all_goals exact integrable_continuous_cube C.toMeasure (by fun_prop)

theorem spearmanRho_mem_Icc (C : Copula 2) : C.spearmanRho ∈ Set.Icc (-1) 1 := by
  constructor
  · rw [C.spearmanRho_eq_neg_one_add]
    have h : 0 ≤ ∫ x, ((x 0 : ℝ) + (x 1 : ℝ) - 1) ^ 2 ∂C.toMeasure :=
      integral_nonneg (fun x => sq_nonneg _)
    linarith
  · rw [C.spearmanRho_eq_one_sub]
    have h : 0 ≤ ∫ x, ((x 0 : ℝ) - (x 1 : ℝ)) ^ 2 ∂C.toMeasure :=
      integral_nonneg (fun x => sq_nonneg _)
    linarith

@[simp] theorem spearmanRho_independence : (independence 2).spearmanRho = 0 := by
  rw [spearmanRho, integral_independence_mul, integral_unit_id]
  norm_num

@[simp] theorem spearmanRho_comonotonic : (comonotonic 2).spearmanRho = 1 := by
  rw [spearmanRho_eq_one_sub, integral_comonotonic _ (by fun_prop)]
  simp

@[simp] theorem spearmanRho_countermonotonic : countermonotonic.spearmanRho = -1 := by
  rw [spearmanRho_eq_neg_one_add, integral_countermonotonic _ (by fun_prop)]
  simp [unitInterval.coe_symm_eq]

end ProbabilityTheory.Copula
