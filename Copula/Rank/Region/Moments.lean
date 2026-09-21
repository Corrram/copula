/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel

Adapted from Corrram/lean-verifications, commit
9e144da5e0d8e2b59dadf9cef090947cb2220313.
Source module: Verification.RankMoments
Imports and namespaces adapted to the copula package; unused helpers omitted.
-/
import Copula.Rank.Concordance

/-! # Absolute-displacement moment representations

These identities apply to arbitrary bivariate copula measures, including
singular ones. They connect the CDF-based footrule and gamma definitions to
the transport costs used in the rho-footrule and rho-gamma articles.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion

theorem footrule_eq_abs_moment (C : Copula 2) :
    C.spearmanFootrule = 1 - 3 * (∫ x, |(x 0 : ℝ) - x 1| ∂C.toMeasure) := by
  have hQ := C.concordanceQ_comonotonic
  rw [Copula.concordanceQ_comm, Copula.concordanceQ] at hQ
  simp only [Copula.cdf_comonotonic_two] at hQ
  have hpoint : (fun x : Fin 2 → I => |(x 0 : ℝ) - x 1|) =
      fun x => (x 0 : ℝ) + x 1 - 2 * min (x 0 : ℝ) (x 1 : ℝ) := by
    funext x
    rcases le_total (x 0 : ℝ) (x 1 : ℝ) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left h]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr h), min_eq_right h]
      ring
  rw [hpoint, integral_sub, integral_add, integral_const_mul,
    C.integral_coe_eval, C.integral_coe_eval]
  · linarith
  all_goals exact Copula.integrable_continuous_cube C.toMeasure (by fun_prop)

theorem gamma_eq_abs_moments (C : Copula 2) :
    C.giniGamma = 2 * (∫ x,
      |(x 0 : ℝ) + x 1 - 1| - |(x 0 : ℝ) - x 1| ∂C.toMeasure) := by
  have hQ := C.concordanceQ_countermonotonic
  rw [Copula.concordanceQ_comm, Copula.concordanceQ] at hQ
  simp only [Copula.cdf_countermonotonic] at hQ
  have hpoint : (fun x : Fin 2 → I => |(x 0 : ℝ) + x 1 - 1|) =
      fun x => 2 * max 0 ((x 0 : ℝ) + x 1 - 1) -
        ((x 0 : ℝ) + x 1 - 1) := by
    funext x
    rcases le_total 0 ((x 0 : ℝ) + x 1 - 1) with h | h
    · rw [abs_of_nonneg h, max_eq_right h]
      ring
    · rw [abs_of_nonpos h, max_eq_left h]
      ring
  have hsum : (∫ x, (x 0 : ℝ) + x 1 - 1 ∂C.toMeasure) = 0 := by
    rw [integral_sub, integral_add, C.integral_coe_eval, C.integral_coe_eval]
    · norm_num
    all_goals exact Copula.integrable_continuous_cube C.toMeasure (by fun_prop)
  have habs : (∫ x, |(x 0 : ℝ) + x 1 - 1| ∂C.toMeasure) =
      2 * (∫ x, max 0 ((x 0 : ℝ) + x 1 - 1) ∂C.toMeasure) := by
    rw [hpoint, integral_sub, integral_const_mul, hsum, sub_zero]
    all_goals exact Copula.integrable_continuous_cube C.toMeasure (by fun_prop)
  rw [integral_sub, habs]
  · linarith [footrule_eq_abs_moment C]
  all_goals exact Copula.integrable_continuous_cube C.toMeasure (by fun_prop)

end ProbabilityTheory.Copula.RankRegion
