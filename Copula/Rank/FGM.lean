/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.SpearmanCDF
import Copula.Families.FGM

/-! # Exact rho, footrule, gamma and beta of the FGM family -/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem integral_unit_mul_one_sub : (∫ t : I, (t : ℝ) * (1 - (t : ℝ))) = 1 / 6 := by
  have he : (fun t : I => (t : ℝ) * (1 - (t : ℝ))) =
      fun t : I => (t : ℝ) - (t : ℝ) ^ 2 := by funext t; ring
  rw [he, integral_sub, integral_unit_id, integral_unit_pow]
  · norm_num
  all_goals exact integrable_continuous_unit volume (by fun_prop)

theorem integral_unit_sq_mul_one_sub_sq :
    (∫ t : I, (t : ℝ) ^ 2 * (1 - (t : ℝ)) ^ 2) = 1 / 30 := by
  have he : (fun t : I => (t : ℝ) ^ 2 * (1 - (t : ℝ)) ^ 2) =
      fun t : I => (t : ℝ) ^ 2 - 2 * (t : ℝ) ^ 3 + (t : ℝ) ^ 4 := by funext t; ring
  rw [he, integral_add, integral_sub, integral_const_mul,
    integral_unit_pow, integral_unit_pow, integral_unit_pow]
  · norm_num
  all_goals exact integrable_continuous_unit volume (by fun_prop)

theorem spearmanRho_fgm (θ : ℝ) (hθ : |θ| ≤ 1) : (fgm θ hθ).spearmanRho = θ / 3 := by
  rw [spearmanRho_eq_integral_cdf]
  have he : (fgm θ hθ).cdf = fun x : Fin 2 → I => (x 0 : ℝ) * (x 1 : ℝ) +
      θ * (((x 0 : ℝ) * (1 - (x 0 : ℝ))) * ((x 1 : ℝ) * (1 - (x 1 : ℝ)))) := by
    funext x; rw [cdf_fgm]; unfold fgmCDF; ring
  rw [he, integral_add, integral_const_mul, integral_independence_mul,
    integral_independence_mul (fun t : I => (t : ℝ) * (1 - (t : ℝ)))
      (fun t : I => (t : ℝ) * (1 - (t : ℝ))), integral_unit_id, integral_unit_mul_one_sub]
  · ring
  all_goals exact integrable_continuous_cube (independence 2).toMeasure (by fun_prop)

theorem integral_diagonal_fgm (θ : ℝ) (hθ : |θ| ≤ 1) :
    (∫ t : I, (fgm θ hθ).cdf ![t, t]) = 1 / 3 + θ / 30 := by
  have he : (fun t : I => (fgm θ hθ).cdf ![t, t]) =
      fun t : I => (t : ℝ) ^ 2 + θ * ((t : ℝ) ^ 2 * (1 - (t : ℝ)) ^ 2) := by
    funext t; simp only [cdf_fgm, Matrix.cons_val_zero, Matrix.cons_val_one]; unfold fgmCDF; ring
  rw [he, integral_add, integral_const_mul, integral_unit_pow, integral_unit_sq_mul_one_sub_sq]
  · norm_num; ring
  all_goals exact integrable_continuous_unit volume (by fun_prop)

theorem integral_antidiagonal_fgm (θ : ℝ) (hθ : |θ| ≤ 1) :
    (∫ t : I, (fgm θ hθ).cdf ![t, unitInterval.symm t]) = 1 / 6 + θ / 30 := by
  have he : (fun t : I => (fgm θ hθ).cdf ![t, unitInterval.symm t]) =
      fun t : I => (t : ℝ) * (1 - (t : ℝ)) + θ * ((t : ℝ) ^ 2 * (1 - (t : ℝ)) ^ 2) := by
    funext t
    simp only [cdf_fgm, Matrix.cons_val_zero, Matrix.cons_val_one, fgmCDF,
      unitInterval.coe_symm_eq]
    ring
  rw [he, integral_add, integral_const_mul, integral_unit_mul_one_sub, integral_unit_sq_mul_one_sub_sq]
  · ring
  all_goals exact integrable_continuous_unit volume (by fun_prop)

theorem spearmanFootrule_fgm (θ : ℝ) (hθ : |θ| ≤ 1) : (fgm θ hθ).spearmanFootrule = θ / 5 := by
  rw [spearmanFootrule, integral_diagonal_fgm]
  ring

theorem giniGamma_fgm (θ : ℝ) (hθ : |θ| ≤ 1) : (fgm θ hθ).giniGamma = 4 * θ / 15 := by
  rw [giniGamma, integral_diagonal_fgm, integral_antidiagonal_fgm]
  ring

theorem blomqvistBeta_fgm (θ : ℝ) (hθ : |θ| ≤ 1) : (fgm θ hθ).blomqvistBeta = θ / 4 := by
  simp only [blomqvistBeta, cdf_fgm, Matrix.cons_val_zero, Matrix.cons_val_one, fgmCDF, unitHalf]
  ring

end ProbabilityTheory.Copula
