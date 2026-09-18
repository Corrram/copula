/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.FGMDensity

/-! # Kendall's tau of FGM copulas

The polynomial density gives the exact formula `2θ/9` on the whole admissible
interval, as in Ansari–Rockel, Table 6.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem integral_unit_mul_one_sub_two_mul :
    (∫ t : I, (t : ℝ) * (1 - 2 * (t : ℝ))) = -1 / 6 := by
  have he : (fun t : I => (t : ℝ) * (1 - 2 * (t : ℝ))) =
      fun t : I => (t : ℝ) - 2 * (t : ℝ) ^ 2 := by funext t; ring
  rw [he, integral_sub, integral_const_mul, integral_unit_id, integral_unit_pow]
  · norm_num
  all_goals exact integrable_continuous_unit volume (by fun_prop)

theorem integral_unit_mul_one_sub_mul_one_sub_two_mul :
    (∫ t : I, (t : ℝ) * (1 - (t : ℝ)) * (1 - 2 * (t : ℝ))) = 0 := by
  have he : (fun t : I => (t : ℝ) * (1 - (t : ℝ)) * (1 - 2 * (t : ℝ))) =
      fun t : I => (t : ℝ) - 3 * (t : ℝ) ^ 2 + 2 * (t : ℝ) ^ 3 := by funext t; ring
  rw [he, integral_add, integral_sub, integral_const_mul, integral_const_mul,
    integral_unit_id, integral_unit_pow, integral_unit_pow]
  · norm_num
  all_goals exact integrable_continuous_unit volume (by fun_prop)

theorem integral_fgm (θ : ℝ) (hθ : |θ| ≤ 1) (f : (Fin 2 → I) → ℝ) :
    (∫ x, f x ∂(fgm θ hθ).toMeasure) = ∫ x, fgmDensity θ x * f x := by
  rw [toMeasure_fgm, integral_withDensity_eq_integral_toReal_smul
    ((continuous_fgmDensity θ).measurable.ennreal_ofReal) (by simp)]
  simp only [ENNReal.toReal_ofReal (fgmDensity_nonneg θ hθ _), smul_eq_mul]

theorem kendallTau_fgm (θ : ℝ) (hθ : |θ| ≤ 1) : (fgm θ hθ).kendallTau = 2 * θ / 9 := by
  rw [kendallTau, integral_fgm]
  have he : (fun x : Fin 2 → I => fgmDensity θ x * (fgm θ hθ).cdf x) =
      fun x : Fin 2 → I => (x 0 : ℝ) * (x 1 : ℝ) +
        θ * (((x 0 : ℝ) * (1 - (x 0 : ℝ))) * ((x 1 : ℝ) * (1 - (x 1 : ℝ)))) +
        θ * (((x 0 : ℝ) * (1 - 2 * (x 0 : ℝ))) * ((x 1 : ℝ) * (1 - 2 * (x 1 : ℝ)))) +
        θ ^ 2 * (((x 0 : ℝ) * (1 - (x 0 : ℝ)) * (1 - 2 * (x 0 : ℝ))) *
          ((x 1 : ℝ) * (1 - (x 1 : ℝ)) * (1 - 2 * (x 1 : ℝ)))) := by
    funext x
    rw [cdf_fgm]
    unfold fgmDensity fgmCDF
    ring
  rw [he]
  have hi : ∀ f : (Fin 2 → I) → ℝ, Continuous f → Integrable f :=
    fun _ h => integrable_continuous_cube volume h
  rw [integral_add (hi _ (by fun_prop)) (hi _ (by fun_prop)),
    integral_add (hi _ (by fun_prop)) (hi _ (by fun_prop)),
    integral_add (hi _ (by fun_prop)) (hi _ (by fun_prop))]
  simp only [integral_const_mul]
  change 4 * ((∫ x, (x 0 : ℝ) * (x 1 : ℝ) ∂(independence 2).toMeasure) +
    θ * (∫ x, ((x 0 : ℝ) * (1 - (x 0 : ℝ))) * ((x 1 : ℝ) * (1 - (x 1 : ℝ)))
      ∂(independence 2).toMeasure) +
    θ * (∫ x, ((x 0 : ℝ) * (1 - 2 * (x 0 : ℝ))) * ((x 1 : ℝ) * (1 - 2 * (x 1 : ℝ)))
      ∂(independence 2).toMeasure) +
    θ ^ 2 * (∫ x, ((x 0 : ℝ) * (1 - (x 0 : ℝ)) * (1 - 2 * (x 0 : ℝ))) *
      ((x 1 : ℝ) * (1 - (x 1 : ℝ)) * (1 - 2 * (x 1 : ℝ)))
      ∂(independence 2).toMeasure)) - 1 = _
  rw [integral_independence_mul,
    integral_independence_mul (fun t : I => (t : ℝ) * (1 - (t : ℝ)))
      (fun t : I => (t : ℝ) * (1 - (t : ℝ))),
    integral_independence_mul (fun t : I => (t : ℝ) * (1 - 2 * (t : ℝ)))
      (fun t : I => (t : ℝ) * (1 - 2 * (t : ℝ))),
    integral_independence_mul (fun t : I => (t : ℝ) * (1 - (t : ℝ)) * (1 - 2 * (t : ℝ)))
      (fun t : I => (t : ℝ) * (1 - (t : ℝ)) * (1 - 2 * (t : ℝ))),
    integral_unit_id, integral_unit_mul_one_sub,
    integral_unit_mul_one_sub_two_mul, integral_unit_mul_one_sub_mul_one_sub_two_mul]
  ring

end ProbabilityTheory.Copula
