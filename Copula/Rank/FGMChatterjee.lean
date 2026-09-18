/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.FGMKendall
import Copula.Rank.ConditionalCDF

/-! # The conditional CDF and Chatterjee's xi of FGM copulas -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The continuous version of the FGM conditional CDF, second coordinate
given first. -/
def fgmConditionalCDF (θ : ℝ) (u v : I) : ℝ :=
  (v : ℝ) + θ * (1 - 2 * (u : ℝ)) * (v : ℝ) * (1 - (v : ℝ))

theorem fgmConditionalCDF_nonneg (θ : ℝ) (hθ : |θ| ≤ 1) (u v : I) :
    0 ≤ fgmConditionalCDF θ u v := by
  have hh : (v : ℝ) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [v.property.1, v.property.2]
  have h := mul_nonneg v.property.1 (fgmDensity_nonneg θ hθ ![u, ⟨(v : ℝ) / 2, hh⟩])
  simp only [fgmDensity, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  unfold fgmConditionalCDF
  nlinarith

theorem integral_Iic_fgmConditionalCDF (θ : ℝ) (u v : I) :
    (∫ t in Iic u, fgmConditionalCDF θ t v) = fgmCDF θ u v := by
  have he : (fun t => fgmConditionalCDF θ t v) =
      fun t : I => (v : ℝ) + (θ * (v : ℝ) * (1 - (v : ℝ))) * (1 - 2 * (t : ℝ)) := by
    funext t; unfold fgmConditionalCDF; ring
  rw [he, integral_add, integral_const_mul, integral_unit_Iic_one_sub_two_mul]
  · simp only [integral_const, Measure.real, Measure.restrict_apply_univ,
      unitInterval.volume_Iic, ENNReal.toReal_ofReal u.property.1, smul_eq_mul, fgmCDF]
    ring
  · exact integrable_const _
  · exact (integrable_continuous_unit volume (by fun_prop)).integrableOn

theorem conditionalCDF_fgm (θ : ℝ) (hθ : |θ| ≤ 1) (v : I) :
    (fun u => (fgm θ hθ).conditionalCDF u v) =ᵐ[volume] fun u => fgmConditionalCDF θ u v := by
  apply conditionalCDF_ae_eq_of_integral
    (hf := integrable_continuous_unit volume (by unfold fgmConditionalCDF; fun_prop))
    (hn := fun u => fgmConditionalCDF_nonneg θ hθ u v)
  intro u
  rw [integral_Iic_fgmConditionalCDF, cdf_fgm]
  rfl

theorem integral_unit_one_sub_two_mul : (∫ t : I, 1 - 2 * (t : ℝ)) = 0 := by
  rw [integral_sub, integral_const_mul, integral_unit_id]
  · norm_num
  all_goals exact integrable_continuous_unit volume (by fun_prop)

theorem integral_unit_one_sub_two_mul_sq : (∫ t : I, (1 - 2 * (t : ℝ)) ^ 2) = 1 / 3 := by
  have he : (fun t : I => (1 - 2 * (t : ℝ)) ^ 2) =
      fun t : I => 1 - 4 * (t : ℝ) + 4 * (t : ℝ) ^ 2 := by funext t; ring
  rw [he, integral_add, integral_sub, integral_const_mul, integral_const_mul,
    integral_unit_id, integral_unit_pow]
  · norm_num
  all_goals exact integrable_continuous_unit volume (by fun_prop)

theorem integral_fgmConditionalCDF_sq (θ : ℝ) (v : I) :
    (∫ u : I, fgmConditionalCDF θ u v ^ 2) =
      (v : ℝ) ^ 2 + θ ^ 2 / 3 * ((v : ℝ) ^ 2 * (1 - (v : ℝ)) ^ 2) := by
  have he : (fun u => fgmConditionalCDF θ u v ^ 2) = fun u : I =>
      (v : ℝ) ^ 2 + (2 * θ * (v : ℝ) ^ 2 * (1 - (v : ℝ))) * (1 - 2 * (u : ℝ)) +
        (θ ^ 2 * (v : ℝ) ^ 2 * (1 - (v : ℝ)) ^ 2) * (1 - 2 * (u : ℝ)) ^ 2 := by
    funext u; unfold fgmConditionalCDF; ring
  rw [he, integral_add, integral_add, integral_const_mul, integral_const_mul,
    integral_unit_one_sub_two_mul, integral_unit_one_sub_two_mul_sq]
  · simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    ring
  all_goals exact integrable_continuous_unit volume (by fun_prop)

theorem chatterjeeXi_fgm (θ : ℝ) (hθ : |θ| ≤ 1) : (fgm θ hθ).chatterjeeXi = θ ^ 2 / 15 := by
  have he (v : I) : (∫ u : I, (fgm θ hθ).conditionalCDF u v ^ 2) =
      (v : ℝ) ^ 2 + θ ^ 2 / 3 * ((v : ℝ) ^ 2 * (1 - (v : ℝ)) ^ 2) := by
    rw [← integral_fgmConditionalCDF_sq]
    apply integral_congr_ae
    filter_upwards [conditionalCDF_fgm θ hθ v] with u hu
    rw [hu]
  unfold chatterjeeXi
  simp_rw [he]
  rw [integral_add, integral_const_mul, integral_unit_pow, integral_unit_sq_mul_one_sub_sq]
  · norm_num; ring
  all_goals exact integrable_continuous_unit volume (by fun_prop)

end ProbabilityTheory.Copula
