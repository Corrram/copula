/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.FGM
import Copula.Dependence.Density

/-! # The FGM density and its multivariate total positivity -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The Lebesgue density of a bivariate FGM copula. -/
def fgmDensity (θ : ℝ) (x : Fin 2 → I) : ℝ :=
  1 + θ * (1 - 2 * (x 0 : ℝ)) * (1 - 2 * (x 1 : ℝ))

theorem continuous_fgmDensity (θ : ℝ) : Continuous (fgmDensity θ) := by
  unfold fgmDensity; fun_prop

theorem fgmDensity_nonneg (θ : ℝ) (hθ : |θ| ≤ 1) (x : Fin 2 → I) : 0 ≤ fgmDensity θ x := by
  have h0 : |1 - 2 * (x 0 : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [(x 0).property.1, (x 0).property.2]
  have h1 : |1 - 2 * (x 1 : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [(x 1).property.1, (x 1).property.2]
  have hp : |θ * (1 - 2 * (x 0 : ℝ)) * (1 - 2 * (x 1 : ℝ))| ≤ 1 := by
    rw [abs_mul, abs_mul]
    nlinarith [abs_nonneg θ, abs_nonneg (1 - 2 * (x 0 : ℝ)),
      abs_nonneg (1 - 2 * (x 1 : ℝ)), mul_le_mul hθ h0 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  unfold fgmDensity
  linarith [(abs_le.mp hp).1]

theorem integral_Iic_fgmDensity (θ : ℝ) (u : Fin 2 → I) :
    (∫ x in Iic u, fgmDensity θ x) = fgmCDF θ (u 0) (u 1) := by
  have he : u = ![u 0, u 1] := by ext i; fin_cases i <;> rfl
  have hf : IntegrableOn (fun x : Fin 2 → I =>
      θ * (1 - 2 * (x 0 : ℝ)) * (1 - 2 * (x 1 : ℝ))) (Iic u) :=
    (integrable_continuous_cube volume (by fun_prop)).integrableOn
  unfold fgmDensity
  rw [integral_add (integrable_const _) hf]
  have hp : (∫ x in Iic u, θ * (1 - 2 * (x 0 : ℝ)) * (1 - 2 * (x 1 : ℝ))) =
      θ * ((u 0 : ℝ) * (1 - (u 0 : ℝ))) * ((u 1 : ℝ) * (1 - (u 1 : ℝ))) := by
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    rw [he, integral_cube_Iic_mul (fun t : I => 1 - 2 * (t : ℝ))
      (fun t : I => 1 - 2 * (t : ℝ))]
    simp only [integral_unit_Iic_one_sub_two_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hp]
  have hv : (∫ _ : Fin 2 → I in Iic u, (1 : ℝ)) = (u 0 : ℝ) * (u 1 : ℝ) := by
    rw [setIntegral_one_eq_measureReal]
    change (independence 2).toMeasure.real (Iic u) = _
    exact cdf_independence u |>.trans (Fin.prod_univ_two _)
  rw [hv]
  unfold fgmCDF
  ring

theorem toMeasure_fgm (θ : ℝ) (hθ : |θ| ≤ 1) :
    (fgm θ hθ).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (fgmDensity θ x)) := by
  apply toMeasure_eq_withDensity_of_cdf_integral _
    (integrable_continuous_cube volume (continuous_fgmDensity θ)) (fgmDensity_nonneg θ hθ)
  intro u
  rw [integral_Iic_fgmDensity, cdf_fgm]

theorem isMTP2_fgmDensity_iff (θ : ℝ) : IsMTP2 (fgmDensity θ) ↔ 0 ≤ θ := by
  rw [isMTP2_fin_two_iff]
  constructor
  · intro h
    have ht := h 0 1 0 1 zero_le_one zero_le_one
    norm_num [fgmDensity] at ht
    nlinarith
  · intro h a b c d hab hcd
    have hn := mul_nonneg (mul_nonneg h (sub_nonneg.mpr (show (a : ℝ) ≤ (b : ℝ) from hab)))
      (sub_nonneg.mpr (show (c : ℝ) ≤ (d : ℝ) from hcd))
    simp only [fgmDensity, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith

theorem hasMTP2Density_fgm (θ : ℝ) (hθ : |θ| ≤ 1) (hpos : 0 ≤ θ) :
    (fgm θ hθ).HasMTP2Density :=
  ⟨fgmDensity θ, (continuous_fgmDensity θ).measurable, fgmDensity_nonneg θ hθ,
    (isMTP2_fgmDensity_iff θ).mpr hpos, toMeasure_fgm θ hθ⟩

end ProbabilityTheory.Copula
