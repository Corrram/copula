/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Conditional

/-! # Chatterjee's directional population coefficient

The direction is coordinate `1` given coordinate `0`. Regular conditional
distributions make the definition applicable to singular copulas too.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Population Chatterjee xi, for the second coordinate given the first. -/
noncomputable def chatterjeeXi (C : Copula 2) : ℝ :=
  6 * (∫ t : I, ∫ u : I, C.conditionalCDF u t ^ 2) - 2

theorem integrable_integral_conditionalCDF_sq (C : Copula 2) :
    Integrable (fun t : I => ∫ u : I, C.conditionalCDF u t ^ 2) := by
  refine (integrable_const (1 : ℝ)).mono'
    (C.measurable_conditionalCDF.pow_const 2).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun u => sq_nonneg _)]
    exact (C.integral_conditionalCDF_sq_le t).trans t.property.2

theorem integral_conditionalCDF_centered_sq (C : Copula 2) (t : I) :
    (∫ u : I, (C.conditionalCDF u t - (t : ℝ)) ^ 2) =
      (∫ u : I, C.conditionalCDF u t ^ 2) - (t : ℝ) ^ 2 := by
  have he : (fun u : I => (C.conditionalCDF u t - (t : ℝ)) ^ 2) =
      fun u : I => C.conditionalCDF u t ^ 2 - (2 * (t : ℝ)) * C.conditionalCDF u t + (t : ℝ) ^ 2 := by
    funext u; ring
  have hm : Integrable (fun u : I => (2 * (t : ℝ)) * C.conditionalCDF u t) :=
    (C.integrable_conditionalCDF t).const_mul _
  have hd : Integrable (fun u : I => C.conditionalCDF u t ^ 2 -
      (2 * (t : ℝ)) * C.conditionalCDF u t) := (C.integrable_conditionalCDF_sq t).sub hm
  rw [he, integral_add hd (integrable_const ((t : ℝ) ^ 2)),
    integral_sub (C.integrable_conditionalCDF_sq t) hm,
    integral_const_mul, C.integral_conditionalCDF]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- The integrated conditional variance form of xi. -/
theorem chatterjeeXi_eq_integral_centered_sq (C : Copula 2) :
    C.chatterjeeXi = 6 * (∫ t : I, ∫ u : I, (C.conditionalCDF u t - (t : ℝ)) ^ 2) := by
  simp_rw [C.integral_conditionalCDF_centered_sq]
  rw [integral_sub C.integrable_integral_conditionalCDF_sq
    (integrable_continuous_unit volume (by fun_prop)), integral_unit_pow]
  unfold chatterjeeXi
  norm_num
  ring

theorem chatterjeeXi_nonneg (C : Copula 2) : 0 ≤ C.chatterjeeXi := by
  rw [C.chatterjeeXi_eq_integral_centered_sq]
  exact mul_nonneg (by norm_num) (integral_nonneg fun t => integral_nonneg fun u => sq_nonneg _)

theorem chatterjeeXi_le_one (C : Copula 2) : C.chatterjeeXi ≤ 1 := by
  have h := integral_mono C.integrable_integral_conditionalCDF_sq
    (integrable_continuous_unit volume continuous_subtype_val) C.integral_conditionalCDF_sq_le
  rw [integral_unit_id] at h
  unfold chatterjeeXi
  linarith

theorem chatterjeeXi_mem_Icc (C : Copula 2) : C.chatterjeeXi ∈ Icc 0 1 :=
  ⟨C.chatterjeeXi_nonneg, C.chatterjeeXi_le_one⟩

/-- Any almost-everywhere equal version of the conditional kernel computes the same xi. -/
theorem chatterjeeXi_eq_of_kernel_ae (C : Copula 2) (κ : Kernel I I)
    (hκ : C.conditionalKernel =ᵐ[volume] κ) :
    C.chatterjeeXi = 6 * (∫ t : I, ∫ u : I, ((κ u).real (Iic t)) ^ 2) - 2 := by
  unfold chatterjeeXi
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => integral_congr_ae (by
    filter_upwards [hκ] with u hu
    simp only [conditionalCDF, hu])

end ProbabilityTheory.Copula
