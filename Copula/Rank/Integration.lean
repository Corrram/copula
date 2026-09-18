/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.CDF.Continuity
import Copula.CDF.Bounds
import Copula.Independence
import Copula.Countermonotonic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-! # Integration tools for population rank coefficients -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem integrable_continuous_cube {d : ℕ} (μ : Measure (Fin d → I)) [IsFiniteMeasure μ]
    {f : (Fin d → I) → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem integrable_continuous_unit (μ : Measure I) [IsFiniteMeasure μ]
    {f : I → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem integrable_cdf {d : ℕ} (C : Copula d) (μ : Measure (Fin d → I)) [IsFiniteMeasure μ] :
    Integrable C.cdf μ := integrable_continuous_cube μ C.continuous_cdf

/-- Integrating a real function over the uniform unit interval. -/
theorem integral_unitInterval (f : ℝ → ℝ) :
    (∫ u : I, f u) = ∫ t in (0 : ℝ)..1, f t := by
  rw [unitInterval.measurePreserving_coe.integral_comp unitInterval.measurableEmbedding_coe,
    intervalIntegral.integral_of_le zero_le_one]
  exact integral_Icc_eq_integral_Ioc

@[simp] theorem integral_unit_pow (n : ℕ) : (∫ u : I, (u : ℝ) ^ n) = 1 / (n + 1 : ℝ) := by
  rw [integral_unitInterval (fun t : ℝ => t ^ n), integral_pow]
  simp

@[simp] theorem integral_unit_id : (∫ u : I, (u : ℝ)) = 1 / 2 := by
  rw [integral_unitInterval (fun t : ℝ => t), integral_id]
  norm_num

theorem integral_eval {d : ℕ} (C : Copula d) (i : Fin d) (f : I → ℝ)
    (hf : Measurable f) : (∫ x, f (x i) ∂C.toMeasure) = ∫ u : I, f u := by
  rw [← C.map_eval i]
  exact (integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable).symm

@[simp] theorem integral_coe_eval {d : ℕ} (C : Copula d) (i : Fin d) :
    (∫ x, (x i : ℝ) ∂C.toMeasure) = 1 / 2 := by
  rw [C.integral_eval i _ measurable_subtype_coe, integral_unit_id]

@[simp] theorem integral_sq_eval {d : ℕ} (C : Copula d) (i : Fin d) :
    (∫ x, (x i : ℝ) ^ 2 ∂C.toMeasure) = 1 / 3 := by
  rw [C.integral_eval i (fun u : I => (u : ℝ) ^ 2) (by fun_prop), integral_unit_pow]
  norm_num

theorem integral_comonotonic {d : ℕ} (f : (Fin d → I) → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂(comonotonic d).toMeasure) = ∫ u : I, f (fun _ => u) := by
  rw [toMeasure_comonotonic]
  exact integral_map (by fun_prop) hf.aestronglyMeasurable

theorem integral_countermonotonic (f : (Fin 2 → I) → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂countermonotonic.toMeasure) = ∫ u : I, f ![u, unitInterval.symm u] := by
  rw [toMeasure_countermonotonic]
  exact integral_map (by fun_prop) hf.aestronglyMeasurable

theorem integral_independence_mul (f g : I → ℝ) :
    (∫ x, f (x 0) * g (x 1) ∂(independence 2).toMeasure) =
      (∫ u : I, f u) * ∫ v : I, g v := by
  have h := integral_fin_nat_prod_eq_prod (μ := fun _ : Fin 2 => (volume : Measure I)) ![f, g]
  simpa [toMeasure_independence, Fin.prod_univ_two] using h

theorem cdf_comonotonic_two (u : Fin 2 → I) :
    (comonotonic 2).cdf u = min (u 0 : ℝ) (u 1 : ℝ) := by
  rw [cdf_comonotonic]
  have he : (⨅ i, u i) = min (u 0) (u 1) := by
    apply le_antisymm (le_min (iInf_le u 0) (iInf_le u 1))
    apply le_iInf
    intro i
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  rw [he]
  rfl

theorem cdf_countermonotonic_le (C : Copula 2) (u : Fin 2 → I) :
    countermonotonic.cdf u ≤ C.cdf u := by
  rw [cdf_countermonotonic]
  apply max_le (C.cdf_nonneg u)
  have h := C.sum_sub_dim_add_one_le_cdf u
  simp only [Fin.sum_univ_two, Nat.cast_ofNat] at h
  linarith

theorem cdf_le_comonotonic (C : Copula 2) (u : Fin 2 → I) :
    C.cdf u ≤ (comonotonic 2).cdf u := by
  rw [cdf_comonotonic_two]
  exact le_min (C.cdf_le_coord u 0) (C.cdf_le_coord u 1)

end ProbabilityTheory.Copula
