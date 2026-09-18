/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.Conditional
import Copula.Dependence.Rank

/-! # Independence, comonotonicity and failures at countermonotonicity -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem hasTP2Kernel_independence : (independence 2).HasTP2Kernel := by
  refine ⟨Kernel.const I (volume : Measure I), inferInstance, conditionalKernel_independence, ?_⟩
  intro a b c d _ _
  simp only [Kernel.const_apply]
  exact le_of_eq (mul_comm _ _)

theorem hasTP2Kernel_comonotonic : (comonotonic 2).HasTP2Kernel := by
  classical
  refine ⟨Kernel.deterministic id measurable_id, inferInstance, ?_, ?_⟩
  · apply conditionalKernel_of_function _ measurable_id
    rw [toMeasure_comonotonic]
    apply (ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2
    exact Filter.Eventually.of_forall fun _ => rfl
  · intro a b c d hab hcd
    simp only [Kernel.deterministic_apply, Measure.real, Measure.dirac_apply' _ measurableSet_Iic,
      Set.indicator, Set.mem_Iic, id_eq, Pi.one_apply]
    by_cases hbc : b ≤ c
    · simp [hbc, hab.trans hbc, hbc.trans hcd, (hab.trans hbc).trans hcd]
    · simp only [hbc, ite_false, ENNReal.toReal_zero, mul_zero]
      positivity

theorem isSI_independence : (independence 2).IsSI := hasTP2Kernel_independence.isSI

theorem isSI_comonotonic : (comonotonic 2).IsSI := hasTP2Kernel_comonotonic.isSI

theorem isTP2CDF_comonotonic : (comonotonic 2).IsTP2CDF := by
  intro a b c d hab hcd
  simp only [cdf_comonotonic_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hab' : (a : ℝ) ≤ (b : ℝ) := hab
  have hcd' : (c : ℝ) ≤ (d : ℝ) := hcd
  by_cases hbc : (b : ℝ) ≤ (c : ℝ)
  · rw [min_eq_left (hab'.trans (hbc.trans hcd')), min_eq_left hbc,
      min_eq_left (hab'.trans hbc), min_eq_left (hbc.trans hcd')]
  · by_cases had : (d : ℝ) ≤ (a : ℝ)
    · rw [min_eq_right had, min_eq_right (hcd'.trans (had.trans hab')),
        min_eq_right (hcd'.trans had), min_eq_right (had.trans hab')]
      exact le_of_eq (mul_comm _ _)
    · rw [min_eq_left (le_of_not_ge had), min_eq_right (le_of_not_ge hbc)]
      rcases le_total (a : ℝ) (c : ℝ) with hac | hca
      · rw [min_eq_left hac]
        exact mul_le_mul_of_nonneg_left (le_min (le_of_not_ge hbc) hcd') a.property.1
      · rw [min_eq_right hca]
        nlinarith [mul_le_mul_of_nonneg_left (le_min hab' (le_of_not_ge had)) c.property.1]

theorem isPQD_independence : (independence 2).IsPQD := isSI_independence.isPQD
theorem isLTD_independence : (independence 2).IsLTD := isSI_independence.isLTD
theorem isRTI_independence : (independence 2).IsRTI := isSI_independence.isRTI
theorem isPQD_comonotonic : (comonotonic 2).IsPQD := isSI_comonotonic.isPQD
theorem isLTD_comonotonic : (comonotonic 2).IsLTD := isSI_comonotonic.isLTD
theorem isRTI_comonotonic : (comonotonic 2).IsRTI := isSI_comonotonic.isRTI

theorem not_isPQD_countermonotonic : ¬ countermonotonic.IsPQD := by
  intro h
  have hb := h.blomqvistBeta_nonneg
  norm_num at hb

theorem not_isLTD_countermonotonic : ¬ countermonotonic.IsLTD :=
  fun h => not_isPQD_countermonotonic h.isPQD
theorem not_isRTI_countermonotonic : ¬ countermonotonic.IsRTI :=
  fun h => not_isPQD_countermonotonic h.isPQD
theorem not_isSI_countermonotonic : ¬ countermonotonic.IsSI :=
  fun h => not_isPQD_countermonotonic h.isPQD
theorem not_isTP2CDF_countermonotonic : ¬ countermonotonic.IsTP2CDF :=
  fun h => not_isPQD_countermonotonic h.isPQD
theorem not_hasTP2Kernel_countermonotonic : ¬ countermonotonic.HasTP2Kernel :=
  fun h => not_isSI_countermonotonic h.isSI

end ProbabilityTheory.Copula
