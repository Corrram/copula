/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Chatterjee

/-! # Conditional kernels and xi for independence and functional dependence -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem conditionalKernel_independence :
    (independence 2).conditionalKernel =ᵐ[volume] Kernel.const I (volume : Measure I) := by
  have h := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := (independence 2).toMeasure) (mα := inferInstance) (mβ := inferInstance)
    (measurable_pi_apply (0 : Fin 2)) (measurable_pi_apply (1 : Fin 2))
    (κ := Kernel.const I (volume : Measure I)) (by
      rw [(independence 2).map_eval, Measure.compProd_const]
      exact (measurePreserving_finTwoArrow (volume : Measure I)).map_eq)
  simpa only [conditionalKernel, map_eval] using h

/-- Functional dependence identifies the conditional kernel almost everywhere. -/
theorem conditionalKernel_of_function (C : Copula 2) {f : I → I} (hf : Measurable f)
    (h : ∀ᵐ x ∂C.toMeasure, x 1 = f (x 0)) :
    C.conditionalKernel =ᵐ[volume] Kernel.deterministic f hf := by
  have he := condDistrib_congr_left (μ := C.toMeasure) (mα := inferInstance)
    (mβ := inferInstance) (X := fun x : Fin 2 → I => x 0) h
  have hc := condDistrib_comp_self (μ := C.toMeasure) (mα := inferInstance)
    (mβ := inferInstance) (X := fun x : Fin 2 → I => x 0)
    (measurable_pi_apply 0).aemeasurable hf
  rw [C.map_eval] at hc
  unfold conditionalKernel
  rw [he]
  exact hc

@[simp] theorem chatterjeeXi_independence : (independence 2).chatterjeeXi = 0 := by
  rw [chatterjeeXi_eq_of_kernel_ae _ _ conditionalKernel_independence]
  simp [Measure.real, unitInterval.volume_Iic, ENNReal.toReal_ofReal unitInterval.nonneg']
  norm_num

/-- Xi is one whenever the second coordinate is a measurable function of the first. -/
theorem chatterjeeXi_eq_one_of_function (C : Copula 2) {f : I → I} (hf : Measurable f)
    (h : ∀ᵐ x ∂C.toMeasure, x 1 = f (x 0)) : C.chatterjeeXi = 1 := by
  have hk := C.conditionalKernel_of_function hf h
  have hs (t : I) : (∫ u : I, C.conditionalCDF u t ^ 2) = (t : ℝ) := by
    rw [← C.integral_conditionalCDF t]
    apply integral_congr_ae
    filter_upwards [hk] with u hu
    simp only [conditionalCDF, hu, Kernel.deterministic_apply, Measure.real,
      Measure.dirac_apply' _ measurableSet_Iic, Set.indicator]
    split_ifs <;> norm_num
  simp_rw [chatterjeeXi, hs]
  rw [integral_unit_id]
  norm_num

@[simp] theorem chatterjeeXi_comonotonic : (comonotonic 2).chatterjeeXi = 1 := by
  apply chatterjeeXi_eq_one_of_function _ measurable_id
  rw [toMeasure_comonotonic]
  apply (ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2
  exact Filter.Eventually.of_forall fun _ => rfl

@[simp] theorem chatterjeeXi_countermonotonic : countermonotonic.chatterjeeXi = 1 := by
  apply chatterjeeXi_eq_one_of_function _ unitInterval.continuous_symm.measurable
  rw [toMeasure_countermonotonic]
  apply (ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2
  exact Filter.Eventually.of_forall fun _ => rfl

end ProbabilityTheory.Copula
