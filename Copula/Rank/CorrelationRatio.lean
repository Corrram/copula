/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.ChatterjeeExamples
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # The directional copula correlation ratio

For uniform coordinates `(U,V)`, the ratio is `Var(E[V | U]) / Var(V)`.
Since `Var(V) = 1/12`, it is twelve times the squared conditional-mean
deviation from `1/2`. This is the variance ratio itself, without a square root.
It vanishes exactly when the conditional mean is constant; it need not detect
independence. Regular conditional kernels also cover singular copulas.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Conditional mean of the second uniform coordinate given the first. -/
noncomputable def conditionalMean (C : Copula 2) (u : I) : ℝ :=
  ∫ v : I, (v : ℝ) ∂C.conditionalKernel u

theorem measurable_conditionalMean (C : Copula 2) : Measurable C.conditionalMean :=
  (measurable_subtype_coe.stronglyMeasurable.integral_kernel).measurable

/-- Averaging a continuous function against the conditional laws recovers the
uniform second marginal. -/
theorem integral_conditionalKernel (C : Copula 2) (f : I → ℝ) (hf : Continuous f) :
    (∫ u : I, ∫ v, f v ∂C.conditionalKernel u) = ∫ v : I, f v := by
  have hi : Integrable f ((C.conditionalKernel ∘ₖ Kernel.const Unit (volume : Measure I)) ()) := by
    rw [← Measure.comp_eq_comp_const_apply, C.conditionalKernel_comp_volume]
    exact integrable_continuous_unit volume hf
  have h := Kernel.integral_comp hi
  rw [← Measure.comp_eq_comp_const_apply, C.conditionalKernel_comp_volume] at h
  exact h.symm

theorem integrable_conditionalKernel_integral (C : Copula 2) (f : I → ℝ)
    (hf : Continuous f) : Integrable (fun u => ∫ v, f v ∂C.conditionalKernel u) := by
  have hi : Integrable f ((C.conditionalKernel ∘ₖ Kernel.const Unit (volume : Measure I)) ()) := by
    rw [← Measure.comp_eq_comp_const_apply, C.conditionalKernel_comp_volume]
    exact integrable_continuous_unit volume hf
  exact hi.integral_comp

theorem conditionalMean_mem_Icc (C : Copula 2) (u : I) : C.conditionalMean u ∈ Icc 0 1 := by
  constructor
  · exact integral_nonneg (fun v => v.property.1)
  · have h := integral_mono (integrable_continuous_unit (C.conditionalKernel u) continuous_subtype_val)
      (integrable_const (1 : ℝ)) (fun v : I => v.property.2)
    simpa [conditionalMean] using h

@[simp] theorem integral_conditionalMean (C : Copula 2) : (∫ u : I, C.conditionalMean u) = 1 / 2 := by
  unfold conditionalMean
  rw [C.integral_conditionalKernel _ continuous_subtype_val, integral_unit_id]

theorem integrable_conditionalMean_centered_sq (C : Copula 2) :
    Integrable (fun u => (C.conditionalMean u - 1 / 2) ^ 2) := by
  refine (integrable_const (1 : ℝ)).mono'
    ((C.measurable_conditionalMean.sub measurable_const).pow_const 2).aestronglyMeasurable ?_
  apply Filter.Eventually.of_forall
  intro u
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := C.conditionalMean_mem_Icc u
  nlinarith [h.1, h.2]

/-- The copula correlation ratio, predicting coordinate 1 from coordinate 0. -/
noncomputable def copulaCorrelationRatio (C : Copula 2) : ℝ :=
  12 * ∫ u : I, (C.conditionalMean u - 1 / 2) ^ 2

theorem copulaCorrelationRatio_nonneg (C : Copula 2) : 0 ≤ C.copulaCorrelationRatio :=
  mul_nonneg (by norm_num) (integral_nonneg (fun _ => sq_nonneg _))

theorem conditionalMean_centered_sq_le (C : Copula 2) (u : I) :
    (C.conditionalMean u - 1 / 2) ^ 2 ≤
      ∫ v : I, ((v : ℝ) - 1 / 2) ^ 2 ∂C.conditionalKernel u := by
  have hm : (∫ v : I, (v : ℝ) - 1 / 2 ∂C.conditionalKernel u) = C.conditionalMean u - 1 / 2 := by
    rw [integral_sub (integrable_continuous_unit _ continuous_subtype_val) (integrable_const _)]
    simp [conditionalMean]
  have hn : 0 ≤ ∫ v : I, (((v : ℝ) - 1 / 2) - (C.conditionalMean u - 1 / 2)) ^ 2
      ∂C.conditionalKernel u := integral_nonneg (fun _ => sq_nonneg _)
  have he : (fun v : I => (((v : ℝ) - 1 / 2) - (C.conditionalMean u - 1 / 2)) ^ 2) =
      fun v : I => ((v : ℝ) - 1 / 2) ^ 2 -
        (2 * (C.conditionalMean u - 1 / 2)) * ((v : ℝ) - 1 / 2) +
        (C.conditionalMean u - 1 / 2) ^ 2 := by funext v; ring
  rw [he, integral_add, integral_sub, integral_const_mul, hm] at hn
  · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hn
    nlinarith
  all_goals exact integrable_continuous_unit _ (by fun_prop)

theorem integral_unit_centered_sq : (∫ v : I, ((v : ℝ) - 1 / 2) ^ 2) = 1 / 12 := by
  have he : (fun v : I => ((v : ℝ) - 1 / 2) ^ 2) =
      fun v : I => (v : ℝ) ^ 2 - (v : ℝ) + 1 / 4 := by funext v; ring
  rw [he, integral_add, integral_sub, integral_unit_pow, integral_unit_id]
  · norm_num
  all_goals exact integrable_continuous_unit _ (by fun_prop)

theorem copulaCorrelationRatio_le_one (C : Copula 2) : C.copulaCorrelationRatio ≤ 1 := by
  have h := integral_mono C.integrable_conditionalMean_centered_sq
    (C.integrable_conditionalKernel_integral _ (by fun_prop)) C.conditionalMean_centered_sq_le
  rw [C.integral_conditionalKernel _ (by fun_prop), integral_unit_centered_sq] at h
  unfold copulaCorrelationRatio
  linarith

theorem copulaCorrelationRatio_mem_Icc (C : Copula 2) : C.copulaCorrelationRatio ∈ Icc 0 1 :=
  ⟨C.copulaCorrelationRatio_nonneg, C.copulaCorrelationRatio_le_one⟩

theorem copulaCorrelationRatio_eq_zero_iff (C : Copula 2) :
    C.copulaCorrelationRatio = 0 ↔ ∀ᵐ u : I, C.conditionalMean u = 1 / 2 := by
  constructor
  · intro h
    have hz : (∫ u : I, (C.conditionalMean u - 1 / 2) ^ 2) = 0 := by
      unfold copulaCorrelationRatio at h
      linarith
    have he := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun u => sq_nonneg (C.conditionalMean u - 1 / 2)))
      C.integrable_conditionalMean_centered_sq).1 hz
    filter_upwards [he] with u hu
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hu)
  · intro h
    have hz : (∫ u : I, (C.conditionalMean u - 1 / 2) ^ 2) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [h] with u hu
      simp [hu]
    rw [copulaCorrelationRatio, hz, mul_zero]

/-- Changing versions of the conditional kernel does not change the ratio. -/
theorem copulaCorrelationRatio_eq_of_kernel_ae (C : Copula 2) (κ : Kernel I I)
    (hκ : C.conditionalKernel =ᵐ[volume] κ) :
    C.copulaCorrelationRatio = 12 * ∫ u : I, ((∫ v : I, (v : ℝ) ∂κ u) - 1 / 2) ^ 2 := by
  unfold copulaCorrelationRatio conditionalMean
  congr 1
  apply integral_congr_ae
  filter_upwards [hκ] with u hu
  rw [hu]

@[simp] theorem copulaCorrelationRatio_independence :
    (independence 2).copulaCorrelationRatio = 0 := by
  rw [copulaCorrelationRatio_eq_of_kernel_ae _ _ conditionalKernel_independence]
  simp

/-- A measurable deterministic response has maximal correlation ratio. -/
theorem copulaCorrelationRatio_eq_one_of_function (C : Copula 2) {f : I → I}
    (hf : Measurable f) (h : ∀ᵐ x ∂C.toMeasure, x 1 = f (x 0)) :
    C.copulaCorrelationRatio = 1 := by
  have hk := C.conditionalKernel_of_function hf h
  have hi := C.integral_conditionalKernel (fun v : I => ((v : ℝ) - 1 / 2) ^ 2) (by fun_prop)
  rw [integral_unit_centered_sq] at hi
  have he : (∫ u : I, (C.conditionalMean u - 1 / 2) ^ 2) =
      ∫ u : I, ∫ v : I, ((v : ℝ) - 1 / 2) ^ 2 ∂C.conditionalKernel u := by
    apply integral_congr_ae
    filter_upwards [hk] with u hu
    simp [conditionalMean, hu, Kernel.deterministic_apply]
  rw [copulaCorrelationRatio, he, hi]
  norm_num

@[simp] theorem copulaCorrelationRatio_comonotonic :
    (comonotonic 2).copulaCorrelationRatio = 1 := by
  apply copulaCorrelationRatio_eq_one_of_function _ measurable_id
  rw [toMeasure_comonotonic]
  apply (ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2
  exact Filter.Eventually.of_forall (fun _ => rfl)

@[simp] theorem copulaCorrelationRatio_countermonotonic :
    countermonotonic.copulaCorrelationRatio = 1 := by
  apply copulaCorrelationRatio_eq_one_of_function _ unitInterval.continuous_symm.measurable
  rw [toMeasure_countermonotonic]
  apply (ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2
  exact Filter.Eventually.of_forall (fun _ => rfl)

end ProbabilityTheory.Copula
