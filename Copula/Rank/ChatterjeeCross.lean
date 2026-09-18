/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.ConditionalDistance
import Copula.Rank.Benchmarks

/-! # The polarized conditional-CDF functional

This symmetric cross term gives the quadratic mixture formula for xi. Its
diagonal is xi itself, its value at independence is zero, and pairing with
comonotonicity gives Spearman's footrule.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem integrable_conditionalCDF_mul (C D : Copula 2) (v : I) :
    Integrable (fun u => C.conditionalCDF u v * D.conditionalCDF u v) := by
  refine (D.integrable_conditionalCDF v).mono'
    ((C.measurable_conditionalCDF_left v).mul
      (D.measurable_conditionalCDF_left v)).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (C.conditionalCDF_nonneg u v)
      (D.conditionalCDF_nonneg u v))]
    exact mul_le_of_le_one_left (D.conditionalCDF_nonneg u v) (C.conditionalCDF_le_one u v)

theorem integrable_integral_conditionalCDF_mul (C D : Copula 2) :
    Integrable (fun v : I => ∫ u : I, C.conditionalCDF u v * D.conditionalCDF u v) := by
  refine (integrable_const (1 : ℝ)).mono'
    (C.measurable_conditionalCDF.mul D.measurable_conditionalCDF).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun v => by
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun u =>
      mul_nonneg (C.conditionalCDF_nonneg u v) (D.conditionalCDF_nonneg u v))]
    have h := integral_mono (C.integrable_conditionalCDF_mul D v) (D.integrable_conditionalCDF v)
      (fun u => mul_le_of_le_one_left (D.conditionalCDF_nonneg u v) (C.conditionalCDF_le_one u v))
    rw [D.integral_conditionalCDF] at h
    exact h.trans v.property.2

/-- Symmetric polarization of xi, normalized so that pairing with independence is zero.
Unlike xi itself, this cross functional can be negative. -/
noncomputable def chatterjeeCross (C D : Copula 2) : ℝ :=
  6 * (∫ v : I, ∫ u : I, C.conditionalCDF u v * D.conditionalCDF u v) - 2

theorem chatterjeeCross_comm (C D : Copula 2) : C.chatterjeeCross D = D.chatterjeeCross C := by
  simp only [chatterjeeCross, mul_comm]

@[simp] theorem chatterjeeCross_self (C : Copula 2) : C.chatterjeeCross C = C.chatterjeeXi := by
  simp only [chatterjeeCross, chatterjeeXi, pow_two]

@[simp] theorem chatterjeeCross_independence (C : Copula 2) :
    C.chatterjeeCross (independence 2) = 0 := by
  have he (v : I) :
      (∫ u : I, C.conditionalCDF u v * (independence 2).conditionalCDF u v) = (v : ℝ) ^ 2 := by
    calc
      _ = ∫ u : I, C.conditionalCDF u v * (v : ℝ) := integral_congr_ae (by
        filter_upwards [conditionalCDF_independence v] with u hu
        rw [hu])
      _ = _ := by rw [integral_mul_const, C.integral_conditionalCDF, pow_two]
  simp only [chatterjeeCross, he, integral_unit_pow]
  norm_num

@[simp] theorem chatterjeeCross_independence_left (C : Copula 2) :
    (independence 2).chatterjeeCross C = 0 := by
  rw [chatterjeeCross_comm, chatterjeeCross_independence]

theorem conditionalCDFDistanceSq_eq_cross (C D : Copula 2) :
    6 * C.conditionalCDFDistanceSq D = C.chatterjeeXi + D.chatterjeeXi - 2 * C.chatterjeeCross D := by
  have he (v : I) : (∫ u : I, (C.conditionalCDF u v - D.conditionalCDF u v) ^ 2) =
      (∫ u : I, C.conditionalCDF u v ^ 2) + (∫ u : I, D.conditionalCDF u v ^ 2) -
        2 * (∫ u : I, C.conditionalCDF u v * D.conditionalCDF u v) := by
    have hp : (fun u : I => (C.conditionalCDF u v - D.conditionalCDF u v) ^ 2) =
        fun u => C.conditionalCDF u v ^ 2 + D.conditionalCDF u v ^ 2 -
          2 * (C.conditionalCDF u v * D.conditionalCDF u v) := by funext u; ring
    have hs : Integrable (fun u : I => C.conditionalCDF u v ^ 2 + D.conditionalCDF u v ^ 2) :=
      (C.integrable_conditionalCDF_sq v).add (D.integrable_conditionalCDF_sq v)
    rw [hp, integral_sub hs
      ((C.integrable_conditionalCDF_mul D v).const_mul 2),
      integral_add (C.integrable_conditionalCDF_sq v) (D.integrable_conditionalCDF_sq v),
      integral_const_mul]
  simp only [conditionalCDFDistanceSq, he]
  have hs : Integrable (fun v : I => (∫ u : I, C.conditionalCDF u v ^ 2) +
      (∫ u : I, D.conditionalCDF u v ^ 2)) :=
    C.integrable_integral_conditionalCDF_sq.add D.integrable_integral_conditionalCDF_sq
  rw [integral_sub hs
      ((C.integrable_integral_conditionalCDF_mul D).const_mul 2),
    integral_add C.integrable_integral_conditionalCDF_sq D.integrable_integral_conditionalCDF_sq,
    integral_const_mul]
  unfold chatterjeeXi chatterjeeCross
  ring

theorem conditionalCDF_comonotonic (v : I) :
    (fun u => (comonotonic 2).conditionalCDF u v) =ᵐ[volume]
      (Iic v).indicator (fun _ => (1 : ℝ)) := by
  have hk := (comonotonic 2).conditionalKernel_of_function measurable_id (by
    rw [toMeasure_comonotonic]
    apply (ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2
    exact Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [hk] with u hu
  simp [conditionalCDF, hu, Kernel.deterministic_apply, Measure.real,
    Measure.dirac_apply' _ measurableSet_Iic, Set.indicator]
  split_ifs <;> norm_num

/-- Pairing a conditional CDF with the deterministic increasing kernel recovers the diagonal. -/
theorem integral_conditionalCDF_mul_comonotonic (C : Copula 2) (v : I) :
    (∫ u : I, C.conditionalCDF u v * (comonotonic 2).conditionalCDF u v) = C.cdf ![v, v] := by
  calc
    _ = ∫ u : I, (Iic v).indicator (fun t => C.conditionalCDF t v) u := integral_congr_ae (by
      filter_upwards [conditionalCDF_comonotonic v] with u hu
      rw [hu]
      by_cases h : u ∈ Iic v <;> simp [h])
    _ = _ := by rw [integral_indicator measurableSet_Iic, C.cdf_eq_integral_conditionalCDF]

@[simp] theorem chatterjeeCross_comonotonic (C : Copula 2) :
    C.chatterjeeCross (comonotonic 2) = C.spearmanFootrule := by
  simp only [chatterjeeCross, integral_conditionalCDF_mul_comonotonic, spearmanFootrule]

end ProbabilityTheory.Copula
