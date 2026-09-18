/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The Laplace transform of a gamma law

Exponential tilting changes the rate of a gamma density. Normalizing the tilted
density gives its Laplace transform without an interchange of improper integrals.
-/

open MeasureTheory Real Set
open scoped ENNReal

namespace ProbabilityTheory

/-- Exponential tilting of a rate-one gamma density. -/
theorem gammaPDF_mul_exp_neg {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (x : ℝ) :
    gammaPDF a 1 x * ENNReal.ofReal (exp (-(t * x))) =
      ENNReal.ofReal ((1 + t) ^ (-a)) * gammaPDF a (1 + t) x := by
  have ht' : 0 < 1 + t := by positivity
  have hga : 0 < Gamma a := Gamma_pos_of_pos ha
  by_cases hx : 0 ≤ x
  · rw [gammaPDF_of_nonneg hx, gammaPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [one_rpow, one_mul, mul_assoc, ← exp_add]
    have he : -x + -(t * x) = -((1 + t) * x) := by ring
    rw [he, rpow_neg ht'.le]
    field_simp
  · simp [gammaPDF_of_neg (lt_of_not_ge hx)]

/-- The Laplace transform of a gamma variable with shape `a` and rate one. -/
theorem lintegral_exp_neg_gammaMeasure {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    ∫⁻ x, ENNReal.ofReal (exp (-(t * x))) ∂gammaMeasure a 1 =
      ENNReal.ofReal ((1 + t) ^ (-a)) := by
  rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _
    ((measurable_gammaPDFReal a 1).ennreal_ofReal) (by fun_prop)]
  simp only [Pi.mul_apply, gammaPDF_mul_exp_neg ha ht]
  rw [lintegral_const_mul _ ((measurable_gammaPDFReal a (1 + t)).ennreal_ofReal),
    lintegral_gammaPDF_eq_one ha (by positivity),
    mul_one]

/-- Gamma variables with positive parameters are strictly positive almost surely. -/
theorem ae_pos_gammaMeasure (a r : ℝ) : ∀ᵐ x ∂gammaMeasure a r, 0 < x := by
  rw [ae_iff]
  have h : {x : ℝ | ¬0 < x} = Iic 0 := by ext x; simp
  rw [h]
  have hn : gammaMeasure a r (Iio 0) = 0 := by
    rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  have : NullSingletonClass (gammaMeasure a r) := by unfold gammaMeasure; infer_instance
  rw [← measure_congr Iio_ae_eq_Iic]
  exact hn

end ProbabilityTheory
