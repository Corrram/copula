/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Spearman

/-! # The CDF integral formula and concordance monotonicity of Spearman's rho -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem integral_unit_upper_indicator (u : I) :
    (∫ t : I, if u ≤ t then (1 : ℝ) else 0) = 1 - (u : ℝ) := by
  classical
  have h := integral_indicator_one (μ := (volume : Measure I)) measurableSet_Ici
    (s := Ici u)
  simpa [Set.indicator, Measure.real, unitInterval.volume_Ici,
    ENNReal.toReal_ofReal (sub_nonneg.mpr u.property.2)] using h

/-- The uniform CDF integral equals the mixed first moment. -/
theorem integral_cdf_independence (C : Copula 2) :
    (∫ x, C.cdf x ∂(independence 2).toMeasure) =
      ∫ x, (x 0 : ℝ) * (x 1 : ℝ) ∂C.toMeasure := by
  classical
  have hf : Integrable (fun p : (Fin 2 → I) × (Fin 2 → I) =>
      if p.2 ≤ p.1 then (1 : ℝ) else 0) ((independence 2).toMeasure.prod C.toMeasure) := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (measurable_const.ite (measurableSet_le measurable_snd measurable_fst)
        measurable_const).aestronglyMeasurable
    · split_ifs <;> norm_num
  have hc (x : Fin 2 → I) : C.cdf x =
      ∫ y, if y ≤ x then (1 : ℝ) else 0 ∂C.toMeasure := by
    symm
    simpa [Set.indicator, cdf] using
      integral_indicator_one (μ := C.toMeasure) (s := Iic x) measurableSet_Iic
  have hi (y : Fin 2 → I) :
      (∫ x, if y ≤ x then (1 : ℝ) else 0 ∂(independence 2).toMeasure) =
        (1 - (y 0 : ℝ)) * (1 - (y 1 : ℝ)) := by
    have he : (fun x : Fin 2 → I => if y ≤ x then (1 : ℝ) else 0) =
        fun x => (if y 0 ≤ x 0 then (1 : ℝ) else 0) *
          (if y 1 ≤ x 1 then (1 : ℝ) else 0) := by
      funext x
      simp only [Pi.le_def, Fin.forall_fin_two]
      by_cases h0 : y 0 ≤ x 0 <;> by_cases h1 : y 1 ≤ x 1 <;> simp [h0, h1]
    rw [he, integral_independence_mul (fun t : I => if y 0 ≤ t then (1 : ℝ) else 0)
      (fun t : I => if y 1 ≤ t then (1 : ℝ) else 0),
      integral_unit_upper_indicator, integral_unit_upper_indicator]
  calc
    (∫ x, C.cdf x ∂(independence 2).toMeasure) =
        ∫ x, ∫ y, if y ≤ x then (1 : ℝ) else 0 ∂C.toMeasure ∂(independence 2).toMeasure := by
      simp_rw [hc]
    _ = ∫ y, ∫ x, if y ≤ x then (1 : ℝ) else 0 ∂(independence 2).toMeasure ∂C.toMeasure :=
      integral_integral_swap hf
    _ = ∫ y, (1 - (y 0 : ℝ)) * (1 - (y 1 : ℝ)) ∂C.toMeasure := by simp_rw [hi]
    _ = ∫ y, (y 0 : ℝ) * (y 1 : ℝ) ∂C.toMeasure := by
      have he : (fun y : Fin 2 → I => (1 - (y 0 : ℝ)) * (1 - (y 1 : ℝ))) =
          fun y : Fin 2 → I => 1 - (y 0 : ℝ) - (y 1 : ℝ) + (y 0 : ℝ) * (y 1 : ℝ) := by
        funext y; ring
      rw [he, integral_add, integral_sub, integral_sub, C.integral_coe_eval, C.integral_coe_eval]
      · norm_num
      all_goals exact integrable_continuous_cube C.toMeasure (by fun_prop)

theorem spearmanRho_eq_integral_cdf (C : Copula 2) :
    C.spearmanRho = 12 * (∫ x, C.cdf x ∂(independence 2).toMeasure) - 3 := by
  rw [integral_cdf_independence]
  rfl

theorem spearmanRho_mono {C D : Copula 2} (h : ∀ u, C.cdf u ≤ D.cdf u) :
    C.spearmanRho ≤ D.spearmanRho := by
  rw [C.spearmanRho_eq_integral_cdf, D.spearmanRho_eq_integral_cdf]
  have hi := integral_mono (C.integrable_cdf (independence 2).toMeasure)
    (D.integrable_cdf (independence 2).toMeasure) h
  linarith

end ProbabilityTheory.Copula
