/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Countermonotonic

/-! # Almost-sure characterizations of the bivariate Fréchet bounds

Uniform coordinates agree almost surely exactly for the comonotonic copula.
They sum to one almost surely exactly for the countermonotonic copula.
These statements apply to arbitrary copula measures, including singular ones.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem ae_eval_eq_comonotonic :
    ∀ᵐ x ∂(comonotonic 2).toMeasure, x 0 = x 1 := by
  rw [toMeasure_comonotonic]
  apply (ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2
  exact Filter.Eventually.of_forall fun _ => rfl

theorem eq_comonotonic_iff_ae_eval_eq (C : Copula 2) :
    C = comonotonic 2 ↔ ∀ᵐ x ∂C.toMeasure, x 0 = x 1 := by
  refine ⟨fun h => h ▸ ae_eval_eq_comonotonic, fun h => ?_⟩
  apply ext
  rw [toMeasure_comonotonic, ← C.map_eval 0,
    Measure.map_map (by fun_prop) (by fun_prop)]
  calc
    C.toMeasure = C.toMeasure.map id := Measure.map_id.symm
    _ = _ := Measure.map_congr (by
      filter_upwards [h] with x hx
      funext i
      fin_cases i
      · rfl
      · exact hx.symm)

theorem ae_eval_eq_symm_countermonotonic :
    ∀ᵐ x ∂countermonotonic.toMeasure, x 1 = unitInterval.symm (x 0) := by
  rw [toMeasure_countermonotonic]
  apply (ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2
  exact Filter.Eventually.of_forall fun _ => rfl

theorem eq_countermonotonic_iff_ae_eval_eq_symm (C : Copula 2) :
    C = countermonotonic ↔ ∀ᵐ x ∂C.toMeasure, x 1 = unitInterval.symm (x 0) := by
  refine ⟨fun h => h ▸ ae_eval_eq_symm_countermonotonic, fun h => ?_⟩
  apply ext
  rw [toMeasure_countermonotonic, ← C.map_eval 0,
    Measure.map_map (by fun_prop) (by fun_prop)]
  calc
    C.toMeasure = C.toMeasure.map id := Measure.map_id.symm
    _ = _ := Measure.map_congr (by
      filter_upwards [h] with x hx
      funext i
      fin_cases i
      · rfl
      · exact hx)

theorem eq_countermonotonic_iff_ae_add_eq_one (C : Copula 2) :
    C = countermonotonic ↔ ∀ᵐ x ∂C.toMeasure, (x 0 : ℝ) + x 1 = 1 := by
  rw [C.eq_countermonotonic_iff_ae_eval_eq_symm]
  constructor
  · intro h
    filter_upwards [h] with x hx
    rw [hx, unitInterval.coe_symm_eq]
    ring
  · intro h
    filter_upwards [h] with x hx
    apply Subtype.ext
    simp only [unitInterval.coe_symm_eq]
    linarith

end ProbabilityTheory.Copula
