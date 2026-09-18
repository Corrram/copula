/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.CDF
import Copula.Reflection
import Copula.Comonotonic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # The bivariate countermonotonic copula

The law of `(U, 1-U)` for a uniform `U` attains the bivariate lower
Fréchet–Hoeffding bound. No higher-dimensional version of that bound is asserted.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The law of a uniform variable paired with its reflection. -/
noncomputable def countermonotonic : Copula 2 :=
  ofMap ⟨volume, inferInstance⟩ (fun t => ![t, unitInterval.symm t])
    (Measurable.of_eval fun i => by fin_cases i <;> fun_prop) (by
      intro i
      fin_cases i
      · exact Measure.map_id
      · exact unitInterval.measurePreserving_symm.map_eq)

@[simp]
theorem toMeasure_countermonotonic : countermonotonic.toMeasure =
    (volume : Measure I).map (fun t => ![t, unitInterval.symm t]) := rfl

/-- Countermonotonicity is obtained by reflecting one coordinate of the diagonal law. -/
theorem reflect_comonotonic_eq_countermonotonic :
    (comonotonic 2).reflect {1} = countermonotonic := by
  apply ext
  rw [toMeasure_reflect, toMeasure_comonotonic]
  have hm : ((volume : Measure I).map (fun t : I => fun _ : Fin 2 => t)).map (reflectPoint {1}) =
      volume.map (reflectPoint {1} ∘ (fun t : I => fun _ : Fin 2 => t)) :=
    Measure.map_map (measurable_reflectPoint _) (Measurable.of_eval fun _ => measurable_id)
  rw [hm]
  have h : reflectPoint ({1} : Finset (Fin 2)) ∘ (fun t _ => t) =
      fun t : I => ![t, unitInterval.symm t] := by
    funext t i
    fin_cases i <;> simp [reflectPoint]
  rw [h, toMeasure_countermonotonic]

/-- The lower Fréchet–Hoeffding bound is attained in dimension two. -/
@[simp]
theorem cdf_countermonotonic (u : Fin 2 → I) :
    countermonotonic.cdf u = max 0 ((u 0 : ℝ) + (u 1 : ℝ) - 1) := by
  have hm : Measurable (fun t : I => ![t, unitInterval.symm t]) :=
    Measurable.of_eval fun i => by fin_cases i <;> fun_prop
  have hpre : (fun t : I => ![t, unitInterval.symm t]) ⁻¹' Iic u =
      Icc (unitInterval.symm (u 1)) (u 0) := by
    ext t
    simp [mem_Iic, Pi.le_def, Fin.forall_fin_two, unitInterval.symm_le_comm, and_comm]
  rw [cdf, toMeasure_countermonotonic, map_measureReal_apply hm measurableSet_Iic, hpre]
  simp only [Measure.real, unitInterval.volume_Icc, unitInterval.coe_symm_eq,
    ENNReal.toReal_ofReal']
  rw [max_comm]
  congr 1
  ring

end ProbabilityTheory.Copula
