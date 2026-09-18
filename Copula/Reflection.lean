/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Basic

/-! # Coordinate reflections of copulas -/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- Reflect exactly the coordinates in `s`. -/
def reflectPoint (s : Finset (Fin d)) (x : Fin d → I) (i : Fin d) : I :=
  if i ∈ s then unitInterval.symm (x i) else x i

theorem measurable_reflectPoint (s : Finset (Fin d)) : Measurable (reflectPoint s) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i ∈ s
  · simpa [reflectPoint, hi] using unitInterval.measurable_symm.comp (measurable_pi_apply i)
  · simpa [reflectPoint, hi] using (measurable_pi_apply i : Measurable (fun x : Fin d → I => x i))

@[simp]
theorem reflectPoint_reflectPoint (s : Finset (Fin d)) (x : Fin d → I) :
    reflectPoint s (reflectPoint s x) = x := by
  funext i
  by_cases hi : i ∈ s <;> simp [reflectPoint, hi]

/-- Uniform marginals are preserved by reflection about `1/2`. -/
noncomputable def reflect (C : Copula d) (s : Finset (Fin d)) : Copula d :=
  ofMap C.measure (reflectPoint s) (measurable_reflectPoint s) (by
    intro i
    by_cases hi : i ∈ s
    · simp only [reflectPoint, hi, ↓reduceIte]
      rw [← Measure.map_map unitInterval.measurable_symm (measurable_pi_apply i), C.map_eval]
      exact unitInterval.measurePreserving_symm.map_eq
    · simpa only [reflectPoint, hi, ↓reduceIte] using C.map_eval i)

@[simp]
theorem toMeasure_reflect (C : Copula d) (s : Finset (Fin d)) :
    (C.reflect s).toMeasure = C.toMeasure.map (reflectPoint s) := rfl

@[simp]
theorem reflect_empty (C : Copula d) : C.reflect ∅ = C := by
  apply ext
  simp [reflectPoint]

/-- Reflection is an involution, including for the empty cube. -/
@[simp]
theorem reflect_reflect (C : Copula d) (s : Finset (Fin d)) :
    (C.reflect s).reflect s = C := by
  apply ext
  rw [toMeasure_reflect, toMeasure_reflect,
    Measure.map_map (measurable_reflectPoint s) (measurable_reflectPoint s)]
  simpa only [Function.comp_def, reflectPoint_reflectPoint] using Measure.map_id

theorem reflect_injective (s : Finset (Fin d)) : Function.Injective (fun C : Copula d => C.reflect s) :=
  Function.LeftInverse.injective (fun C => C.reflect_reflect s)

end ProbabilityTheory.Copula
