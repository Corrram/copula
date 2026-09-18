/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Reflection
import Copula.Rectangle
import Copula.Dependence.Basic

/-! # Upper orthants and survival probabilities -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- Upper orthant probability, using closed coordinate orthants. Uniform marginals
make the choice of open or closed faces immaterial. -/
noncomputable def survival (C : Copula d) (u : Fin d → I) : ℝ :=
  C.toMeasure.real (Ici u)

theorem ae_eval_ne (C : Copula d) (i : Fin d) (t : I) :
    ∀ᵐ x ∂C.toMeasure, x i ≠ t := by
  rw [ae_iff]
  simpa only [Set.preimage, Set.mem_singleton_iff, not_not] using
    (C.measure_preimage_eval i (measurableSet_singleton t)).trans (measure_singleton t)

theorem survival_eq_strict (C : Copula d) (u : Fin d → I) :
    C.survival u = C.toMeasure.real {x | ∀ i, u i < x i} := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [ae_all_iff.2 (fun i => C.ae_eval_ne i (u i))] with x hx
  simp only [mem_Ici, Pi.le_def]
  exact propext (forall_congr' fun i => ⟨fun h => lt_of_le_of_ne h (hx i).symm, le_of_lt⟩)

theorem survival_eq_cdf_reflect (C : Copula d) (u : Fin d → I) :
    C.survival u = (C.reflect Finset.univ).cdf (reflectPoint Finset.univ u) := by
  rw [survival, cdf, toMeasure_reflect, map_measureReal_apply
    (measurable_reflectPoint _) measurableSet_Iic]
  congr 1
  ext x
  simp [reflectPoint, Pi.le_def]

theorem survival_two (C : Copula 2) (u : Fin 2 → I) :
    C.survival u = 1 - (u 0 : ℝ) - (u 1 : ℝ) + C.cdf u := by
  rw [C.survival_eq_strict]
  have he : {x : Fin 2 → I | ∀ i, u i < x i} =
      Set.pi univ (fun i => Ioc (u i) (1 : I)) := by
    ext x
    simp only [mem_ofPred_eq, mem_univ_pi, mem_Ioc]
    exact forall_congr' fun i => (and_iff_left (show x i ≤ 1 from (x i).property.2)).symm
  rw [he, C.measureReal_rectangle_two u (fun _ => 1) (fun _ => unitInterval.le_one _)]
  simp [C.cdf_one, C.cdf_two_one_left, C.cdf_two_one_right]

end ProbabilityTheory.Copula
