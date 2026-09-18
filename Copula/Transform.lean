/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Basic

/-!
# Coordinate transformations

Selecting coordinates preserves copulas. The selection need not be injective:
repeating a coordinate is allowed and introduces perfect dependence. Coordinate
permutations are a special case.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {d e f : ℕ}

/-- Select, reorder, or repeat coordinates of a copula. -/
noncomputable def reindex (C : Copula d) (ρ : Fin e → Fin d) : Copula e :=
  ofMap C.measure (fun x i => x (ρ i))
    (Measurable.of_eval fun i => measurable_pi_apply (ρ i)) (fun i => C.map_eval (ρ i))

@[simp]
theorem toMeasure_reindex (C : Copula d) (ρ : Fin e → Fin d) :
    (C.reindex ρ).toMeasure = C.toMeasure.map (fun x i => x (ρ i)) := rfl

@[simp]
theorem reindex_id (C : Copula d) : C.reindex id = C := by
  apply ext
  simp

theorem reindex_reindex (C : Copula d) (ρ : Fin e → Fin d) (η : Fin f → Fin e) :
    (C.reindex ρ).reindex η = C.reindex (ρ ∘ η) := by
  apply ext
  simp only [toMeasure_reindex]
  exact Measure.map_map
    (Measurable.of_eval fun i => measurable_pi_apply (η i))
    (Measurable.of_eval fun i => measurable_pi_apply (ρ i))

/-- Applying a coordinate permutation and its inverse recovers the copula. -/
@[simp]
theorem reindex_equiv_symm (C : Copula d) (ρ : Fin e ≃ Fin d) :
    (C.reindex ρ).reindex ρ.symm = C := by
  simp only [reindex_reindex, Function.comp_def, Equiv.apply_symm_apply]
  exact C.reindex_id

end ProbabilityTheory.Copula
