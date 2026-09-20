/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Vine.Family

/-! # Copula laws on coordinate subsets

Coordinates outside the active subset are padded by zero. This gives all
intermediate vine marginals the same ambient measurable space.
-/

open MeasureTheory Set Function
open scoped unitInterval

namespace ProbabilityTheory.Copula.Vine

variable {d : ℕ}

/-- Retain the coordinates in `s` and set the others to zero. -/
def project (s : Finset (Fin d)) (x : Fin d → I) (i : Fin d) : I :=
  if i ∈ s then x i else 0

theorem measurable_project (s : Finset (Fin d)) : Measurable (project s) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i ∈ s <;> simp only [project, hi, ite_true, ite_false] <;> fun_prop

theorem project_project {s t : Finset (Fin d)} (h : s ⊆ t) (x : Fin d → I) :
    project s (project t x) = project s x := by
  funext i
  by_cases hi : i ∈ s
  · simp [project, hi, h hi]
  · simp [project, hi]

/-- A copula on an active coordinate subset, padded by zeros elsewhere. -/
structure Marginal (s : Finset (Fin d)) where
  /-- The ambient probability law. -/
  measure : ProbabilityMeasure (Fin d → I)
  /-- Active coordinate laws are uniform. -/
  uniform (i : Fin d) (hi : i ∈ s) : measure.toMeasure.map (fun x => x i) = volume
  /-- Inactive coordinates are zero almost surely. -/
  supported : ∀ᵐ x ∂measure.toMeasure, project s x = x

namespace Marginal

variable {s t : Finset (Fin d)}

/-- The underlying probability measure. -/
def toMeasure (M : Marginal s) : Measure (Fin d → I) := M.measure.toMeasure

instance (M : Marginal s) : IsProbabilityMeasure M.toMeasure :=
  inferInstanceAs (IsProbabilityMeasure M.measure.toMeasure)

@[ext] theorem ext {L R : Marginal s} (h : L.toMeasure = R.toMeasure) : L = R := by
  cases L
  cases R
  congr
  exact ProbabilityMeasure.toMeasure_injective h

@[simp] theorem map_project_self (M : Marginal s) : M.toMeasure.map (project s) = M.toMeasure := by
  rw [Measure.map_congr (show project s =ᵐ[M.toMeasure] id from M.supported)]
  exact Measure.map_id

/-- Restrict a marginal to a smaller coordinate subset. -/
noncomputable def restrict (M : Marginal t) (h : s ⊆ t) : Marginal s where
  measure := M.measure.map (project s)
  uniform i hi := by
    rw [ProbabilityMeasure.toMeasure_map,
      Measure.map_map (measurable_pi_apply i) (measurable_project s)]
    simpa only [comp_def, project, hi, ite_true] using M.uniform i (h hi)
  supported := by
    rw [ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff (measurable_project s).aemeasurable
      (measurableSet_eq_fun (measurable_project s) measurable_id)).2
    exact Filter.Eventually.of_forall (fun x => project_project (s := s) (t := s) le_rfl x)

/-- The empty marginal is a point mass at the zero vector. -/
noncomputable def empty : Marginal (∅ : Finset (Fin d)) where
  measure := ⟨Measure.dirac (fun _ => 0), inferInstance⟩
  uniform i hi := False.elim (Finset.notMem_empty i hi)
  supported := by
    change ∀ᵐ x ∂Measure.dirac (fun _ : Fin d => (0 : I)), project ∅ x = x
    apply (ae_dirac_iff (measurableSet_eq_fun (measurable_project ∅) measurable_id)).2
    funext i
    simp [project]

/-- Regard an ordinary copula as a marginal on all coordinates. -/
def ofCopula (C : Copula d) : Marginal (Finset.univ : Finset (Fin d)) where
  measure := C.measure
  uniform i _ := C.map_eval i
  supported := Filter.Eventually.of_forall (by intro x; funext i; simp [project])

/-- A uniform single coordinate, padded by zeros. -/
noncomputable def singleton (i : Fin d) : Marginal {i} :=
  (ofCopula (independence d)).restrict (Finset.subset_univ {i})

/-- Convert a full-coordinate marginal to the library's copula type. -/
def toCopula (M : Marginal (Finset.univ : Finset (Fin d))) : Copula d where
  measure := M.measure
  marginal_eq i := M.uniform i (Finset.mem_univ i)

/-- Transport a marginal along equality of its active sets. -/
def cast (M : Marginal s) (h : s = t) : Marginal t := h ▸ M

@[simp] theorem toMeasure_cast (M : Marginal s) (h : s = t) :
    (M.cast h).toMeasure = M.toMeasure := by subst t; rfl

theorem map_empty (M : Marginal s) :
    M.toMeasure.map (project ∅) = (empty (d := d)).toMeasure := by
  have he : project (∅ : Finset (Fin d)) = (fun _ : Fin d → I => fun _ => (0 : I)) := by
    funext x i
    simp [project]
  rw [he]
  simp [empty, toMeasure]

theorem toMeasure_eq_uniform_singleton (i : Fin d) (M : Marginal {i}) :
    M.toMeasure = (volume : Measure I).map (fun u => project {i} (fun _ => u)) := by
  have hm : Measurable (fun u : I => project {i} (fun _ => u)) :=
    (measurable_project {i}).comp (by fun_prop)
  rw [← M.uniform i (Finset.mem_singleton_self i),
    Measure.map_map hm (measurable_pi_apply i)]
  calc
    M.toMeasure = M.toMeasure.map id := Measure.map_id.symm
    _ = _ := Measure.map_congr (by
      filter_upwards [M.supported] with x hx
      funext j
      have hj := congrFun hx j
      by_cases hji : j = i
      · simp [project, hji]
      · simpa [Function.comp_def, project, hji] using hj.symm)

instance (i : Fin d) : Subsingleton (Marginal {i}) where
  allEq L R := ext ((toMeasure_eq_uniform_singleton i L).trans
    (toMeasure_eq_uniform_singleton i R).symm)

end Marginal

/-- Reinsert one conditioned coordinate into a padded conditioning vector. -/
def insertCoordinate (s : Finset (Fin d)) (a : Fin d) (p : (Fin d → I) × I)
    (i : Fin d) : I := if i = a then p.2 else project s p.1 i

theorem measurable_insertCoordinate (s : Finset (Fin d)) (a : Fin d) :
    Measurable (insertCoordinate s a) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i = a
  · simp only [insertCoordinate, hi, ite_true]
    fun_prop
  · simp only [insertCoordinate, hi, ite_false]
    exact (measurable_pi_apply i).comp ((measurable_project s).comp measurable_fst)

/-- The conditional distribution of a coordinate given a retained subset. -/
noncomputable def coordinateKernel {t : Finset (Fin d)} (M : Marginal t)
    (s : Finset (Fin d)) (a : Fin d) : Kernel (Fin d → I) I :=
  condDistrib (fun x => x a) (project s) M.toMeasure

instance {t : Finset (Fin d)} (M : Marginal t) (s : Finset (Fin d)) (a : Fin d) :
    IsMarkovKernel (coordinateKernel M s a) :=
  inferInstanceAs (IsMarkovKernel (condDistrib _ _ M.toMeasure))

/-- Conditioning on the empty coordinate set leaves an active coordinate uniform. -/
theorem coordinateKernel_empty {t : Finset (Fin d)} (M : Marginal t)
    (a : Fin d) (ha : a ∈ t) : coordinateKernel M ∅ a (fun _ => 0) = volume := by
  have h := condDistrib_comp_map (μ := M.toMeasure)
    (measurable_project (∅ : Finset (Fin d))).aemeasurable
    (measurable_pi_apply a).aemeasurable
  have hu : M.toMeasure.map (fun x => x a) = volume := M.uniform a ha
  rw [M.map_empty, hu] at h
  change (coordinateKernel M ∅ a ∘ₘ Measure.dirac (fun _ => (0 : I))) = volume at h
  rw [Measure.dirac_bind (coordinateKernel M ∅ a).measurable] at h
  exact h

@[simp] theorem unitQuantile_volume (u : I) : unitQuantile (volume : Measure I) u = u := by
  apply le_antisymm
  · apply (unitQuantile_le_iff _ _ _).2
    simp [Measure.real, unitInterval.volume_Iic, ENNReal.toReal_ofReal u.property.1]
  · have h := (unitQuantile_le_iff (volume : Measure I) u (unitQuantile volume u)).1 le_rfl
    simpa [Measure.real, unitInterval.volume_Iic,
      ENNReal.toReal_ofReal (unitQuantile volume u).property.1] using h

/-- Disintegrating and reinserting a coordinate recovers its entire marginal law. -/
theorem map_insertCoordinate_disintegration {t s : Finset (Fin d)} (M : Marginal t)
    (a : Fin d) (ht : t = insert a s) :
    ((M.toMeasure.map (project s)) ⊗ₘ coordinateKernel M s a).map
      (insertCoordinate s a) = M.toMeasure := by
  rw [coordinateKernel, compProd_map_condDistrib (measurable_project s).aemeasurable
    (measurable_pi_apply a).aemeasurable,
    Measure.map_map (measurable_insertCoordinate s a)
      ((measurable_project s).prodMk (measurable_pi_apply a))]
  have he : (insertCoordinate s a ∘ (fun x => (project s x, x a))) =ᵐ[M.toMeasure] id := by
    filter_upwards [M.supported] with x hx
    funext i
    have hi := congrFun hx i
    by_cases hia : i = a
    · simp [insertCoordinate, hia]
    · simp only [comp_def, insertCoordinate, hia, ite_false, project_project le_rfl]
      simpa [project, ht, hia] using hi
  rw [Measure.map_congr he, Measure.map_id]

end ProbabilityTheory.Copula.Vine
