/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Vine.Marginal

/-! # Conditional pair-copula gluing

Glue the laws of `(a, S)` and `(b, S)` over their common `S` marginal using
a measurable family of pair copulas. Both input laws are preserved, without
assuming densities or continuous conditional distributions.
-/

open MeasureTheory Set Function
open scoped unitInterval

namespace ProbabilityTheory.Copula.Vine

variable {d : ℕ} {s l r : Finset (Fin d)}

private theorem measurable_fst_eval (i : Fin 2) :
    Measurable (fun p : (Fin d → I) × (Fin 2 → I) => (p.1, p.2 i)) :=
  measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)

/-- The compatibility conditions for two marginals sharing a conditioning set. -/
structure Overlap (L : Marginal l) (R : Marginal r) (D : Marginal s)
    (a b : Fin d) : Prop where
  left_set : l = insert a s
  right_set : r = insert b s
  left_notMem : a ∉ s
  right_notMem : b ∉ s
  distinct : a ≠ b
  left_map : L.toMeasure.map (project s) = D.toMeasure
  right_map : R.toMeasure.map (project s) = D.toMeasure

/-- Insert the two conditional quantiles into their shared conditioning vector. -/
noncomputable def glueMap (L : Marginal l) (R : Marginal r) (s : Finset (Fin d))
    (a b : Fin d) (p : (Fin d → I) × (Fin 2 → I)) (i : Fin d) : I :=
  if i = a then unitQuantile (coordinateKernel L s a p.1) (p.2 0)
  else if i = b then unitQuantile (coordinateKernel R s b p.1) (p.2 1)
  else project s p.1 i

set_option maxHeartbeats 1000000 in
theorem measurable_glueMap (L : Marginal l) (R : Marginal r) (s : Finset (Fin d))
    (a b : Fin d) : Measurable (glueMap L R s a b) := by
  have hL : Measurable (fun p : (Fin d → I) × (Fin 2 → I) =>
      unitQuantile (coordinateKernel L s a p.1) (p.2 0)) :=
    (measurable_kernelQuantile (coordinateKernel L s a)).comp (measurable_fst_eval 0)
  have hR : Measurable (fun p : (Fin d → I) × (Fin 2 → I) =>
      unitQuantile (coordinateKernel R s b p.1) (p.2 1)) :=
    (measurable_kernelQuantile (coordinateKernel R s b)).comp (measurable_fst_eval 1)
  apply Measurable.of_eval
  intro i
  by_cases ha : i = a
  · simp only [glueMap, ha, ite_true]
    exact hL
  · by_cases hb : i = b
    · simp only [glueMap, ha, ite_false]
      simp only [hb, ite_true]
      exact hR
    · simp only [glueMap, ha, hb, ite_false]
      exact (measurable_pi_apply i).comp ((measurable_project s).comp measurable_fst)

/-- The probability law obtained by conditional pair-copula gluing. -/
noncomputable def glueProbability (L : Marginal l) (R : Marginal r) (D : Marginal s)
    (a b : Fin d) (F : Family (Fin d → I) 2) : ProbabilityMeasure (Fin d → I) :=
  ⟨(D.toMeasure ⊗ₘ (F.comap (project s) (measurable_project s)).kernel).map
    (glueMap L R s a b), inferInstance⟩

theorem toMeasure_glueProbability (L : Marginal l) (R : Marginal r) (D : Marginal s)
    (a b : Fin d) (F : Family (Fin d → I) 2) :
    (glueProbability L R D a b F).toMeasure =
      (D.toMeasure ⊗ₘ (F.comap (project s) (measurable_project s)).kernel).map
        (glueMap L R s a b) := rfl

/-- Event probabilities for a non-simplified pair-copula join. The pair family
is evaluated at the actual shared coordinates, not averaged in advance. -/
theorem glueProbability_apply (L : Marginal l) (R : Marginal r) (D : Marginal s)
    (a b : Fin d) (F : Family (Fin d → I) 2) {A : Set (Fin d → I)}
    (hA : MeasurableSet A) :
    (glueProbability L R D a b F).toMeasure A =
      ∫⁻ x, F.kernel (project s x) {z | glueMap L R s a b (x, z) ∈ A} ∂D.toMeasure := by
  rw [toMeasure_glueProbability, Measure.map_apply (measurable_glueMap L R s a b) hA,
    Measure.compProd_apply ((measurable_glueMap L R s a b) hA)]
  rfl

private theorem measurable_insertPair (a b : Fin d) :
    Measurable (fun (z : Fin 2 → I) (i : Fin d) =>
      if i = a then z 0 else if i = b then z 1 else 0) := by
  apply Measurable.of_eval
  intro i
  by_cases hia : i = a
  · simp only [hia, ite_true]
    exact measurable_pi_apply 0
  · by_cases hib : i = b
    · simp only [hia, ite_false]
      simp only [hib, ite_true]
      exact measurable_pi_apply 1
    · simp only [hia, hib, ite_false]
      exact measurable_const

/-- With no conditioning coordinates, gluing inserts the supplied pair law
directly into the two active coordinates. -/
theorem glueProbability_empty (L : Marginal l) (R : Marginal r) (a b : Fin d)
    (ha : a ∈ l) (hb : b ∈ r) (F : Family (Fin d → I) 2) :
    (glueProbability L R Marginal.empty a b F).toMeasure =
      (F.copula (fun _ => 0)).toMeasure.map
        (fun z i => if i = a then z 0 else if i = b then z 1 else 0) := by
  ext A hA
  rw [glueProbability_apply _ _ _ _ _ _ hA, Measure.map_apply (measurable_insertPair a b) hA]
  change (∫⁻ x, F.kernel (project ∅ x) {z | glueMap L R ∅ a b (x, z) ∈ A}
      ∂Measure.dirac (fun _ => 0)) = _
  rw [lintegral_dirac]
  congr 1
  ext z
  have he : glueMap L R ∅ a b ((fun _ => 0), z) =
      (fun i => if i = a then z 0 else if i = b then z 1 else 0) := by
    funext i
    simp [glueMap, coordinateKernel_empty L a ha, coordinateKernel_empty R b hb, project]
  exact Iff.of_eq (congrArg (fun x => x ∈ A) he)

/-- Projecting an unconditional join onto its ordered endpoints recovers the
input pair copula, including singular copulas. -/
theorem map_glueProbability_empty_pair (L : Marginal l) (R : Marginal r)
    (a b : Fin d) (ha : a ∈ l) (hb : b ∈ r) (hab : a ≠ b)
    (F : Family (Fin d → I) 2) :
    (glueProbability L R Marginal.empty a b F).toMeasure.map (fun x => ![x a, x b]) =
      (F.copula (fun _ => 0)).toMeasure := by
  rw [glueProbability_empty L R a b ha hb F,
    Measure.map_map (by fun_prop) (measurable_insertPair a b)]
  have he : (fun x : Fin d → I => ![x a, x b]) ∘
      (fun (z : Fin 2 → I) i => if i = a then z 0 else if i = b then z 1 else 0) = id := by
    funext z i
    fin_cases i <;> simp [hab.symm]
  rw [he, Measure.map_id]

theorem map_glue_left (L : Marginal l) (R : Marginal r) (D : Marginal s)
    (a b : Fin d) (F : Family (Fin d → I) 2) (h : Overlap L R D a b) :
    (glueProbability L R D a b F).toMeasure.map (project l) = L.toMeasure := by
  have he : project l ∘ glueMap L R s a b = insertCoordinate s a ∘
      (fun p => (p.1, unitQuantile (coordinateKernel L s a p.1) (p.2 0))) := by
    funext p i
    by_cases ha : i = a
    · simp [project, glueMap, insertCoordinate, ha, h.left_set]
    · by_cases hb : i = b
      · simp [project, insertCoordinate, hb, h.left_set,
          h.distinct.symm, h.right_notMem]
      · by_cases hs : i ∈ s <;> simp [project, glueMap, insertCoordinate, ha, hb, hs, h.left_set]
  have hq : Measurable (fun p : (Fin d → I) × (Fin 2 → I) =>
      (p.1, unitQuantile (coordinateKernel L s a p.1) (p.2 0))) :=
    measurable_fst.prodMk ((measurable_kernelQuantile (coordinateKernel L s a)).comp
      (measurable_fst_eval 0))
  rw [toMeasure_glueProbability,
    Measure.map_map (measurable_project l) (measurable_glueMap L R s a b), he,
    ← Measure.map_map (measurable_insertCoordinate s a) hq,
    map_family_quantile, ← h.left_map, map_insertCoordinate_disintegration L a h.left_set]

theorem map_glue_right (L : Marginal l) (R : Marginal r) (D : Marginal s)
    (a b : Fin d) (F : Family (Fin d → I) 2) (h : Overlap L R D a b) :
    (glueProbability L R D a b F).toMeasure.map (project r) = R.toMeasure := by
  have he : project r ∘ glueMap L R s a b = insertCoordinate s b ∘
      (fun p => (p.1, unitQuantile (coordinateKernel R s b p.1) (p.2 1))) := by
    funext p i
    by_cases ha : i = a
    · simp [project, insertCoordinate, ha, h.right_set,
        h.distinct, h.left_notMem]
    · by_cases hb : i = b
      · simp [project, glueMap, insertCoordinate, hb, h.right_set, h.distinct.symm]
      · by_cases hs : i ∈ s <;> simp [project, glueMap, insertCoordinate, ha, hb, hs, h.right_set]
  have hq : Measurable (fun p : (Fin d → I) × (Fin 2 → I) =>
      (p.1, unitQuantile (coordinateKernel R s b p.1) (p.2 1))) :=
    measurable_fst.prodMk ((measurable_kernelQuantile (coordinateKernel R s b)).comp
      (measurable_fst_eval 1))
  rw [toMeasure_glueProbability,
    Measure.map_map (measurable_project r) (measurable_glueMap L R s a b), he,
    ← Measure.map_map (measurable_insertCoordinate s b) hq,
    map_family_quantile, ← h.right_map, map_insertCoordinate_disintegration R b h.right_set]

/-- Join compatible marginal copulas through a possibly non-simplified pair family. -/
noncomputable def glue (L : Marginal l) (R : Marginal r) (D : Marginal s)
    (a b : Fin d) (F : Family (Fin d → I) 2) (h : Overlap L R D a b) :
    Marginal (insert a (insert b s)) where
  measure := glueProbability L R D a b F
  uniform i hi := by
    by_cases hil : i ∈ l
    · have hm := congrArg (fun μ : Measure (Fin d → I) => μ.map (fun x => x i))
        (map_glue_left L R D a b F h)
      rw [Measure.map_map (measurable_pi_apply i) (measurable_project l)] at hm
      simpa only [comp_def, project, hil, ite_true] using hm.trans (L.uniform i hil)
    · have hir : i ∈ r := by
        rw [h.left_set] at hil
        rw [h.right_set]
        simp only [Finset.mem_insert] at hi hil ⊢
        tauto
      have hm := congrArg (fun μ : Measure (Fin d → I) => μ.map (fun x => x i))
        (map_glue_right L R D a b F h)
      rw [Measure.map_map (measurable_pi_apply i) (measurable_project r)] at hm
      simpa only [comp_def, project, hir, ite_true] using hm.trans (R.uniform i hir)
  supported := by
    rw [toMeasure_glueProbability]
    apply (ae_map_iff (measurable_glueMap L R s a b).aemeasurable
      (measurableSet_eq_fun (measurable_project _) measurable_id)).2
    apply Filter.Eventually.of_forall
    intro p
    funext i
    by_cases ha : i = a
    · simp [project, glueMap, ha]
    · by_cases hb : i = b
      · simp [project, glueMap, hb]
      · by_cases hs : i ∈ s <;> simp [project, glueMap, ha, hb, hs]

@[simp] theorem map_glue_project_left (L : Marginal l) (R : Marginal r) (D : Marginal s)
    (a b : Fin d) (F : Family (Fin d → I) 2) (h : Overlap L R D a b) :
    (glue L R D a b F h).toMeasure.map (project l) = L.toMeasure :=
  map_glue_left L R D a b F h

@[simp] theorem map_glue_project_right (L : Marginal l) (R : Marginal r) (D : Marginal s)
    (a b : Fin d) (F : Family (Fin d → I) 2) (h : Overlap L R D a b) :
    (glue L R D a b F h).toMeasure.map (project r) = R.toMeasure :=
  map_glue_right L R D a b F h

end ProbabilityTheory.Copula.Vine
