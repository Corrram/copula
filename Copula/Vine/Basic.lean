/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Vine.Quantile
import Copula.Transform
import Copula.Unique

/-!
# Simplified C-vine copulas

One construction step adjoins an independent uniform root to a residual copula,
then applies the conditional quantile of each root-pair copula to its residual
coordinate. Iterating this step gives a simplified C-vine in any finite dimension.
The recursive residual copula is fixed, independent of the value of the root.
-/

open MeasureTheory Set Function
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace Vine

/-- The inverse conditional transform for one level of a C-vine. -/
noncomputable def rootTransform {d : ℕ} (pairs : Fin d → Copula 2)
    (p : I × (Fin d → I)) : Fin (d + 1) → I :=
  Fin.cons p.1 (fun i => (pairs i).conditionalQuantile p.1 (p.2 i))

theorem measurable_rootTransform {d : ℕ} (pairs : Fin d → Copula 2) :
    Measurable (rootTransform pairs) := by
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_fst
  · exact (pairs j).measurable_conditionalQuantile.comp
      (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))

theorem map_root_coordinate {d : ℕ} (D : Copula d) (i : Fin d) :
    ((volume : Measure I).prod D.toMeasure).map (fun p => (p.1, p.2 i)) =
      (volume : Measure I).prod volume := by
  have h := Measure.map_prod_map (volume : Measure I) D.toMeasure
    measurable_id (measurable_pi_apply i)
  simpa only [Measure.map_id, D.map_eval, Prod.map_def, id_eq] using h.symm

end Vine

/-- Adjoin a root with the prescribed bivariate copulas to a residual copula.
The residual dependence is independent of the root (the simplifying assumption). -/
noncomputable def vineStep {d : ℕ} (pairs : Fin d → Copula 2) (D : Copula d) :
    Copula (d + 1) :=
  ofMap ⟨(volume : Measure I).prod D.toMeasure, inferInstance⟩
    (Vine.rootTransform pairs) (Vine.measurable_rootTransform pairs) (fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · change ((volume : Measure I).prod D.toMeasure).map Prod.fst = volume
        simp
      · change ((volume : Measure I).prod D.toMeasure).map
          (fun p => (pairs j).conditionalQuantile p.1 (p.2 j)) = volume
        have hp : Measurable (fun p : I × (Fin d → I) => (p.1, p.2 j)) := by fun_prop
        calc
          _ = (((volume : Measure I).prod D.toMeasure).map
              (fun p => (p.1, p.2 j))).map (uncurry (pairs j).conditionalQuantile) :=
            (Measure.map_map (pairs j).measurable_conditionalQuantile hp).symm
          _ = volume := by
            rw [Vine.map_root_coordinate, (pairs j).map_uncurry_conditionalQuantile])

@[simp]
theorem toMeasure_vineStep {d : ℕ} (pairs : Fin d → Copula 2) (D : Copula d) :
    (vineStep pairs D).toMeasure =
      ((volume : Measure I).prod D.toMeasure).map (Vine.rootTransform pairs) := rfl

/-- Each first-tree pair is exactly the bivariate copula supplied by the caller. -/
@[simp]
theorem reindex_vineStep_root_pair {d : ℕ} (pairs : Fin d → Copula 2)
    (D : Copula d) (i : Fin d) :
    (vineStep pairs D).reindex ![0, i.succ] = pairs i := by
  apply Copula.ext
  rw [toMeasure_reindex, toMeasure_vineStep,
    Measure.map_map (by fun_prop) (Vine.measurable_rootTransform pairs)]
  have he : ((fun x : Fin (d + 1) → I => fun j => x (![0, i.succ] j)) ∘
      Vine.rootTransform pairs) =
      (fun p => ![p.1, (pairs i).conditionalQuantile p.1 (p.2 i)]) := by
    funext p j
    fin_cases j <;> rfl
  rw [he]
  have hm : Measurable (fun p : I × I => ![p.1, (pairs i).conditionalQuantile p.1 p.2]) := by
    apply Measurable.of_eval
    intro j
    fin_cases j
    · exact measurable_fst
    · exact (pairs i).measurable_conditionalQuantile
  have hp : Measurable (fun p : I × (Fin d → I) => (p.1, p.2 i)) := by fun_prop
  calc
    _ = (((volume : Measure I).prod D.toMeasure).map (fun p => (p.1, p.2 i))).map
        (fun p => ![p.1, (pairs i).conditionalQuantile p.1 p.2]) :=
      (Measure.map_map hm hp).symm
    _ = (pairs i).toMeasure := by
      rw [Vine.map_root_coordinate, (pairs i).map_pair_conditionalQuantile]

/-- A simplified C-vine, with roots ordered `0, 1, …`.
At each level the pair copulas describe the remaining coordinates conditional
on all earlier roots. There are `d * (d - 1) / 2` bivariate inputs in dimension `d`. -/
inductive CVine : ℕ → Type where
  /-- The empty vine. -/
  | nil : CVine 0
  /-- Add the next root and its pair copulas. -/
  | cons {d : ℕ} (pairs : Fin d → Copula 2) (tail : CVine d) : CVine (d + 1)

namespace CVine

/-- The copula represented by a simplified C-vine. -/
noncomputable def toCopula : {d : ℕ} → CVine d → Copula d
  | _, .nil => independence 0
  | _, .cons pairs tail => vineStep pairs tail.toCopula

@[simp]
theorem toCopula_nil : CVine.nil.toCopula = independence 0 := rfl

@[simp]
theorem toCopula_cons {d : ℕ} (pairs : Fin d → Copula 2) (tail : CVine d) :
    (CVine.cons pairs tail).toCopula = vineStep pairs tail.toCopula := rfl

/-- A one-dimensional vine has no pair-copula inputs. -/
def singleton : CVine 1 := .cons Fin.elim0 .nil

@[simp]
theorem toCopula_singleton : singleton.toCopula = independence 1 := Subsingleton.elim _ _

/-- Construct a C-vine from its strict upper triangular table of pair copulas.
The entry `(i, j)` is the pair of coordinates `i` and `j` conditional on
coordinates `0, …, i - 1`. Entries below the diagonal are not required. -/
def ofPairs : (d : ℕ) → ((i j : Fin d) → i < j → Copula 2) → CVine d
  | 0, _ => .nil
  | d + 1, pairs => .cons (fun j => pairs 0 j.succ (Fin.succ_pos j))
      (ofPairs d (fun i j hij => pairs i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)))

/-- The first row of the triangular table gives the root's bivariate marginals. -/
@[simp]
theorem reindex_ofPairs_root_pair {d : ℕ}
    (pairs : (i j : Fin (d + 1)) → i < j → Copula 2) (j : Fin d) :
    (ofPairs (d + 1) pairs).toCopula.reindex ![0, j.succ] =
      pairs 0 j.succ (Fin.succ_pos j) := by
  exact reindex_vineStep_root_pair _ _ j

/-- A bivariate vine consists of its single pair copula. -/
def pair (C : Copula 2) : CVine 2 := .cons (fun _ => C) singleton

@[simp]
theorem toCopula_pair (C : Copula 2) : (pair C).toCopula = C := by
  have h := reindex_vineStep_root_pair (fun _ : Fin 1 => C) singleton.toCopula 0
  have hid : (![0, (0 : Fin 1).succ] : Fin 2 → Fin 2) = id := by decide
  simpa only [pair, toCopula_cons, hid, reindex_id] using h

/-- A three-variable vine with pairs `C₀₁`, `C₀₂` and conditional pair `C₁₂;₀`. -/
def triple (C₀₁ C₀₂ C₁₂₀ : Copula 2) : CVine 3 :=
  .cons ![C₀₁, C₀₂] (pair C₁₂₀)

@[simp]
theorem toCopula_triple (C₀₁ C₀₂ C₁₂₀ : Copula 2) :
    (triple C₀₁ C₀₂ C₁₂₀).toCopula = vineStep ![C₀₁, C₀₂] C₁₂₀ := by
  simp [triple]

end CVine

end ProbabilityTheory.Copula
