/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Integration
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.Order.ProjIcc

/-! # Finite mixtures of paths with uniform marginals

This constructor allows unequal segment lengths and zero weights. Marginal
identities are checked against continuous test functions, and the resulting
copula retains an explicit integration formula for its paths.
-/

open MeasureTheory
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.FinitePathCoupling

variable {ι : Type*} [Fintype ι]

noncomputable def measure (w : ι → ℝ) (X : ι → I → (Fin 2 → I)) : Measure (Fin 2 → I) :=
  ∑ i, Real.toNNReal (w i) • (volume : Measure I).map (X i)

instance (w : ι → ℝ) (X : ι → I → (Fin 2 → I)) : IsFiniteMeasure (measure w X) := by
  unfold measure
  infer_instance

theorem integral_measure (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (X : ι → I → (Fin 2 → I)) (hX : ∀ i, Continuous (X i))
    {f : (Fin 2 → I) → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂measure w X) = ∑ i, w i * ∫ u : I, f (X i u) := by
  unfold measure
  rw [integral_finsetSum_measure (fun _ _ => integrable_continuous_cube _ hf)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_nnreal_measure, integral_map (hX i).measurable.aemeasurable hf.aestronglyMeasurable]
  change ((Real.toNNReal (w i) : ℝ) * _) = _
  rw [Real.coe_toNNReal _ (hw i)]

theorem map_eval_eq (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (X : ι → I → (Fin 2 → I)) (hX : ∀ i, Continuous (X i))
    (hmarg : ∀ (j : Fin 2) (f : I → ℝ), Continuous f →
      (∑ i, w i * ∫ u : I, f (X i u j)) = ∫ u : I, f u) (j : Fin 2) :
    (measure w X).map (fun x => x j) = volume := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map (measurable_pi_apply j).aemeasurable f.continuous.aestronglyMeasurable,
    integral_measure w hw X hX (by fun_prop)]
  exact hmarg j f f.continuous

noncomputable def copula (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (X : ι → I → (Fin 2 → I)) (hX : ∀ i, Continuous (X i))
    (hmarg : ∀ (j : Fin 2) (f : I → ℝ), Continuous f →
      (∑ i, w i * ∫ u : I, f (X i u j)) = ∫ u : I, f u) : Copula 2 where
  measure := ⟨measure w X, by
    apply isProbabilityMeasure_iff.mpr
    have h := congrArg (fun μ : Measure I => μ Set.univ) (map_eval_eq w hw X hX hmarg 0)
    simpa only [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ,
      Set.preimage_univ, measure_univ] using h⟩
  marginal_eq := map_eval_eq w hw X hX hmarg

theorem integral_copula (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (X : ι → I → (Fin 2 → I)) (hX : ∀ i, Continuous (X i))
    (hmarg : ∀ (j : Fin 2) (f : I → ℝ), Continuous f →
      (∑ i, w i * ∫ u : I, f (X i u j)) = ∫ u : I, f u)
    {f : (Fin 2 → I) → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂(copula w hw X hX hmarg).toMeasure) = ∑ i, w i * ∫ u : I, f (X i u) :=
  integral_measure w hw X hX hf

/-- Extend a continuous test function from the unit interval by constant tails. -/
noncomputable def extend (f : I → ℝ) (x : ℝ) : ℝ := f (Set.projIcc 0 1 zero_le_one x)

@[fun_prop] theorem continuous_extend {f : I → ℝ} (hf : Continuous f) :
    Continuous (extend f) := hf.comp continuous_projIcc

@[simp] theorem extend_coe (f : I → ℝ) (u : I) : extend f u = f u := by
  unfold extend
  rw [Set.projIcc_val]

/-- Weighted integration of an affine path, including zero-length paths. -/
theorem integral_affine (f : ℝ → ℝ) (a b : ℝ) :
    (b - a) * (∫ u : I, f (a + (b - a) * u)) = ∫ u in a..b, f u := by
  rw [integral_unitInterval (fun u : ℝ => f (a + (b - a) * u))]
  have h := intervalIntegral.smul_integral_comp_add_mul f (b - a) a (a := 0) (b := 1)
  simpa only [smul_eq_mul, mul_zero, mul_one, add_zero, add_sub_cancel] using h

end ProbabilityTheory.Copula.RankRegion.FinitePathCoupling
