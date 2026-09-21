/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.FiniteMoments
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open MeasureTheory
open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def finiteWeight (μ : Measure Ω) (f : Ω → ι) (i : ι) : ℝ :=
  μ.real (f ⁻¹' {i})

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem finiteWeight_nonneg (μ : Measure Ω) (f : Ω → ι) (i : ι) :
    0 ≤ finiteWeight μ f i := ENNReal.toReal_nonneg

theorem finiteWeight_sum (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ι}
    (hf : Measurable f) : ∑ i, finiteWeight μ f i = 1 := by
  simpa [finiteWeight] using
    (sum_measureReal_preimage_singleton (μ := μ) Finset.univ
      (fun i _ => hf (measurableSet_singleton i)))

theorem integral_finite_map (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ι}
    (hf : Measurable f) (g : ι → ℝ) :
    (∫ x, g (f x) ∂μ) = ∑ i, finiteWeight μ f i * g i := by
  rw [← integral_map hf.aemeasurable (measurable_of_finite g).aestronglyMeasurable,
    integral_fintype (Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_eq_mul, map_measureReal_apply hf (measurableSet_singleton i)]
  rfl

theorem integral_finite_pair (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ι}
    (hf : Measurable f) (g : ι → ι → ℝ) :
    (∫ x, ∫ y, g (f x) (f y) ∂μ ∂μ) = weighted2 (finiteWeight μ f) g := by
  simp_rw [integral_finite_map μ hf]
  rw [integral_finite_map μ hf (fun i => ∑ j, finiteWeight μ f j * g i j)]
  simp only [weighted2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end ProbabilityTheory.Copula.RankRegion.RhoTau
