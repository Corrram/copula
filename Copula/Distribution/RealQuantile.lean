/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Distribution.ProbabilityIntegralTransform

/-! # The left-continuous quantile of a real law

For a probability measure `ν` on `ℝ` with distribution function `F`, the generalized inverse
`realQuantile ν t = inf {y | t ≤ F y}` is monotone on the open unit interval. If `F` is
continuous, then `realQuantile ν (F y) = y` for `ν`-almost every `y`: the exceptional points lie in
countably many level sets of `F` (one for each rational number, and the zero level), each of which
is null because `F` pushes `ν` forward to the uniform law.

This is the device used for the converse of Nelsen, *An Introduction to Copulas*, second edition,
Theorem 2.5.4 (`Copula.RandomVariable.Monotone`).
-/

open MeasureTheory Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory

variable (ν : Measure ℝ)

/-- The left-continuous generalized inverse `t ↦ inf {y | t ≤ F y}` of the CDF `F` of `ν`.
Outside `(0, 1)` the value is Lean's junk value of `sInf`. -/
noncomputable def realQuantile (t : ℝ) : ℝ :=
  sInf {y | t ≤ cdf ν y}

theorem bddBelow_setOf_le_cdf {t : ℝ} (ht : 0 < t) : BddBelow {y | t ≤ cdf ν y} := by
  obtain ⟨z, hz⟩ := ((tendsto_cdf_atBot ν).eventually_lt_const ht).exists
  refine ⟨z, fun y hy => ?_⟩
  by_contra! hyz
  have := monotone_cdf ν hyz.le
  change t ≤ cdf ν y at hy
  linarith

theorem nonempty_setOf_le_cdf {t : ℝ} (ht : t < 1) : {y | t ≤ cdf ν y}.Nonempty :=
  ((tendsto_cdf_atTop ν).eventually_const_le ht).exists

/-- The quantile is monotone on the open unit interval. -/
theorem monotoneOn_realQuantile : MonotoneOn (realQuantile ν) (Ioo 0 1) := by
  intro t ht u hu htu
  exact csInf_le_csInf (bddBelow_setOf_le_cdf ν ht.1) (nonempty_setOf_le_cdf ν hu.2)
    (fun y hy => le_trans htu hy)

/-- The quantile never exceeds the point at which the CDF is evaluated. -/
theorem realQuantile_cdf_le {y : ℝ} (hy : 0 < cdf ν y) : realQuantile ν (cdf ν y) ≤ y :=
  csInf_le (bddBelow_setOf_le_cdf ν hy) (show cdf ν y ≤ cdf ν y from le_rfl)

/-- The quantile inverts the CDF at every point that is not on the level of a rational point. -/
theorem realQuantile_cdf_eq {y : ℝ} (hy : 0 < cdf ν y) (hq : ∀ q : ℚ, cdf ν q ≠ cdf ν y) :
    realQuantile ν (cdf ν y) = y := by
  apply le_antisymm (realQuantile_cdf_le ν hy)
  by_contra! hlt
  obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt ⟨y, show cdf ν y ≤ cdf ν y from le_rfl⟩ hlt
  obtain ⟨q, hzq, hqy⟩ := exists_rat_btwn hzy
  have h1 := monotone_cdf ν hzq.le
  have h2 := monotone_cdf ν hqy.le
  change cdf ν y ≤ cdf ν z at hz
  exact hq q (le_antisymm h2 (hz.trans h1))

/-- For a continuous CDF `F`, the quantile recovers `y` from `F y` almost surely. -/
theorem ae_realQuantile_cdf [IsProbabilityMeasure ν] (hc : Continuous (cdf ν)) :
    ∀ᵐ y ∂ν, realQuantile ν (cdf ν y) = y := by
  let A : Set I := insert 0 (range fun q : ℚ => cdfUnit ν q)
  have hA : A.Countable := (countable_range _).insert 0
  have hnull : ν (cdfUnit ν ⁻¹' A) = 0 := by
    rw [← Measure.map_apply (measurable_cdfUnit ν) hA.measurableSet, map_cdfUnit ν hc]
    exact hA.measure_zero volume
  refine measure_mono_null (fun y hy => ?_) hnull
  change ¬ realQuantile ν (cdf ν y) = y at hy
  change cdfUnit ν y ∈ A
  by_contra hyA
  apply hy
  have h0 : cdfUnit ν y ≠ 0 := fun h => hyA (Or.inl h)
  refine realQuantile_cdf_eq ν (lt_of_le_of_ne (cdf_nonneg ν y)
    (fun h => h0 (Subtype.ext h.symm))) (fun q hq => hyA (Or.inr ⟨q, Subtype.ext hq⟩))

/-- For a continuous CDF `F`, almost surely `0 < F y < 1`. -/
theorem ae_cdf_mem_Ioo [IsProbabilityMeasure ν] (hc : Continuous (cdf ν)) :
    ∀ᵐ y ∂ν, cdf ν y ∈ Ioo 0 1 := by
  let A : Set I := {0, 1}
  have hA : A.Countable := (countable_singleton 1).insert 0
  have hnull : ν (cdfUnit ν ⁻¹' A) = 0 := by
    rw [← Measure.map_apply (measurable_cdfUnit ν) hA.measurableSet, map_cdfUnit ν hc]
    exact hA.measure_zero volume
  refine measure_mono_null (fun y hy => ?_) hnull
  change ¬ (0 < cdf ν y ∧ cdf ν y < 1) at hy
  change cdfUnit ν y = 0 ∨ cdfUnit ν y = 1
  rcases le_or_gt (cdf ν y) 0 with h0 | h0
  · exact Or.inl (Subtype.ext (le_antisymm h0 (cdf_nonneg ν y)))
  · exact Or.inr (Subtype.ext (le_antisymm (cdf_le_one ν y) (not_lt.mp fun h1 => hy ⟨h0, h1⟩)))

end ProbabilityTheory
