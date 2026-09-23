import Copula.Rank.Region.RhoFootrule.Exact
import Copula.Rank.Region.MeanVariance.Paper.Moments

/-! # The full sharp rho-footrule region

The package supplies arithmetic boundary parameters, actual attaining copulas,
and global inequalities. The coefficient order here matches the article.
Uniqueness of the optimizing copula is proved in `OptimizerUniqueness.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.MeanVariance

open Copula.RankRegion

abbrev BoundaryParameter := RhoFootrule.UpperParameter

/-- The upper boundary as a scalar function on its valid interval. -/
noncomputable def upperRho (p : ℝ) : ℝ :=
  if h : p ∈ Set.Icc (-1 / 2) 1 then (RhoFootrule.upperParameter_exists h).choose.rho else 0

/-- The scalar boundary agrees with every explicit arithmetic arc. -/
theorem upperRho_parameter (a : BoundaryParameter) : upperRho a.footrule = a.rho := by
  have hp : a.footrule ∈ Set.Icc (-1 / 2) 1 :=
    a.coefficients.1 ▸ a.copula.spearmanFootrule_mem_Icc
  rw [upperRho, dite_eq_left hp]
  exact RhoFootrule.upperParameter_rho_unique _ a (RhoFootrule.upperParameter_exists hp).choose_spec

/-- Both coefficient identities of the constructed boundary copula. -/
theorem boundary_coefficients (a : BoundaryParameter) :
    a.copula.spearmanFootrule = a.footrule ∧ a.copula.spearmanRho = a.rho := a.coefficients

/-- Global sharp upper bound, valid for singular copulas too. -/
theorem sharp_upper_bound (C : Copula 2) : C.spearmanRho ≤ upperRho C.spearmanFootrule := by
  obtain ⟨a, ha⟩ := RhoFootrule.upperParameter_exists C.spearmanFootrule_mem_Icc
  rw [← ha, upperRho_parameter]
  exact a.maximizes C ha.symm

/-- Every upper-boundary point is attained. -/
theorem upper_boundary_attained {p : ℝ} (hp : p ∈ Set.Icc (-1 / 2) 1) :
    ∃ C : Copula 2, C.spearmanFootrule = p ∧ C.spearmanRho = upperRho p := by
  obtain ⟨a, ha⟩ := RhoFootrule.upperParameter_exists hp
  exact ⟨a.copula, a.coefficients.1.trans ha,
    a.coefficients.2.trans (ha ▸ upperRho_parameter a).symm⟩

/-- The known lower boundary, with its exact square-root normalization. -/
theorem sharp_lower_bound (C : Copula 2) :
    -1 + 2 * (Real.sqrt ((1 + 2 * C.spearmanFootrule) / 3)) ^ 3 ≤ C.spearmanRho :=
  RhoFootrule.lower_bound C

theorem lower_boundary_attained {p : ℝ} (hp : p ∈ Set.Icc (-1 / 2) 1) :
    ∃ C : Copula 2, C.spearmanFootrule = p ∧
      C.spearmanRho = -1 + 2 * (Real.sqrt ((1 + 2 * p) / 3)) ^ 3 :=
  RhoFootrule.lowerBoundary_attained hp

/-- Corollary 1.2: both directions, in the source's (rho, footrule) order. -/
theorem exact_region (r p : ℝ) :
    (∃ C : Copula 2, C.spearmanRho = r ∧ C.spearmanFootrule = p) ↔
      p ∈ Set.Icc (-1 / 2) 1 ∧ RhoFootrule.lowerBoundary p ≤ r ∧ r ≤ upperRho p := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    exact ⟨C.spearmanFootrule_mem_Icc, RhoFootrule.lower_bound C, sharp_upper_bound C⟩
  · rintro ⟨hp, hl, hu⟩
    obtain ⟨a, ha⟩ := RhoFootrule.upperParameter_exists hp
    obtain ⟨C, hC, hr⟩ := (RhoFootrule.exists_copula_iff p r).mpr
      ⟨hp, hl, a, ha, by simpa only [← ha, upperRho_parameter] using hu⟩
    exact ⟨C, hr, hC⟩

/-- Arc junctions yield the same boundary value. -/
theorem boundary_value_unique (a b : BoundaryParameter) (h : a.footrule = b.footrule) :
    a.rho = b.rho := RhoFootrule.upperParameter_rho_unique a b h

end ProbabilityTheory.Copula.RankRegion.MeanVariance
