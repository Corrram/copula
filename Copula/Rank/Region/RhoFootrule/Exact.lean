/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoFootrule.Lower
import Copula.Rank.Region.RhoFootrule.UpperCoverage

/-! # The exact rho–footrule region

The lower boundary is explicit in `lowerBoundary`. The upper boundary is the
countable collection of polynomial arcs `UpperParameter.footrule` and
`UpperParameter.rho`. Both descriptions use only real arithmetic, an integer
parameter, and the stated nonnegativity/normalization constraints.

Necessity uses global transport duality inequalities. Sufficiency uses the
constructed boundary copulas and interpolation at fixed footrule.
-/

namespace ProbabilityTheory.Copula.RankRegion.RhoFootrule

/-- Exact membership, with the upper boundary given parametrically. -/
theorem exists_copula_iff (p r : ℝ) :
    (∃ C : Copula 2, C.spearmanFootrule = p ∧ C.spearmanRho = r) ↔
      p ∈ Set.Icc (-1 / 2) 1 ∧ lowerBoundary p ≤ r ∧
        ∃ a : UpperParameter, a.footrule = p ∧ r ≤ a.rho := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    refine ⟨C.spearmanFootrule_mem_Icc, lower_bound C, ?_⟩
    obtain ⟨a, ha⟩ := upperParameter_exists C.spearmanFootrule_mem_Icc
    exact ⟨a, ha, a.maximizes C ha.symm⟩
  · rintro ⟨hp, hl, a, ha, hu⟩
    obtain ⟨L, hLp, hLr⟩ := lowerBoundary_attained hp
    exact fixed_footrule_intermediate L a.copula hLp ((a.coefficients).1.trans ha)
      (hLr ▸ hl) ((a.coefficients).2.symm ▸ hu)

/-- Every upper-boundary fibre has a unique value, even at arc junctions. -/
theorem upperParameter_rho_unique (a b : UpperParameter) (h : a.footrule = b.footrule) :
    a.rho = b.rho := by
  apply le_antisymm
  · have hh := b.maximizes a.copula ((a.coefficients).1.trans h)
    rwa [(a.coefficients).2] at hh
  · have hh := a.maximizes b.copula ((b.coefficients).1.trans h.symm)
    rwa [(b.coefficients).2] at hh

end ProbabilityTheory.Copula.RankRegion.RhoFootrule
