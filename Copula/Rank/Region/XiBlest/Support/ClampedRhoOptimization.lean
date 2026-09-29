/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.XiBlest.Support.StochasticRho
import Copula.Rank.Region.Common.ClampedRhoOptimization

/-! # A sharp quadratic certificate for clamped conditional distributions (re-export)

Compatibility module. The development lives in
`Copula.Rank.Region.Common.ClampedRhoOptimization`, namespace
`ProbabilityTheory.Copula.RankRegion.Common`. The `export` below makes its public
declarations available under
`ProbabilityTheory.Copula.RankRegion.XiBlest.Support`
as the very same constants.
-/

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

export ProbabilityTheory.Copula.RankRegion.Common (unitClamp unitClamp_mem unitClamp_projection
  clamped_quadratic_certificate integrable_rho_section integrable_rho_profile
  rho_conditional_formula clamped_rho_distance_bound clamped_rho_support clamped_rho_support_eq_iff)

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
