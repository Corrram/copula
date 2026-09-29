/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.XiRho.Support.StochasticRigidity
import Copula.Rank.Region.Common.StochasticBounds

/-! # Conditional moment bounds for stochastically increasing copulas (re-export)

Compatibility module. The development lives in
`Copula.Rank.Region.Common.StochasticBounds`, namespace
`ProbabilityTheory.Copula.RankRegion.Common`. The `export` below makes its public
declarations available under
`ProbabilityTheory.Copula.RankRegion.XiRho.Support`
as the very same constants.
-/

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

export ProbabilityTheory.Copula.RankRegion.Common (exists_antitone_version
  conditionalCDF_antitone_version integrable_unit_bounded integral_sq_le_lower_at_mean
  conditionalCDF_sq_le_diagonal xi_le_footrule_of_isSI)

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
