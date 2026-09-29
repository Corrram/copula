/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.XiRho.Support.XiReflection
import Copula.Rank.Region.XiRho.Support.AETotalPositivity
import Copula.Rank.Region.Common.StochasticRigidity

/-! # Stochastic monotonicity and maximal Chatterjee xi (re-export)

Compatibility module. The development lives in
`Copula.Rank.Region.Common.StochasticRigidity`, namespace
`ProbabilityTheory.Copula.RankRegion.Common`. The `export` below makes its public
declarations available under
`ProbabilityTheory.Copula.RankRegion.XiRho.Support`
as the very same constants.
-/

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

export ProbabilityTheory.Copula.RankRegion.Common (conditionalCDF_binary_of_xi_one
  cdfSection_concave_of_isSI cdfSection_differentiable_ae cdf_eq_min_of_isSI_binary
  isSI_xi_eq_one_iff isSD_xi_eq_one_iff)

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
