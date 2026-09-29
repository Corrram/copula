/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.XiBlest.Support.StochasticBounds
import Copula.Rank.Region.Common.StochasticRho

/-! # Spearman rho dominates xi under stochastic monotonicity (re-export)

Compatibility module. The development lives in
`Copula.Rank.Region.Common.StochasticRho`, namespace
`ProbabilityTheory.Copula.RankRegion.Common`. The `export` below makes its public
declarations available under
`ProbabilityTheory.Copula.RankRegion.XiBlest.Support`
as the very same constants.
-/

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

export ProbabilityTheory.Copula.RankRegion.Common (integral_lower_integral integrable_lower_integral
  integral_abs_sub_of_antitone integral_sq_le_twice_lower_integral conditionalCDF_sq_le_cdf_integral
  spearmanRho_eq_iterated_cdf xi_le_rho_of_isSI xi_le_neg_rho_of_isSD
  xi_le_abs_rho_of_stochastically_monotone)

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
