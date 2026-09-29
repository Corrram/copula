/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.XiRho.Support.ClampedRhoOptimization
import Copula.Rank.Region.XiRho.Support.ConditionalCopula
import Copula.Rank.Region.Common.DiagonalBand

/-! # Diagonal-band copulas at every nonnegative slope (re-export)

Compatibility module. The development lives in
`Copula.Rank.Region.Common.DiagonalBand`, namespace
`ProbabilityTheory.Copula.RankRegion.Common`. The `export` below makes its public
declarations available under
`ProbabilityTheory.Copula.RankRegion.XiRho.Support`
as the very same constants.
-/

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

export ProbabilityTheory.Copula.RankRegion.Common (clampedMean continuous_clampedMean
  clampedMean_monotone clampedMean_zero clampedMean_top exists_clamped_intercept bandIntercept
  bandIntercept_mean bandIntercept_monotone bandKernel bandKernel_integrable bandKernel_monotone
  bandKernel_zero bandKernel_one diagonalBand diagonalBand_cdf diagonalBand_conditionalCDF
  diagonalBand_isSI diagonalBand_support diagonalBand_support_eq_iff diagonalBand_maximal_rho
  diagonalBand_maximal_rho_eq_iff)

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
