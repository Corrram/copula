/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.XiRho.Support.Mixture
import Copula.Rank.Region.Common.XiAffineRegion

/-! # Convexity of xi regions with an affine second coefficient (re-export)

Compatibility module. The development lives in
`Copula.Rank.Region.Common.XiAffineRegion`, namespace
`ProbabilityTheory.Copula.RankRegion.Common`. The `export` below makes its public
declarations available under
`ProbabilityTheory.Copula.RankRegion.XiRho.Support`
as the very same constants.
-/

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

export ProbabilityTheory.Copula.RankRegion.Common (xiCoefficientRegion
  xi_intermediate_at_coefficient xi_upward_at_coefficient convex_xiCoefficientRegion)

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
