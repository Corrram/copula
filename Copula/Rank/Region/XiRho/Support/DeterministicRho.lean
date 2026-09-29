/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.XiRho.Support.CenteredProperties
import Copula.Rank.Region.XiRho.Support.Mixture
import Copula.Rank.Region.Common.DeterministicRho

/-! # Every rho is attained at xi=1 by a radially symmetric copula (re-export)

Compatibility module. The development lives in
`Copula.Rank.Region.Common.DeterministicRho`, namespace
`ProbabilityTheory.Copula.RankRegion.Common`. The `export` below makes its public
declarations available under
`ProbabilityTheory.Copula.RankRegion.XiRho.Support`
as the very same constants.
-/

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

export ProbabilityTheory.Copula.RankRegion.Common (centralW_rho deterministic_rho_attained)

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
