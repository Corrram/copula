/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.Common.TentIntegral

/-! # Exact squared integral of a median tent (re-export)

Compatibility module. The development lives in
`Copula.Rank.Region.Common.TentIntegral`, namespace
`ProbabilityTheory.Copula.RankRegion.Common`. The `export` below makes its public
declarations available under
`ProbabilityTheory.Copula.RankRegion.XiBeta`
as the very same constants.
-/

namespace ProbabilityTheory.Copula.RankRegion.XiBeta

export ProbabilityTheory.Copula.RankRegion.Common (medianTent continuous_medianTent
  medianTent_lipschitz integral_medianTent_sq)

end ProbabilityTheory.Copula.RankRegion.XiBeta
