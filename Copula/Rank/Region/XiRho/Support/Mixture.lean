/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.Common.Mixture

/-! # Continuous coefficient paths along copula mixtures (re-export)

Compatibility module. The development lives in
`Copula.Rank.Region.Common.Mixture`, namespace
`ProbabilityTheory.Copula.RankRegion.Common`. The `export` below makes its public
declarations available under
`ProbabilityTheory.Copula.RankRegion.XiRho.Support`
as the very same constants.
-/

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

export ProbabilityTheory.Copula.RankRegion.Common (continuous_xi_mix continuous_tau_mix
  exists_unitInterval_eq)

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
