/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.Common.Functional

/-! # Measurable functional dependence survives ordinal sums (re-export)

Compatibility module. The development lives in
`Copula.Rank.Region.Common.Functional`, namespace
`ProbabilityTheory.Copula.RankRegion.Common`. The `export` below makes its public
declarations available under
`ProbabilityTheory.Copula.RankRegion.XiRho.Support`
as the very same constants.
-/

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

export ProbabilityTheory.Copula.RankRegion.Common (HasFunctionalWitness
  HasFunctionalWitness.ordinalSum HasFunctionalWitness.xi_eq_one functional_comonotonic
  functional_countermonotonic)

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
