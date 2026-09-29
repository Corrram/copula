/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.Common.CenteredOrdinal

/-! # The centered ordinal-sum identities (equation 9) (re-export)

Compatibility module. The development lives in
`Copula.Rank.Region.Common.CenteredOrdinal`, namespace
`ProbabilityTheory.Copula.RankRegion.Common`. The `export` below makes its public
declarations available under
`ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support`
as the very same constants.
-/

namespace ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support

export ProbabilityTheory.Copula.RankRegion.Common (centralMargin centralSplit central_weight
  centeredOrdinal centeredOrdinal_zero centeredOrdinal_one centralEmbed coe_centralEmbed
  centeredOrdinal_cdf centeredOrdinal_tau centeredOrdinal_footrule centeredOrdinal_beta
  centeredOrdinal_rho)

end ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support
