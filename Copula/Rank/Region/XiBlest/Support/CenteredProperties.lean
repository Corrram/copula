/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.XiBlest.Support.CenteredOrdinal
import Copula.Rank.Region.XiBlest.Support.Functional
import Copula.Rank.Region.Common.CenteredProperties

/-! # Dependence and symmetry of a central countermonotonic block (re-export)

Compatibility module. The development lives in
`Copula.Rank.Region.Common.CenteredProperties`, namespace
`ProbabilityTheory.Copula.RankRegion.Common`. The `export` below makes its public
declarations available under
`ProbabilityTheory.Copula.RankRegion.XiBlest.Support`
as the very same constants.
-/

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

export ProbabilityTheory.Copula.RankRegion.Common (centralMargin_lt_one central_top
  centeredOrdinal_cdf_below centeredOrdinal_cdf_above centralEmbed_surjectiveOn centralW
  centralW_exchangeable centralW_xi centralW_beta centralW_cdf_inside centralW_cdf_ordered
  centralW_radiallySymmetric centralW_pqd)

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
