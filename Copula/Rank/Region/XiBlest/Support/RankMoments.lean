/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.Common.RankMoments

/-! # Absolute-displacement moment representations (re-export)

Compatibility module. The development lives in
`Copula.Rank.Region.Common.RankMoments`, namespace
`ProbabilityTheory.Copula.RankRegion.Common`. The `export` below makes its public
declarations available under
`ProbabilityTheory.Copula.RankRegion.XiBlest.Support`
as the very same constants.
-/

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

export ProbabilityTheory.Copula.RankRegion.Common (footrule_eq_abs_moment gamma_eq_abs_moments)

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
