/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.XiRho.Support.TwoStrip
import Copula.Rank.Region.Common.StepDensity

/-! # Exact density identification for two-strip copulas (re-export)

Compatibility module. The development lives in
`Copula.Rank.Region.Common.StepDensity`, namespace
`ProbabilityTheory.Copula.RankRegion.Common`. The `export` below makes its public
declarations available under
`ProbabilityTheory.Copula.RankRegion.XiRho.Support`
as the very same constants.
-/

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

export ProbabilityTheory.Copula.RankRegion.Common (lowerStep measurable_lowerStep
  integrable_lowerStep integral_lowerStep medianSign measurable_medianSign integral_medianSign
  twoStrip_density)

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
