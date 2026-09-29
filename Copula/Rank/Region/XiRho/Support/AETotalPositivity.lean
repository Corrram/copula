/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.XiRho.Support.StepDensity
import Copula.Rank.Region.Common.AETotalPositivity

/-! # Ordered density minors, with a null-set invariant convention (re-export)

Compatibility module. The development lives in
`Copula.Rank.Region.Common.AETotalPositivity`, namespace
`ProbabilityTheory.Copula.RankRegion.Common`. The `export` below makes its public
declarations available under
`ProbabilityTheory.Copula.RankRegion.XiRho.Support`
as the very same constants.
-/

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

export ProbabilityTheory.Copula.RankRegion.Common (HasAEOrderedMinors HasAEOrderedMinors.congr
  aeOrderedMinors_congr exists_mem_Ioo_of_ae medianSign_antitone stepDensity_minor
  stepDensity_ordered_minors stepDensity_ae_minors_iff IsRR2 HasRR2Density aeOrderedMinors_of_tp2
  aeOrderedMinors_of_rr2 ae_curry_of_ae_eq density_ae_eq)

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
