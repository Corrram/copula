/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.Common.TwoStrip

/-! # Copulas from a Lipschitz displacement on two median strips (re-export)

Compatibility module. The development lives in
`Copula.Rank.Region.Common.TwoStrip`, namespace
`ProbabilityTheory.Copula.RankRegion.Common`. The `export` below makes its public
declarations available under
`ProbabilityTheory.Copula.RankRegion.XiRho.Support`
as the very same constants.
-/

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

export ProbabilityTheory.Copula.RankRegion.Common (StripDisplacement StripDisplacement.abs_le
  StripDisplacement.casesOn StripDisplacement.continuous StripDisplacement.ctorIdx
  StripDisplacement.lipschitz StripDisplacement.mk StripDisplacement.mk.inj
  StripDisplacement.mk.injEq StripDisplacement.mk.noConfusion StripDisplacement.mk.sizeOf_spec
  StripDisplacement.noConfusion StripDisplacement.noConfusionType StripDisplacement.one
  StripDisplacement.rec StripDisplacement.recOn StripDisplacement.toFun StripDisplacement.zero
  medianWedge medianWedge_lipschitz twoStrip cdf_twoStrip stripKernel stripKernel_integrable
  integral_median_step integral_stripKernel_Iic conditionalCDF_twoStrip integral_stripKernel_sq
  xi_twoStrip beta_twoStrip instCoeFunStripDisplacementForallElemRealUnitInterval)

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
