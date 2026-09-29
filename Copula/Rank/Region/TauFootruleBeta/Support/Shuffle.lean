/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.TauFootruleBeta.Support.RankMoments
import Copula.Rank.Region.Common.Shuffle

/-! # Finite shuffles with increasing strips (re-export)

Compatibility module. The development lives in
`Copula.Rank.Region.Common.Shuffle`, namespace
`ProbabilityTheory.Copula.RankRegion.Common`. The `export` below makes its public
declarations available under
`ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support`
as the very same constants.
-/

namespace ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support

export ProbabilityTheory.Copula.RankRegion.Common (stripCut stripCut_eq_min_sub stripCut_zero
  stripCut_full stripCut_inside ShuffleStrip ShuffleStrip.casesOn ShuffleStrip.continuous_point
  ShuffleStrip.ctorIdx ShuffleStrip.instIsFiniteMeasureForallFinOfNatNatElemRealUnitIntervalLaw
  ShuffleStrip.integral_law ShuffleStrip.law ShuffleStrip.law_Iic ShuffleStrip.law_univ
  ShuffleStrip.mk ShuffleStrip.mk.inj ShuffleStrip.mk.injEq ShuffleStrip.mk.noConfusion
  ShuffleStrip.mk.sizeOf_spec ShuffleStrip.noConfusion ShuffleStrip.noConfusionType
  ShuffleStrip.point ShuffleStrip.rec ShuffleStrip.recOn ShuffleStrip.width
  ShuffleStrip.width_nonneg ShuffleStrip.x ShuffleStrip.x_end ShuffleStrip.x_nonneg ShuffleStrip.y
  ShuffleStrip.y_end ShuffleStrip.y_nonneg PositiveShuffle PositiveShuffle.casesOn
  PositiveShuffle.cdf PositiveShuffle.cdf_point PositiveShuffle.copula PositiveShuffle.ctorIdx
  PositiveShuffle.footrule
  PositiveShuffle.instIsFiniteMeasureForallFinOfNatNatElemRealUnitIntervalLaw
  PositiveShuffle.instIsProbabilityMeasureForallFinOfNatNatElemRealUnitIntervalLaw
  PositiveShuffle.integral_copula PositiveShuffle.law PositiveShuffle.law_Iic
  PositiveShuffle.marginal PositiveShuffle.mk PositiveShuffle.mk.inj PositiveShuffle.mk.injEq
  PositiveShuffle.mk.noConfusion PositiveShuffle.mk.sizeOf_spec PositiveShuffle.noConfusion
  PositiveShuffle.noConfusionType PositiveShuffle.rec PositiveShuffle.recOn PositiveShuffle.strip
  PositiveShuffle.tau PositiveShuffle.tile_x PositiveShuffle.tile_y PositiveShuffle.total)

end ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support
