/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.Common.AETotalPositivity
import Copula.Rank.Region.Common.CenteredOrdinal
import Copula.Rank.Region.Common.CenteredProperties
import Copula.Rank.Region.Common.ClampedRhoOptimization
import Copula.Rank.Region.Common.ConditionalCopula
import Copula.Rank.Region.Common.DeterministicRho
import Copula.Rank.Region.Common.DiagonalBand
import Copula.Rank.Region.Common.Functional
import Copula.Rank.Region.Common.Mixture
import Copula.Rank.Region.Common.RampIntegrals
import Copula.Rank.Region.Common.RankMoments
import Copula.Rank.Region.Common.Shuffle
import Copula.Rank.Region.Common.StepDensity
import Copula.Rank.Region.Common.StochasticBounds
import Copula.Rank.Region.Common.StochasticRho
import Copula.Rank.Region.Common.StochasticRigidity
import Copula.Rank.Region.Common.TentIntegral
import Copula.Rank.Region.Common.TwoStrip
import Copula.Rank.Region.Common.XiAffineRegion
import Copula.Rank.Region.Common.XiReflection

/-! # Shared support for the exact-region developments

The modules under `Copula.Rank.Region.Common` (namespace
`ProbabilityTheory.Copula.RankRegion.Common`) collect the auxiliary results that the
`XiRho`, `XiBlest`, `XiBeta`, `TauFootruleBeta` and `MeanVariance` region developments
share: centered ordinal sums with a countermonotonic block, diagonal-band and two-strip
copulas, finite increasing shuffles, conditional-copula constructions, stochastic
monotonicity bounds relating ξ, ρ and the footrule, ramp and tent integrals, measurable
functional witnesses, and continuity along mixtures.

The historical module paths `Copula.Rank.Region.<X>.Support.*` (and
`Copula.Rank.Region.XiBeta.{TwoStrip,TentIntegral}`) remain as thin compatibility modules
that `export` these declarations into their original namespaces, so every old name
denotes the same constant as its `Common` counterpart.
-/
