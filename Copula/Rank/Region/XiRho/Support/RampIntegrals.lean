/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.Common.RampIntegrals

/-! # Polynomial moments of a truncated linear ramp (re-export)

Compatibility module. The development lives in
`Copula.Rank.Region.Common.RampIntegrals`, namespace
`ProbabilityTheory.Copula.RankRegion.Common`. The `export` below makes its public
declarations available under
`ProbabilityTheory.Copula.RankRegion.XiRho.Support`
as the very same constants.
-/

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

export ProbabilityTheory.Copula.RankRegion.Common (ramp continuous_ramp ramp_mem integral_ramp_pow
  integral_ramp integral_ramp_sq integral_id_mul_ramp integral_weight_mul_ramp
  integral_unit_reflection integral_complement_reflected_ramp_sq
  integral_weight_complement_reflected_ramp integral_unit_two_halves integral_sqrt_two_cube_half)

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
