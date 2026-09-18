/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Full support of uniform measure on the closed unit interval -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Every nonempty relatively open subset of the unit interval has positive volume. -/
instance isOpenPosMeasure_unitInterval : (volume : Measure I).IsOpenPosMeasure where
  open_pos U hU hne := by
    obtain ⟨a, b, hab, hs⟩ := hU.exists_Ioo_subset hne
    apply ne_of_gt
    apply lt_of_lt_of_le _ (measure_mono hs)
    rw [unitInterval.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)

end ProbabilityTheory.Copula
