/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.Measure

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion

/-- Integrate a measurable observable when its two pullbacks are integrable.
This includes the threshold signs in magnitude constructions. -/
theorem integral_ordinalSum_measurable (C D : Copula 2) (a : I)
    {f : (Fin 2 → I) → ℝ} (hf : Measurable f)
    (hL : Integrable (fun x => f (fun i => OrdinalSum.lowerEmbed a (x i))) C.toMeasure)
    (hU : Integrable (fun x => f (fun i => OrdinalSum.upperEmbed a (x i))) D.toMeasure) :
    (∫ x, f x ∂(C.ordinalSum D a).toMeasure) =
      (a : ℝ) * (∫ x, f (fun i => OrdinalSum.lowerEmbed a (x i)) ∂C.toMeasure) +
      (1 - (a : ℝ)) * ∫ x, f (fun i => OrdinalSum.upperEmbed a (x i)) ∂D.toMeasure := by
  have hmL : Measurable (fun (x : Fin 2 → I) i => OrdinalSum.lowerEmbed a (x i)) := by fun_prop
  have hmU : Measurable (fun (x : Fin 2 → I) i => OrdinalSum.upperEmbed a (x i)) := by fun_prop
  have hiL := (integrable_map_measure hf.aestronglyMeasurable hmL.aemeasurable).mpr hL
  have hiU := (integrable_map_measure hf.aestronglyMeasurable hmU.aemeasurable).mpr hU
  rw [toMeasure_ordinalSum, integral_add_measure
    (hiL.smul_measure ENNReal.ofReal_ne_top) (hiU.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure,
    integral_map hmL.aemeasurable hf.aestronglyMeasurable,
    integral_map hmU.aemeasurable hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal a.property.1, ENNReal.toReal_ofReal (sub_nonneg.mpr a.property.2)]
  rfl

end ProbabilityTheory.Copula.RankRegion
