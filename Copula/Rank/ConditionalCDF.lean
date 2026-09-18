/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.Conditional
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! # Identifying conditional CDFs by their lower-interval integrals -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- An integrable nonnegative candidate is a version of the conditional CDF
at a fixed threshold if its indefinite integrals recover the copula CDF.
The exceptional null set is allowed to depend on the threshold. -/
theorem conditionalCDF_ae_eq_of_integral (C : Copula 2) (v : I) {f : I → ℝ}
    (hf : Integrable f) (hn : ∀ t, 0 ≤ f t)
    (hF : ∀ u, (∫ t in Iic u, f t) = C.cdf ![u, v]) :
    (fun t => C.conditionalCDF t v) =ᵐ[volume] f := by
  have hK := C.integrable_conditionalCDF v
  have := isFiniteMeasure_withDensity_ofReal hK.2
  have he : (volume : Measure I).withDensity (fun t => ENNReal.ofReal (C.conditionalCDF t v)) =
      (volume : Measure I).withDensity (fun t => ENNReal.ofReal (f t)) := by
    apply Measure.ext_of_Iic
    intro u
    rw [withDensity_apply _ measurableSet_Iic, withDensity_apply _ measurableSet_Iic,
      ← ofReal_integral_eq_lintegral_ofReal hK.integrableOn
        (Filter.Eventually.of_forall (fun t => C.conditionalCDF_nonneg t v)),
      ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (Filter.Eventually.of_forall hn),
      hF, C.cdf_eq_integral_conditionalCDF]
  have hae := (withDensity_eq_iff_of_sigmaFinite
    (C.measurable_conditionalCDF_left v).ennreal_ofReal.aemeasurable
    hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mp he
  filter_upwards [hae] with t ht
  have h := congrArg ENNReal.toReal ht
  simpa only [ENNReal.toReal_ofReal (C.conditionalCDF_nonneg t v),
    ENNReal.toReal_ofReal (hn t)] using h

end ProbabilityTheory.Copula
