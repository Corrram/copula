import Copula.Rank.Region.XiBlest.Support.ConditionalMean

/-! # Measurability and boundedness of conditional means -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

theorem conditionalMean_measurable (C : Copula 2) : Measurable (conditionalMean C) := by
  change Measurable (fun u => conditionalMean C u)
  simp_rw [conditionalMean_eq]
  exact measurable_const.sub C.measurable_conditionalCDF.stronglyMeasurable.integral_prod_left.measurable

theorem conditionalMean_mem (C : Copula 2) (u : I) : conditionalMean C u ∈ Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg (fun v => v.property.1),?_⟩
  have h := integral_mono (Copula.integrable_continuous_unit (C.conditionalKernel u) continuous_subtype_val)
    (integrable_const (1 : ℝ)) (fun v : I => v.property.2)
  simpa [conditionalMean] using h

theorem conditionalMean_centered_sq_integrable (C : Copula 2) :
    Integrable (fun u => (conditionalMean C u-1/2)^2) := by
  refine (integrable_const (1 : ℝ)).mono'
    (((conditionalMean_measurable C).sub measurable_const).pow_const 2).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have h := conditionalMean_mem C u
    nlinarith [h.1,h.2]

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
