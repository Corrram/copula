import Copula.Rank.ConditionalCDF
import Copula.Reflection.Bivariate

/-! # Reflection of the response coordinate preserves directional xi -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

theorem conditionalCDF_reflect_second (C : Copula 2) (v : I) :
    (fun u => (C.reflect {1}).conditionalCDF u v) =ᵐ[volume]
      fun u => 1 - C.conditionalCDF u (unitInterval.symm v) := by
  apply Copula.conditionalCDF_ae_eq_of_integral _ v
    ((integrable_const 1).sub (C.integrable_conditionalCDF _))
    (fun u => sub_nonneg.mpr (C.conditionalCDF_le_one u _))
  intro u
  simp only [Pi.sub_apply]
  rw [integral_sub (integrable_const _) (C.integrable_conditionalCDF _).integrableOn,
    ← C.cdf_eq_integral_conditionalCDF, C.cdf_reflect_second]
  simp [integral_const, Measure.real, unitInterval.volume_Iic,
    ENNReal.toReal_ofReal u.property.1]

theorem xi_reflect_second (C : Copula 2) : (C.reflect {1}).chatterjeeXi = C.chatterjeeXi := by
  have he (v : I) : (∫ u : I, (C.reflect {1}).conditionalCDF u v ^ 2) =
      1 - 2 * (1 - (v : ℝ)) + (∫ u : I, C.conditionalCDF u (unitInterval.symm v) ^ 2) := by
    calc
      _ = ∫ u : I, 1 - 2 * C.conditionalCDF u (unitInterval.symm v) +
          C.conditionalCDF u (unitInterval.symm v) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [conditionalCDF_reflect_second C v] with u hu
        rw [hu]
        ring
      _ = _ := by
        have hi : Integrable (fun u => 2 * C.conditionalCDF u (unitInterval.symm v)) :=
          (C.integrable_conditionalCDF _).const_mul _
        have hj : Integrable (fun u => 1 - 2 * C.conditionalCDF u (unitInterval.symm v)) :=
          (integrable_const 1).sub hi
        rw [integral_add hj (C.integrable_conditionalCDF_sq _),
          integral_sub (integrable_const _) hi, integral_const_mul, C.integral_conditionalCDF]
        simp [unitInterval.coe_symm_eq]
  have hs := unitInterval.measurePreserving_symm.integral_comp
    unitInterval.symmMeasurableEquiv.measurableEmbedding
    (fun v : I => ∫ u : I, C.conditionalCDF u v ^ 2)
  have hcomp : Integrable (fun v : I => ∫ u : I, C.conditionalCDF u (unitInterval.symm v) ^ 2) :=
    unitInterval.measurePreserving_symm.integrable_comp_of_integrable C.integrable_integral_conditionalCDF_sq
  have hi : (∫ v : I, 1 - 2 * (1 - (v : ℝ))) = 0 := by
    rw [integral_sub (integrable_const _) ((Copula.integrable_continuous_unit volume
      (show Continuous (fun v : I => 1 - (v : ℝ)) by fun_prop)).const_mul _),
      integral_const_mul, integral_sub (integrable_const _)
        (Copula.integrable_continuous_unit volume continuous_subtype_val), Copula.integral_unit_id]
    norm_num
  unfold Copula.chatterjeeXi
  simp_rw [he]
  rw [integral_add (Copula.integrable_continuous_unit volume (by fun_prop)) hcomp, hi, zero_add, hs]

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
