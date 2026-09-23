import Copula.Rank.Region.XiBlest.Support.ConditionalMeanRegularity

/-! # Conditional CDFs with exact endpoints at every predictor -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

/-- Removing the null response endpoint makes rescaling identities pointwise. -/
noncomputable def normalizedCDF (C : Copula 2) (u v : I) : ℝ :=
  if v = 0 then 0 else C.conditionalCDF u v

theorem normalizedCDF_measurable (C : Copula 2) :
    Measurable (fun p : I × I => normalizedCDF C p.2 p.1) :=
  measurable_const.ite (measurableSet_eq_fun measurable_fst measurable_const) C.measurable_conditionalCDF

theorem normalizedCDF_mem (C : Copula 2) (u v : I) : normalizedCDF C u v ∈ Icc (0 : ℝ) 1 := by
  unfold normalizedCDF
  split_ifs
  · exact ⟨le_rfl,zero_le_one⟩
  · exact ⟨C.conditionalCDF_nonneg u v,C.conditionalCDF_le_one u v⟩

theorem normalizedCDF_zero (C : Copula 2) (u : I) : normalizedCDF C u 0 = 0 := by simp [normalizedCDF]

theorem normalizedCDF_one (C : Copula 2) (u : I) : normalizedCDF C u 1 = 1 := by
  have he : Iic (1 : I) = univ := by ext v; simp [unitInterval.le_one']
  simp [normalizedCDF,Copula.conditionalCDF,he]

theorem normalizedCDF_mono (C : Copula 2) (u : I) : Monotone (normalizedCDF C u) := by
  intro v w hvw
  by_cases hv : v = 0
  · rw [hv,normalizedCDF_zero]
    exact (normalizedCDF_mem C u w).1
  have hw : w ≠ 0 := by intro h; exact hv (le_antisymm (h ▸ hvw) v.property.1)
  simp only [normalizedCDF,ite_eq_right hv,ite_eq_right hw]
  exact measureReal_mono (Iic_subset_Iic.mpr hvw)

theorem normalizedCDF_ae (C : Copula 2) (v : I) :
    (fun u => normalizedCDF C u v) =ᵐ[volume] fun u => C.conditionalCDF u v := by
  by_cases hv : v = 0
  · subst v
    have hz : (fun u => C.conditionalCDF u 0) =ᵐ[volume] fun _ => 0 :=
      (integral_eq_zero_iff_of_nonneg (fun u => C.conditionalCDF_nonneg u 0)
        (C.integrable_conditionalCDF 0)).mp (C.integral_conditionalCDF 0)
    simpa only [normalizedCDF_zero] using hz.symm
  · exact Filter.Eventually.of_forall fun u => by simp only [normalizedCDF,ite_eq_right hv]

theorem normalizedCDF_response_ae (C : Copula 2) (u : I) :
    normalizedCDF C u =ᵐ[volume] C.conditionalCDF u := by
  filter_upwards [Measure.ae_ne (volume : Measure I) 0] with v hv
  simp only [normalizedCDF,ite_eq_right hv]

theorem normalizedCDF_integrable (C : Copula 2) (v : I) :
    Integrable (fun u => normalizedCDF C u v) :=
  (C.integrable_conditionalCDF v).congr (normalizedCDF_ae C v).symm

theorem normalizedCDF_mean (C : Copula 2) (v : I) : (∫ u : I, normalizedCDF C u v) = v := by
  rw [integral_congr_ae (normalizedCDF_ae C v),C.integral_conditionalCDF]

theorem normalizedCDF_response_integrable (C : Copula 2) (u : I) : Integrable (normalizedCDF C u) := by
  refine (integrable_const (1 : ℝ)).mono'
    ((normalizedCDF_measurable C).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun v => by
    rw [Real.norm_eq_abs,abs_of_nonneg (normalizedCDF_mem C u v).1]
    exact (normalizedCDF_mem C u v).2

theorem normalizedCDF_response_integral (C : Copula 2) (u : I) :
    (∫ v : I, normalizedCDF C u v) = 1-conditionalMean C u := by
  rw [integral_congr_ae (normalizedCDF_response_ae C u),conditionalMean_eq]
  ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
