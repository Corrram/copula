import Copula.Rank.Region.XiBlest.Support.ConditionalIID

/-! # Conditional means and the copula correlation ratio -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

/-- The integral of a distribution function on [0,1] is one minus its mean. -/
theorem integral_unit_cdf (μ : Measure I) [IsProbabilityMeasure μ] :
    (∫ u : I, μ.real (Iic u)) = 1 - ∫ v : I, (v : ℝ) ∂μ := by
  have hi : Integrable (fun p : I × I => if p.2 ≤ p.1 then (1 : ℝ) else 0)
      ((volume : Measure I).prod μ) := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (measurable_const.ite (measurableSet_le measurable_snd measurable_fst)
        measurable_const).aestronglyMeasurable
    · split_ifs <;> norm_num
  have hF (u : I) : μ.real (Iic u) = ∫ v : I, if v ≤ u then (1 : ℝ) else 0 ∂μ := by
    have h := integral_indicator (μ := μ) (f := fun _ : I => (1 : ℝ)) (s := Iic u) measurableSet_Iic
    simpa [Set.indicator, smul_eq_mul] using h.symm
  simp_rw [hF]
  rw [integral_integral_swap hi]
  simp_rw [Copula.integral_unit_upper_indicator]
  rw [integral_sub (integrable_const _) (Copula.integrable_continuous_unit μ continuous_subtype_val)]
  simp

/-- Mean of the conditional distribution of the response rank. -/
noncomputable def conditionalMean (C : Copula 2) (t : I) : ℝ :=
  ∫ v : I, (v : ℝ) ∂C.conditionalKernel t

/-- The conditional-mean identity holds for every value of the selected Markov kernel. -/
theorem conditionalMean_eq (C : Copula 2) (t : I) :
    conditionalMean C t = 1 - ∫ v : I, C.conditionalCDF t v := by
  have h := integral_unit_cdf (C.conditionalKernel t)
  change (∫ v : I, C.conditionalCDF t v) = 1 - conditionalMean C t at h
  linarith

private theorem cdf_joint_integrable (C : Copula 2) :
    Integrable (fun p : I × I => C.conditionalCDF p.2 p.1)
      ((volume : Measure I).prod volume) := by
  refine (integrable_const (1 : ℝ)).mono' C.measurable_conditionalCDF.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun p => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (C.conditionalCDF_nonneg _ _)]
      using C.conditionalCDF_le_one p.2 p.1

private theorem cdf_mean_mem (C : Copula 2) (t : I) :
    (∫ v : I, C.conditionalCDF t v) ∈ Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg (fun v => C.conditionalCDF_nonneg t v), ?_⟩
  have hi : Integrable (fun v => C.conditionalCDF t v) := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
    · exact (C.measurable_conditionalCDF.comp
        (show Measurable (fun v : I => (v, t)) by fun_prop)).aestronglyMeasurable
    · simpa only [Real.norm_eq_abs, abs_of_nonneg (C.conditionalCDF_nonneg _ _)]
        using C.conditionalCDF_le_one t v
  simpa using integral_mono hi (integrable_const (1 : ℝ)) (fun v => C.conditionalCDF_le_one t v)

private theorem cdf_mean_integral (C : Copula 2) :
    (∫ t : I, ∫ v : I, C.conditionalCDF t v) = 1 / 2 := by
  rw [← integral_integral_swap (cdf_joint_integrable C)]
  simp_rw [C.integral_conditionalCDF]
  exact Copula.integral_unit_id

/-- The copula correlation ratio is the conditional-mean variance divided by 1/12. -/
noncomputable def correlationRatio (C : Copula 2) : ℝ :=
  12 * ∫ t : I, (conditionalMean C t - 1 / 2) ^ 2

/-- Rho of the conditional-copy copula is the original copula correlation ratio. -/
theorem conditionalIID_rho_eq_ratio (C : Copula 2) :
    (conditionalIID C).spearmanRho = correlationRatio C := by
  have hi := (cdf_joint_integrable C).integral_prod_right
  have hm : Measurable (fun t : I => ∫ v : I, C.conditionalCDF t v) :=
    C.measurable_conditionalCDF.stronglyMeasurable.integral_prod_left.measurable
  have hsq : Integrable (fun t : I => (∫ v : I, C.conditionalCDF t v) ^ 2) := by
    refine (integrable_const (1 : ℝ)).mono' (hm.pow_const 2).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [(cdf_mean_mem C t).1, (cdf_mean_mem C t).2]
  have he : (fun t : I => (conditionalMean C t - 1 / 2) ^ 2) =
      fun t => (∫ v : I, C.conditionalCDF t v) ^ 2 - (∫ v : I, C.conditionalCDF t v) + 1 / 4 := by
    funext t
    rw [conditionalMean_eq]
    ring
  have heint : (∫ t : I, (conditionalMean C t - 1 / 2) ^ 2) =
      (∫ t : I, (∫ v : I, C.conditionalCDF t v) ^ 2) - 1 / 4 := by
    rw [he]
    have h₁ := integral_add (hsq.sub hi) (integrable_const (1 / 4 : ℝ))
    have h₂ := integral_sub hsq hi
    simp only [Pi.sub_apply] at h₁ h₂
    rw [h₁, h₂, cdf_mean_integral]
    norm_num
    ring
  rw [conditionalIID_rho, correlationRatio, heint]
  ring

theorem correlationRatio_nonneg (C : Copula 2) : 0 ≤ correlationRatio C :=
  mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _)

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
