import Copula.Classical.Bivariate
import Copula.Rank.Chatterjee
import Copula.Rank.SpearmanCDF
import Copula.Rank.Benchmarks

/-! # The copula of two conditionally independent response copies

Its distribution function is the integral of the product of the two conditional
CDFs. The construction applies to every copula, including singular laws.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

private theorem kernel_product_integrable (C : Copula 2) (u v : I) :
    Integrable (fun t => C.conditionalCDF t u * C.conditionalCDF t v) := by
  refine (C.integrable_conditionalCDF v).mono'
    ((C.measurable_conditionalCDF_left u).mul
      (C.measurable_conditionalCDF_left v)).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (C.conditionalCDF_nonneg t u)
      (C.conditionalCDF_nonneg t v))]
    exact mul_le_of_le_one_left (C.conditionalCDF_nonneg t v) (C.conditionalCDF_le_one t u)

private theorem kernel_zero_ae (C : Copula 2) :
    (fun t => C.conditionalCDF t 0) =ᵐ[volume] 0 := by
  apply (integral_eq_zero_iff_of_nonneg (fun t => C.conditionalCDF_nonneg t 0)
    (C.integrable_conditionalCDF 0)).mp
  simpa using C.integral_conditionalCDF 0

private theorem kernel_one (C : Copula 2) (t : I) : C.conditionalCDF t 1 = 1 := by
  have he : Iic (1 : I) = univ := by ext u; simp [unitInterval.le_one']
  simp [Copula.conditionalCDF, he]

private theorem kernel_mono (C : Copula 2) (t : I) : Monotone (C.conditionalCDF t) := by
  intro u v huv
  exact measureReal_mono (Iic_subset_Iic.mpr huv)

/-- Positivity of rectangle increments follows from monotonicity of each conditional CDF. -/
theorem conditionalIID_classical (C : Copula 2) :
    Copula.IsClassical (fun x : Fin 2 → I =>
      ∫ t : I, C.conditionalCDF t (x 0) * C.conditionalCDF t (x 1)) := by
  apply Copula.IsClassical.ofBivariate (fun u v => ∫ t : I, C.conditionalCDF t u * C.conditionalCDF t v)
  · intro v
    apply integral_eq_zero_of_ae
    filter_upwards [kernel_zero_ae C] with t ht
    simp [ht]
  · intro u
    apply integral_eq_zero_of_ae
    filter_upwards [kernel_zero_ae C] with t ht
    simp [ht]
  · intro v
    simp_rw [kernel_one, one_mul]
    exact C.integral_conditionalCDF v
  · intro u
    simp_rw [kernel_one, mul_one]
    exact C.integral_conditionalCDF u
  · intro a b c d hab hcd
    have hi₁ := kernel_product_integrable C b d
    have hi₂ := kernel_product_integrable C a d
    have hi₃ := kernel_product_integrable C b c
    have hi₄ := kernel_product_integrable C a c
    have he : (∫ t : I, C.conditionalCDF t b * C.conditionalCDF t d -
        C.conditionalCDF t a * C.conditionalCDF t d - C.conditionalCDF t b * C.conditionalCDF t c +
        C.conditionalCDF t a * C.conditionalCDF t c) =
        (∫ t : I, C.conditionalCDF t b * C.conditionalCDF t d) -
        (∫ t : I, C.conditionalCDF t a * C.conditionalCDF t d) -
        (∫ t : I, C.conditionalCDF t b * C.conditionalCDF t c) +
        (∫ t : I, C.conditionalCDF t a * C.conditionalCDF t c) := by
      exact (integral_add ((hi₁.sub hi₂).sub hi₃) hi₄).trans
        (congrArg (fun r : ℝ => r + ∫ t : I, C.conditionalCDF t a * C.conditionalCDF t c)
          ((integral_sub (hi₁.sub hi₂) hi₃).trans
            (congrArg (fun r : ℝ => r - ∫ t : I, C.conditionalCDF t b * C.conditionalCDF t c)
              (integral_sub hi₁ hi₂))))
    rw [← he]
    apply integral_nonneg
    intro t
    have h := mul_nonneg (sub_nonneg.mpr (kernel_mono C t hab))
      (sub_nonneg.mpr (kernel_mono C t hcd))
    dsimp only [Pi.zero_apply]
    nlinarith only [h]

/-- The law of two conditionally independent copies of coordinate 1 given coordinate 0. -/
noncomputable def conditionalIID (C : Copula 2) : Copula 2 :=
  Copula.ofClassical _ (conditionalIID_classical C)

theorem conditionalIID_cdf (C : Copula 2) (u v : I) :
    (conditionalIID C).cdf ![u, v] = ∫ t : I, C.conditionalCDF t u * C.conditionalCDF t v := by
  simp [conditionalIID]

/-- The Markov-square footrule is exactly the original directed Chatterjee coefficient. -/
theorem conditionalIID_footrule (C : Copula 2) :
    (conditionalIID C).spearmanFootrule = C.chatterjeeXi := by
  unfold Copula.spearmanFootrule Copula.chatterjeeXi
  simp_rw [conditionalIID_cdf, pow_two]

/-- Integral formula for rho of the conditional-copy law. -/
theorem conditionalIID_rho (C : Copula 2) :
    (conditionalIID C).spearmanRho =
      12 * (∫ t : I, (∫ u : I, C.conditionalCDF t u) ^ 2) - 3 := by
  have hi : Integrable (fun p : (Fin 2 → I) × I =>
      C.conditionalCDF p.2 (p.1 0) * C.conditionalCDF p.2 (p.1 1))
      ((Copula.independence 2).toMeasure.prod volume) := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · have h₀ := C.measurable_conditionalCDF.comp
        (show Measurable (fun p : (Fin 2 → I) × I => (p.1 0, p.2)) by fun_prop)
      have h₁ := C.measurable_conditionalCDF.comp
        (show Measurable (fun p : (Fin 2 → I) × I => (p.1 1, p.2)) by fun_prop)
      exact (h₀.mul h₁).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (C.conditionalCDF_nonneg _ _)
        (C.conditionalCDF_nonneg _ _))]
      exact (mul_le_of_le_one_left (C.conditionalCDF_nonneg _ _) (C.conditionalCDF_le_one _ _)).trans
        (C.conditionalCDF_le_one _ _)
  rw [Copula.spearmanRho_eq_integral_cdf]
  have hc : (conditionalIID C).cdf = fun x : Fin 2 → I =>
      ∫ t : I, C.conditionalCDF t (x 0) * C.conditionalCDF t (x 1) := by
    funext x
    simp [conditionalIID]
  rw [hc, integral_integral_swap hi]
  simp_rw [Copula.integral_independence_mul, pow_two]

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
