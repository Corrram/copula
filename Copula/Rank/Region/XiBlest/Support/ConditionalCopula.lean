import Copula.Classical.Bivariate
import Copula.Rank.ConditionalCDF
import Copula.Dependence.ConditionalMonotonicity

/-! # Constructing a copula from a family of conditional CDFs -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

/-- Integral construction, with uniform mean and monotonicity in the response threshold. -/
theorem conditional_integral_classical (h : I → I → ℝ)
    (hi : ∀ v, Integrable (h v))
    (hm : ∀ u, Monotone (fun v => h v u))
    (hz : ∀ u, h 0 u = 0) (ho : ∀ u, h 1 u = 1)
    (hmean : ∀ v, (∫ u : I, h v u) = (v : ℝ)) :
    Copula.IsClassical (fun z : Fin 2 → I => ∫ u in Iic (z 0), h (z 1) u) := by
  apply Copula.IsClassical.ofBivariate (fun u v => ∫ t in Iic u, h v t)
  · intro v
    have he : Iic (0 : I) = {0} := by ext u; simp
    simp [he]
  · intro u
    simp_rw [hz]
    simp
  · intro v
    have he : Iic (1 : I) = univ := by ext u; simp [unitInterval.le_one']
    simpa only [he, Measure.restrict_univ] using hmean v
  · intro u
    simp_rw [ho]
    simp [integral_const, Measure.real, unitInterval.volume_Iic,
      ENNReal.toReal_ofReal u.property.1]
  · intro a b c d hab hcd
    have hc := Copula.integral_Iic_add_Ioc_unit (hi c) hab
    have hd := Copula.integral_Iic_add_Ioc_unit (hi d) hab
    have he := setIntegral_mono_on (hi c).integrableOn (hi d).integrableOn
      measurableSet_Ioc (fun u (_ : u ∈ Ioc a b) => hm u hcd)
    linarith

noncomputable def copulaOfConditional (h : I → I → ℝ)
    (hi : ∀ v, Integrable (h v))
    (hm : ∀ u, Monotone (fun v => h v u))
    (hz : ∀ u, h 0 u = 0) (ho : ∀ u, h 1 u = 1)
    (hmean : ∀ v, (∫ u : I, h v u) = (v : ℝ)) : Copula 2 :=
  Copula.ofClassical _ (conditional_integral_classical h hi hm hz ho hmean)

theorem copulaOfConditional_cdf (h : I → I → ℝ)
    (hi : ∀ v, Integrable (h v))
    (hm : ∀ u, Monotone (fun v => h v u))
    (hz : ∀ u, h 0 u = 0) (ho : ∀ u, h 1 u = 1)
    (hmean : ∀ v, (∫ u : I, h v u) = (v : ℝ)) (u v : I) :
    (copulaOfConditional h hi hm hz ho hmean).cdf ![u, v] = ∫ t in Iic u, h v t := by
  simp [copulaOfConditional]

theorem copulaOfConditional_kernel (h : I → I → ℝ)
    (hi : ∀ v, Integrable (h v))
    (hm : ∀ u, Monotone (fun v => h v u))
    (hz : ∀ u, h 0 u = 0) (ho : ∀ u, h 1 u = 1)
    (hmean : ∀ v, (∫ u : I, h v u) = (v : ℝ)) (v : I) :
    (fun u => (copulaOfConditional h hi hm hz ho hmean).conditionalCDF u v) =ᵐ[volume]
      h v := by
  apply Copula.conditionalCDF_ae_eq_of_integral _ v (hi v)
  · intro u
    simpa only [hz] using hm u (show (0 : I) ≤ v from v.property.1)
  · intro u
    exact (copulaOfConditional_cdf h hi hm hz ho hmean u v).symm

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
