import Copula.Rank.Region.XiBlest.Support.NormalizedConditionalCDF
import Copula.Rank.Chatterjee

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

theorem normalizedCDF_affine_energy (C : Copula 2) (a b : ℝ) :
    (∫ v : I, ∫ u : I, (a+b*normalizedCDF C u v)^2) = a^2+a*b+b^2*(C.chatterjeeXi+2)/6 := by
  have he (v : I) : (∫ u : I, (a+b*normalizedCDF C u v)^2) =
      a^2+2*a*b*(v : ℝ)+b^2*(∫ u : I, C.conditionalCDF u v^2) := by
    have hae : (fun u => (a+b*normalizedCDF C u v)^2) =ᵐ[volume] fun u => (a+b*C.conditionalCDF u v)^2 := by
      filter_upwards [normalizedCDF_ae C v] with u hu
      rw [hu]
    rw [integral_congr_ae hae]
    have hp (u : I) : (a+b*C.conditionalCDF u v)^2 =
        a^2+(2*a*b)*C.conditionalCDF u v+b^2*C.conditionalCDF u v^2 := by ring
    simp_rw [hp]
    rw [integral_add (f := fun u : I => a^2+(2*a*b)*C.conditionalCDF u v) ((integrable_const (a^2)).add ((C.integrable_conditionalCDF v).const_mul (2*a*b)))
      ((C.integrable_conditionalCDF_sq v).const_mul (b^2)),
      integral_add (integrable_const (a^2)) ((C.integrable_conditionalCDF v).const_mul (2*a*b))]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,integral_const_mul,C.integral_conditionalCDF]
  simp_rw [he]
  have ha : Integrable (fun _ : I => a^2) := integrable_const _
  have hb : Integrable (fun v : I => (2*a*b)*(v : ℝ)) :=
    (Copula.integrable_continuous_unit volume continuous_subtype_val).const_mul _
  rw [integral_add (f := fun v : I => a^2+(2*a*b)*(v : ℝ)) (ha.add hb) (C.integrable_integral_conditionalCDF_sq.const_mul (b^2)),integral_add ha hb]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,integral_const_mul,Copula.integral_unit_id,
    Copula.chatterjeeXi]
  ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
