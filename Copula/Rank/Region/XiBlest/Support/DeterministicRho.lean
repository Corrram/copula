import Copula.Rank.Region.XiBlest.Support.CenteredProperties
import Copula.Rank.Region.XiBlest.Support.Mixture

/-! # Every rho is attained at xi=1 by a radially symmetric copula -/

open ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

theorem centralW_rho (α : I) : (centralW α).spearmanRho = 1 - 2 * (α : ℝ) ^ 3 := by
  rw [centralW, centeredOrdinal_rho, Copula.spearmanRho_countermonotonic]
  ring

theorem deterministic_rho_attained (r : ℝ) (hr : r ∈ Icc (-1) 1) :
    ∃ C : Copula 2, C.IsRadiallySymmetric ∧ C.chatterjeeXi = 1 ∧ C.spearmanRho = r := by
  have hc : Continuous (fun a : I => -(centralW a).spearmanRho) := by
    simp_rw [centralW_rho]
    fun_prop
  obtain ⟨a, ha⟩ := exists_unitInterval_eq (z := -r) hc
    (by rw [centralW_rho]; norm_num; linarith [hr.2])
    (by rw [centralW_rho]; norm_num; linarith [hr.1])
  exact ⟨centralW a, centralW_radiallySymmetric a, centralW_xi a, by linarith⟩

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
