import Copula.Rank.Region.XiRho.Paper.SelectedResults
import Copula.Rank.Region.XiRho.Support.DeterministicRho

/-! # The entire vertical boundary in Theorem 1 -/

open ProbabilityTheory Set

namespace ProbabilityTheory.Copula.RankRegion.XiRho

theorem xi_one_slice (r : ℝ) :
    (∃ C : Copula 2, C.chatterjeeXi = 1 ∧ C.spearmanRho = r) ↔ r ∈ Icc (-1) 1 := by
  constructor
  · rintro ⟨C, _, rfl⟩
    exact C.spearmanRho_mem_Icc
  · intro hr
    obtain ⟨C, _, hxi, hrho⟩ := ProbabilityTheory.Copula.RankRegion.XiRho.Support.deterministic_rho_attained r hr
    exact ⟨C, hxi, hrho⟩

theorem symmetric_xi_one_attained (r : ℝ) (hr : r ∈ Icc (-1) 1) :
    ∃ C : Copula 2, C.IsRadiallySymmetric ∧ C.chatterjeeXi = 1 ∧ C.spearmanRho = r :=
  ProbabilityTheory.Copula.RankRegion.XiRho.Support.deterministic_rho_attained r hr

end ProbabilityTheory.Copula.RankRegion.XiRho
