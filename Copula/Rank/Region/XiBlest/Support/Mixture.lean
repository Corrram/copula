import Copula.Rank.ChatterjeeMixture
import Copula.Rank.KendallMixture
import Mathlib.Topology.Order.IntermediateValue

/-! # Continuous coefficient paths along copula mixtures

The quadratic identities make continuity explicit without imposing a density
or continuity assumption on the conditional distributions of a copula.
-/

open ProbabilityTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

theorem continuous_xi_mix (C D : Copula 2) :
    Continuous (fun a : I => (C.mix D a).chatterjeeXi) := by
  simp_rw [Copula.chatterjeeXi_mix]
  fun_prop

theorem continuous_tau_mix (C D : Copula 2) :
    Continuous (fun a : I => (C.mix D a).kendallTau) := by
  simp_rw [Copula.kendallTau_mix]
  fun_prop

/-- A continuous real-valued function on the closed unit interval attains
every value between its endpoint values. -/
theorem exists_unitInterval_eq {f : I → ℝ} (hf : Continuous f) {z : ℝ}
    (hz0 : f 0 ≤ z) (hz1 : z ≤ f 1) : ∃ a : I, f a = z := by
  have h := intermediate_value_Icc (show (0 : I) ≤ 1 from zero_le_one)
    hf.continuousOn ⟨hz0, hz1⟩
  obtain ⟨a, _, ha⟩ := h
  exact ⟨a, ha⟩

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
