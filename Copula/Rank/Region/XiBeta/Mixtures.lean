import Copula.Basic
import Copula.Rank.Region.XiBeta.Mixture
import Copula.Rank.ConditionalDerivative
import Copula.Rank.Mixture

/-! # The fixed-beta interpolation step in the proof of Theorem 1

Boundary constructions and the sharp inequality are separate obligations.
This module proves that any two available endpoints with the same beta can
be joined through every intermediate xi value, including singular endpoints.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBeta

theorem xi_derivative_formula (C : Copula 2) :
    C.chatterjeeXi = 6 * (∫ v : I, ∫ u : I, deriv (C.cdfSection v) (u : ℝ) ^ 2) - 2 :=
  C.chatterjeeXi_eq_integral_deriv

theorem xi_mixture_continuous (C D : Copula 2) :
    Continuous (fun a : I => (C.mix D a).chatterjeeXi) :=
  ProbabilityTheory.Copula.RankRegion.XiBeta.continuous_xi_mix C D

theorem beta_mixture_fixed (C D : Copula 2) {b : ℝ}
    (hC : C.blomqvistBeta = b) (hD : D.blomqvistBeta = b) (a : I) :
    (C.mix D a).blomqvistBeta = b := by
  rw [Copula.blomqvistBeta_mix, hC, hD]
  ring

/-- Every xi between two copulas' values is attained at their common beta. -/
theorem fixed_beta_intermediate (C D : Copula 2) {b x : ℝ}
    (hC : C.blomqvistBeta = b) (hD : D.blomqvistBeta = b)
    (hxC : C.chatterjeeXi ≤ x) (hxD : x ≤ D.chatterjeeXi) :
    ∃ E : Copula 2, E.blomqvistBeta = b ∧ E.chatterjeeXi = x := by
  obtain ⟨a, ha⟩ := ProbabilityTheory.Copula.RankRegion.XiBeta.exists_unitInterval_eq
    (xi_mixture_continuous D C) (by simpa using hxC) (by simpa using hxD)
  exact ⟨D.mix C a, beta_mixture_fixed D C hD hC a, ha⟩

end ProbabilityTheory.Copula.RankRegion.XiBeta
