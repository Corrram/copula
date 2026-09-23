import Copula.Rank.Region.XiRho.Paper.Definitions
import Copula.Rank.FGMChatterjee
import Copula.Rank.ConditionalDerivative
import Copula.Rank.ConditionalDistance
import Copula.Rank.Extrema
import Copula.Dependence.ConditionalMonotonicity

/-! # Endpoint cases and a restricted instance of Theorem 2

The general SI/SD inequality is proved in `StochasticBounds.lean`.
The full equality classification is proved in `StochasticEquality.lean`.
The curved diagonal-band boundary remains pending.
The FGM result below has the explicit restriction `abs θ ≤ 1` and is not
advertised as the general stochastic-monotonicity theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiRho

theorem xi_derivative_formula (C : Copula 2) :
    C.chatterjeeXi = 6 * (∫ v : I, ∫ u : I, (deriv (C.cdfSection v) u) ^ 2) - 2 :=
  C.chatterjeeXi_eq_integral_deriv

/-- The xi=0 slice in Theorem 1 consists of the independence copula alone. -/
theorem xi_zero_slice (C : Copula 2) :
    C.chatterjeeXi = 0 ↔ C = Copula.independence 2 ∧ C.spearmanRho = 0 := by
  constructor
  · intro h
    have he := C.chatterjeeXi_eq_zero_iff.mp h
    exact ⟨he, by simp [he]⟩
  · rintro ⟨rfl, _⟩
    simp

theorem rho_extreme_implies_xi_one (C : Copula 2)
    (h : C.spearmanRho = 1 ∨ C.spearmanRho = -1) : C.chatterjeeXi = 1 := by
  rcases h with h | h
  · rw [C.spearmanRho_eq_one_iff.mp h]
    simp
  · rw [C.spearmanRho_eq_neg_one_iff.mp h]
    simp

/-- Every admissible FGM copula is conditionally increasing or decreasing. -/
theorem fgm_stochastically_monotone (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.fgm θ hθ).IsCI ∨ (Copula.fgm θ hθ).IsCD := by
  rcases le_total 0 θ with h | h
  · exact Or.inl ((Copula.isCI_fgm_iff θ hθ).mpr h)
  · exact Or.inr ((Copula.isCD_fgm_iff θ hθ).mpr h)

/-- Theorem 2 restricted to the entire signed FGM family. -/
theorem fgm_xi_le_abs_rho (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.fgm θ hθ).chatterjeeXi ≤ |(Copula.fgm θ hθ).spearmanRho| := by
  rw [Copula.chatterjeeXi_fgm, Copula.spearmanRho_fgm, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hsq : |θ| ^ 2 ≤ |θ| := by nlinarith [abs_nonneg θ]
  nlinarith [sq_abs θ, abs_nonneg θ]

/-- In the restricted FGM result, equality occurs only at independence. -/
theorem fgm_xi_eq_abs_rho_iff (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.fgm θ hθ).chatterjeeXi = |(Copula.fgm θ hθ).spearmanRho| ↔ θ = 0 := by
  rw [Copula.chatterjeeXi_fgm, Copula.spearmanRho_fgm, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  constructor
  · intro he
    have hsq : |θ| ^ 2 ≤ |θ| := by nlinarith [abs_nonneg θ]
    have hz : |θ| = 0 := by nlinarith [sq_abs θ, abs_nonneg θ]
    exact abs_eq_zero.mp hz
  · rintro rfl
    norm_num

end ProbabilityTheory.Copula.RankRegion.XiRho
