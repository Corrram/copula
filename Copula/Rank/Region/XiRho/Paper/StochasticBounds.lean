import Copula.Rank.Region.XiRho.Paper.Definitions
import Copula.Rank.Region.XiRho.Support.StochasticRho

/-! # The general SI/SD inequality and the conditional representation of rho

These results apply to all bivariate copulas, including singular laws.
The full equality classification in Theorem 2 is proved in `StochasticEquality.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiRho

theorem rho_conditionalCDF_formula (C : Copula 2) :
    C.spearmanRho =
      12 * (∫ v : I, ∫ u : I, (1 - (u : ℝ)) * C.conditionalCDF u v) - 3 := by
  rw [ProbabilityTheory.Copula.RankRegion.XiRho.Support.spearmanRho_eq_iterated_cdf]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with v
  simp_rw [C.cdf_eq_integral_conditionalCDF]
  exact ProbabilityTheory.Copula.RankRegion.XiRho.Support.integral_lower_integral (C.measurable_conditionalCDF_left v)
    (fun u => ⟨C.conditionalCDF_nonneg u v, C.conditionalCDF_le_one u v⟩)

theorem rho_derivative_formula (C : Copula 2) :
    C.spearmanRho =
      12 * (∫ v : I, ∫ u : I, (1 - (u : ℝ)) * deriv (C.cdfSection v) (u : ℝ)) - 3 := by
  rw [rho_conditionalCDF_formula]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with v
  apply integral_congr_ae
  filter_upwards [C.conditionalCDF_eq_deriv v] with u hu
  rw [hu]

theorem si_xi_le_rho (C : Copula 2) (hC : C.IsSI) : C.chatterjeeXi ≤ C.spearmanRho :=
  ProbabilityTheory.Copula.RankRegion.XiRho.Support.xi_le_rho_of_isSI C hC

theorem sd_xi_le_neg_rho (C : Copula 2) (hC : C.IsSD) : C.chatterjeeXi ≤ -C.spearmanRho :=
  ProbabilityTheory.Copula.RankRegion.XiRho.Support.xi_le_neg_rho_of_isSD C hC

theorem stochastic_xi_le_abs_rho (C : Copula 2) (hC : C.IsSI ∨ C.IsSD) :
    C.chatterjeeXi ≤ |C.spearmanRho| :=
  ProbabilityTheory.Copula.RankRegion.XiRho.Support.xi_le_abs_rho_of_stochastically_monotone C hC

theorem not_stochastically_monotone_of_abs_rho_lt_xi (C : Copula 2)
    (h : |C.spearmanRho| < C.chatterjeeXi) : ¬C.IsSI ∧ ¬C.IsSD := by
  constructor
  · intro hC
    exact (not_le_of_gt h) (stochastic_xi_le_abs_rho C (Or.inl hC))
  · intro hC
    exact (not_le_of_gt h) (stochastic_xi_le_abs_rho C (Or.inr hC))

end ProbabilityTheory.Copula.RankRegion.XiRho
