/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.Common.StochasticRho
import Copula.Rank.Integration
import Copula.Families.NelsenTable.N9

/-! # Spearman's rho of the Gumbel--Barnett family (Nelsen 4.2.9)

For `C(u, v) = u v exp (-θ log u log v)` the inner integral is elementary:
`∫₀¹ u v u^(-θ log v) du = v / (2 - θ log v)`, so
`ρ = 12 ∫₀¹ v / (2 - θ log v) dv - 3`. The remaining integral is an exponential integral
(`∫₀^∞ e^(-2s) / (2 + θ s) ds`), which has no elementary closed form.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace SpearmanNelsen9

/-- The inner integral of the Gumbel--Barnett CDF. -/
theorem integral_cdf_nelsen9 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) (v : I) :
    (∫ u : I, (nelsen9 θ hθ h1).cdf ![u, v]) = (v : ℝ) / (2 - θ * Real.log v) := by
  by_cases hv : v = 0
  · subst hv
    have : ∀ u : I, (nelsen9 θ hθ h1).cdf ![u, 0] = 0 := fun u =>
      (nelsen9 θ hθ h1).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
    simp [this]
  have hvp : 0 < (v : ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
  have hlog : Real.log v ≤ 0 := Real.log_nonpos v.property.1 v.property.2
  have ha : 0 < 1 - θ * Real.log v := by nlinarith
  have hpt : ∀ u : I, (nelsen9 θ hθ h1).cdf ![u, v] = (v : ℝ) * (u : ℝ) ^ (1 - θ * Real.log v) := by
    intro u
    rw [nelsen9_cdf_full]
    by_cases hu : u = 0
    · subst hu
      simp [Real.zero_rpow ha.ne']
    · have hup : 0 < (u : ℝ) :=
        lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))
      simp only [hu, hv, or_self, ↓reduceIte]
      rw [Real.rpow_def_of_pos hup,
        show Real.log u * (1 - θ * Real.log v) = Real.log u + -(θ * Real.log u * Real.log v) by ring,
        Real.exp_add, Real.exp_log hup]
      ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_unitInterval (fun t : ℝ => t ^ (1 - θ * Real.log v)),
    integral_rpow (Or.inl (by linarith)), Real.one_rpow,
    Real.zero_rpow (by linarith : 1 - θ * Real.log v + 1 ≠ 0)]
  rw [show 1 - θ * Real.log v + 1 = 2 - θ * Real.log v by ring]
  ring

end SpearmanNelsen9

/-- Spearman's rho of the Gumbel--Barnett copula (Nelsen 4.2.9, `0 < θ ≤ 1`):
`ρ = 12 ∫₀¹ v / (2 - θ log v) dv - 3`. -/
theorem spearmanRho_nelsen9 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    (nelsen9 θ hθ h1).spearmanRho =
      12 * (∫ v in (0 : ℝ)..1, v / (2 - θ * Real.log v)) - 3 := by
  rw [RankRegion.Common.spearmanRho_eq_iterated_cdf]
  simp_rw [SpearmanNelsen9.integral_cdf_nelsen9]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    ← integral_subtype measurableSet_Icc]

end ProbabilityTheory.Copula
