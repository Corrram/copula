/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Truncated

/-! # The negative-parameter bivariate Clayton family

This branch is bivariate: negative parameters do not give the same admissible
range in all dimensions. Truncation is performed before taking the power.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem negativeClayton_exponent (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0) :
    1 ≤ (-θ)⁻¹ := by
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (by linarith : 0 < -θ)).mpr
  linarith

/-- Clayton for the full negative bivariate range `−1 ≤ θ < 0`. -/
noncomputable def claytonNegative (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0) : Copula 2 :=
  (truncatedLinearGenerator.innerPower (-θ)⁻¹ (negativeClayton_exponent θ hθ hn)).copula

theorem isArchimedean_claytonNegative (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0) :
    IsArchimedean (claytonNegative θ hθ hn) :=
  (truncatedLinearGenerator.innerPower (-θ)⁻¹ (negativeClayton_exponent θ hθ hn)).isArchimedean

theorem cdf_claytonNegative (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0)
    (u : Fin 2 → I) (hu : ∀ i, u i ≠ 0) :
    (claytonNegative θ hθ hn).cdf u =
      (max 0 ((u 0 : ℝ) ^ (-θ) + (u 1 : ℝ) ^ (-θ) - 1)) ^ (-θ)⁻¹ := by
  rw [claytonNegative, BivariateGenerator.cdf_copula, BivariateGenerator.cdf,
    ite_eq_right (not_or.mpr ⟨hu 0, hu 1⟩)]
  simp only [BivariateGenerator.innerPower, truncatedLinearGenerator, coe_unitPower, inv_inv]
  congr 2
  ring

@[simp] theorem claytonNegative_neg_one :
    claytonNegative (-1) le_rfl (by norm_num) = countermonotonic := by
  simp [claytonNegative]

end ProbabilityTheory.Copula
