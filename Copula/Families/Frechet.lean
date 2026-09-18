/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Mixture
import Copula.Countermonotonic

/-! # Fréchet and Mardia mixture families -/

open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The bivariate Fréchet family: weights `a`, `b`, and `1-a-b` on `M`, `W`, and `Π`. -/
noncomputable def frechet (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) : Copula 2 :=
  finiteMixture ![comonotonic 2, countermonotonic, independence 2] ![a, b, 1 - a - b]
    (by intro i; fin_cases i <;> simp <;> linarith)
    (by simp [Fin.sum_univ_succ])

theorem cdf_frechet (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)
    (u : Fin 2 → I) :
    (frechet a b ha hb hab).cdf u = a * (comonotonic 2).cdf u +
      b * countermonotonic.cdf u + (1 - a - b) * (independence 2).cdf u := by
  simp [frechet, Fin.sum_univ_succ]
  ring

/-- Mardia's one-parameter family, for `θ ∈ [-1,1]`. -/
noncomputable def mardia (θ : ℝ) (hθ : |θ| ≤ 1) : Copula 2 :=
  frechet (θ ^ 2 * (1 + θ) / 2) (θ ^ 2 * (1 - θ) / 2)
    (div_nonneg (mul_nonneg (sq_nonneg θ) (by linarith [(abs_le.mp hθ).1])) (by norm_num))
    (div_nonneg (mul_nonneg (sq_nonneg θ) (by linarith [(abs_le.mp hθ).2])) (by norm_num))
    (by have := (abs_le.mp hθ).1; have := (abs_le.mp hθ).2; nlinarith [sq_nonneg θ])

@[simp] theorem mardia_zero : mardia 0 (by norm_num) = independence 2 := by
  apply ext_cdf; intro u
  simp [mardia, cdf_frechet]

@[simp] theorem mardia_one : mardia 1 (by norm_num) = comonotonic 2 := by
  apply ext_cdf; intro u
  simp [mardia, cdf_frechet]

@[simp] theorem mardia_neg_one : mardia (-1) (by norm_num) = countermonotonic := by
  apply ext_cdf; intro u
  norm_num [mardia, cdf_frechet]

end ProbabilityTheory.Copula
