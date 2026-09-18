/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Mixture
import Copula.Rank.Benchmarks
import Copula.Families.Frechet

/-! # Spearman's rho of Fréchet and Mardia copulas -/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem spearmanRho_frechet (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (frechet a b ha hb hab).spearmanRho = a - b := by
  have hm := spearmanRho_eq_integral_cdf (comonotonic 2)
  have hw := spearmanRho_eq_integral_cdf countermonotonic
  have hp := spearmanRho_eq_integral_cdf (independence 2)
  rw [spearmanRho_comonotonic] at hm
  rw [spearmanRho_countermonotonic] at hw
  rw [spearmanRho_independence] at hp
  rw [spearmanRho_eq_integral_cdf]
  simp_rw [cdf_frechet]
  rw [integral_add, integral_add]
  · simp only [integral_const_mul]
    have hm' : (∫ u, (comonotonic 2).cdf u ∂(independence 2).toMeasure) = 1 / 3 := by linarith
    have hw' : (∫ u, countermonotonic.cdf u ∂(independence 2).toMeasure) = 1 / 6 := by linarith
    have hp' : (∫ u, (independence 2).cdf u ∂(independence 2).toMeasure) = 1 / 4 := by linarith
    rw [hm', hw', hp']
    ring
  all_goals exact integrable_continuous_cube _ (by fun_prop)

theorem spearmanRho_mardia (θ : ℝ) (hθ : |θ| ≤ 1) :
    (mardia θ hθ).spearmanRho = θ ^ 3 := by
  rw [mardia, spearmanRho_frechet]
  ring

end ProbabilityTheory.Copula
