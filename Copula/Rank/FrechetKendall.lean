/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.KendallMixture
import Copula.Rank.Frechet

/-! # Classical coefficient formulas for Fréchet and Mardia copulas

Together with `Rank.Frechet` and `Rank.FrechetChatterjee`, these formulas
cover all six supported coefficients on the entire parameter domains.
The tau formulas agree with Table 6 of Ansari and Rockel,
*Dependence properties of bivariate copula families*.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem kendallTau_frechet (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (frechet a b ha hb hab).kendallTau = (a - b) * (a + b + 2) / 3 := by
  rw [frechet, kendallTau_finiteMixture]
  simp [Fin.sum_univ_succ, concordanceQ_comonotonic, concordanceQ_countermonotonic,
    concordanceQ_independence]
  ring

theorem kendallTau_mardia (θ : ℝ) (hθ : |θ| ≤ 1) :
    (mardia θ hθ).kendallTau = θ ^ 3 * (θ ^ 2 + 2) / 3 := by
  rw [mardia, kendallTau_frechet]
  ring

theorem spearmanFootrule_frechet (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (frechet a b ha hb hab).spearmanFootrule = a - b / 2 := by
  have he := concordanceQ_comonotonic (frechet a b ha hb hab)
  have hq : (frechet a b ha hb hab).concordanceQ (comonotonic 2) = (2 * a - b + 1) / 3 := by
    rw [frechet, concordanceQ_finiteMixture_left]
    simp [Fin.sum_univ_succ, concordanceQ_comonotonic]
    ring
  rw [hq] at he
  linarith

theorem giniGamma_frechet (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (frechet a b ha hb hab).giniGamma = a - b := by
  rw [giniGamma_eq_concordanceQ, frechet, concordanceQ_finiteMixture_left,
    concordanceQ_finiteMixture_left]
  simp [Fin.sum_univ_succ, concordanceQ_comonotonic, concordanceQ_countermonotonic]
  ring

theorem blomqvistBeta_frechet (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (frechet a b ha hb hab).blomqvistBeta = a - b := by
  have hm := blomqvistBeta_comonotonic
  have hw := blomqvistBeta_countermonotonic
  have hp := blomqvistBeta_independence
  unfold blomqvistBeta at *
  have hm' : (comonotonic 2).cdf ![unitHalf, unitHalf] = 1 / 2 := by linarith
  have hw' : countermonotonic.cdf ![unitHalf, unitHalf] = 0 := by linarith
  have hp' : (independence 2).cdf ![unitHalf, unitHalf] = 1 / 4 := by linarith
  rw [cdf_frechet, hm', hw', hp']
  ring

theorem spearmanFootrule_mardia (θ : ℝ) (hθ : |θ| ≤ 1) :
    (mardia θ hθ).spearmanFootrule = θ ^ 2 * (1 + 3 * θ) / 4 := by
  rw [mardia, spearmanFootrule_frechet]
  ring

theorem giniGamma_mardia (θ : ℝ) (hθ : |θ| ≤ 1) :
    (mardia θ hθ).giniGamma = θ ^ 3 := by
  rw [mardia, giniGamma_frechet]
  ring

theorem blomqvistBeta_mardia (θ : ℝ) (hθ : |θ| ≤ 1) :
    (mardia θ hθ).blomqvistBeta = θ ^ 3 := by
  rw [mardia, blomqvistBeta_frechet]
  ring

theorem kendallTau_frechet_eq_zero_iff (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (frechet a b ha hb hab).kendallTau = 0 ↔ a = b := by
  rw [kendallTau_frechet]
  have hp : a + b + 2 ≠ 0 := by linarith
  simp [hp, sub_eq_zero]

theorem kendallTau_mardia_eq_zero_iff (θ : ℝ) (hθ : |θ| ≤ 1) :
    (mardia θ hθ).kendallTau = 0 ↔ θ = 0 := by
  rw [kendallTau_mardia]
  have hp : θ ^ 2 + 2 ≠ 0 := by positivity
  simp [hp]

end ProbabilityTheory.Copula
