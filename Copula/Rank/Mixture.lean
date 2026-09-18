/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.SpearmanCDF
import Copula.Mixture

/-! # Affine dependence coefficients under convex mixtures

Rho, footrule, gamma and beta are affine in the copula. This statement does
not extend to Kendall's tau or Chatterjee's xi.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem spearmanRho_mix (C D : Copula 2) (a : I) :
    (mix C D a).spearmanRho = (a : ℝ) * C.spearmanRho + (1 - (a : ℝ)) * D.spearmanRho := by
  simp_rw [spearmanRho_eq_integral_cdf, cdf_mix]
  rw [integral_add ((C.integrable_cdf _).const_mul _) ((D.integrable_cdf _).const_mul _),
    integral_const_mul, integral_const_mul]
  ring

theorem spearmanFootrule_mix (C D : Copula 2) (a : I) :
    (mix C D a).spearmanFootrule =
      (a : ℝ) * C.spearmanFootrule + (1 - (a : ℝ)) * D.spearmanFootrule := by
  simp_rw [spearmanFootrule, cdf_mix]
  rw [integral_add (C.integrable_diagonal_cdf.const_mul _) (D.integrable_diagonal_cdf.const_mul _),
    integral_const_mul, integral_const_mul]
  ring

theorem giniGamma_mix (C D : Copula 2) (a : I) :
    (mix C D a).giniGamma = (a : ℝ) * C.giniGamma + (1 - (a : ℝ)) * D.giniGamma := by
  simp_rw [giniGamma, cdf_mix]
  rw [integral_add (C.integrable_diagonal_cdf.const_mul _) (D.integrable_diagonal_cdf.const_mul _),
    integral_add (C.integrable_antidiagonal_cdf.const_mul _) (D.integrable_antidiagonal_cdf.const_mul _)]
  simp_rw [integral_const_mul]
  ring

theorem blomqvistBeta_mix (C D : Copula 2) (a : I) :
    (mix C D a).blomqvistBeta = (a : ℝ) * C.blomqvistBeta + (1 - (a : ℝ)) * D.blomqvistBeta := by
  simp only [blomqvistBeta, cdf_mix]
  ring

end ProbabilityTheory.Copula
