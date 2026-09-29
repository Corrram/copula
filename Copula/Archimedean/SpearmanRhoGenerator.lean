/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.Common.StochasticRho
import Copula.Rank.Integration
import Copula.Archimedean.Basic

/-! # Spearman's rho and Blomqvist's beta of an Archimedean copula in terms of its generator

For a bivariate Archimedean generator `g` with inverse generator `ψ = g.toFun` and generator
`φ = g.invFun`, the CDF is `C(u, v) = ψ(φ(u) + φ(v))` on the open square. Hence
* `β = 4 ψ(2 φ(1/2)) - 1` (`BivariateGenerator.blomqvistBeta_copula`), and
* `ρ = 12 ∫₀¹ ∫₀¹ C(u, v) du dv - 3` with `C = g.cdf` (`BivariateGenerator.spearmanRho_copula`),
  i.e. `ρ = 12 ∫∫ ψ(φ(u) + φ(v)) du dv - 3`.

For the individual table families the double integral collapses to a series, a one-dimensional
integral or a closed form in `Copula.Archimedean.SpearmanRhoAMH`, `SpearmanRhoNelsen9` and
`SpearmanRhoNelsen2`; for most families (Clayton, Gumbel, Joe, ...) it has no elementary
evaluation and this generic double-integral form is the statement.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace BivariateGenerator

/-- Blomqvist's beta of an Archimedean copula: `β = 4 ψ(2 φ(1/2)) - 1`. -/
theorem blomqvistBeta_copula (g : BivariateGenerator) :
    g.copula.blomqvistBeta = 4 * g.toFun (2 * g.invFun unitHalf) - 1 := by
  have hne : (unitHalf : I) ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    change (1 / 2 : ℝ) = 0 at this
    norm_num at this
  rw [Copula.blomqvistBeta, cdf_copula]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, cdf, or_self, hne, ↓reduceIte]
  rw [two_mul]

/-- Spearman's rho of an Archimedean copula as a double integral of `ψ(φ(u) + φ(v))`. -/
theorem spearmanRho_copula (g : BivariateGenerator) :
    g.copula.spearmanRho = 12 * (∫ v : I, ∫ u : I, g.cdf u v) - 3 := by
  rw [RankRegion.Common.spearmanRho_eq_iterated_cdf]
  simp only [cdf_copula, Matrix.cons_val_zero, Matrix.cons_val_one]

end BivariateGenerator

end ProbabilityTheory.Copula
