/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Integration

/-! # Population rank coefficients of bivariate copulas

These are population functionals, not finite-sample rank estimators.
Spearman's footrule uses the convention with range `[-1/2,1]`.
The conditional-distribution coefficient of Chatterjee is in `Rank.Chatterjee`.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Spearman's rho: the Pearson correlation of the two uniform coordinates. -/
noncomputable def spearmanRho (C : Copula 2) : ℝ :=
  12 * (∫ x, (x 0 : ℝ) * (x 1 : ℝ) ∂C.toMeasure) - 3

/-- Kendall's tau, expressed as the self-concordance integral. -/
noncomputable def kendallTau (C : Copula 2) : ℝ := 4 * (∫ x, C.cdf x ∂C.toMeasure) - 1

/-- Spearman's population footrule coefficient, normalized to `[-1/2,1]`. -/
noncomputable def spearmanFootrule (C : Copula 2) : ℝ :=
  6 * (∫ t : I, C.cdf ![t, t]) - 2

/-- Gini's gamma, using the diagonal and antidiagonal sections of the copula. -/
noncomputable def giniGamma (C : Copula 2) : ℝ :=
  4 * ((∫ t : I, C.cdf ![t, t]) + (∫ t : I, C.cdf ![t, unitInterval.symm t])) - 2

/-- The midpoint of the closed unit interval. -/
noncomputable def unitHalf : I := ⟨1 / 2, by norm_num, by norm_num⟩

/-- Blomqvist's beta, the population median concordance coefficient. -/
noncomputable def blomqvistBeta (C : Copula 2) : ℝ := 4 * C.cdf ![unitHalf, unitHalf] - 1

theorem integrable_diagonal_cdf (C : Copula 2) : Integrable (fun t : I => C.cdf ![t, t]) :=
  integrable_continuous_unit volume (C.continuous_cdf.comp (by fun_prop))

theorem integrable_antidiagonal_cdf (C : Copula 2) :
    Integrable (fun t : I => C.cdf ![t, unitInterval.symm t]) :=
  integrable_continuous_unit volume (C.continuous_cdf.comp (by fun_prop))

theorem blomqvistBeta_mem_Icc (C : Copula 2) : blomqvistBeta C ∈ Set.Icc (-1) 1 := by
  have hn := C.cdf_nonneg ![unitHalf, unitHalf]
  have hu := C.cdf_le_coord ![unitHalf, unitHalf] 0
  change C.cdf ![unitHalf, unitHalf] ≤ 1 / 2 at hu
  constructor <;> unfold blomqvistBeta <;> linarith

theorem kendallTau_mem_Icc (C : Copula 2) : kendallTau C ∈ Set.Icc (-1) 1 := by
  have hn : 0 ≤ ∫ x, C.cdf x ∂C.toMeasure := integral_nonneg C.cdf_nonneg
  have hu := integral_mono (C.integrable_cdf C.toMeasure)
    (integrable_continuous_cube C.toMeasure (show Continuous (fun x : Fin 2 → I => (x 0 : ℝ)) by
      fun_prop)) (fun x => C.cdf_le_coord x 0)
  rw [C.integral_coe_eval] at hu
  constructor <;> unfold kendallTau <;> linarith

theorem blomqvistBeta_mono {C D : Copula 2} (h : ∀ u, C.cdf u ≤ D.cdf u) :
    C.blomqvistBeta ≤ D.blomqvistBeta := by
  unfold blomqvistBeta
  linarith [h ![unitHalf, unitHalf]]

theorem spearmanFootrule_mono {C D : Copula 2} (h : ∀ u, C.cdf u ≤ D.cdf u) :
    C.spearmanFootrule ≤ D.spearmanFootrule := by
  have hi := integral_mono C.integrable_diagonal_cdf D.integrable_diagonal_cdf
    (fun t => h ![t, t])
  unfold spearmanFootrule
  linarith

theorem giniGamma_mono {C D : Copula 2} (h : ∀ u, C.cdf u ≤ D.cdf u) :
    C.giniGamma ≤ D.giniGamma := by
  have hd := integral_mono C.integrable_diagonal_cdf D.integrable_diagonal_cdf
    (fun t => h ![t, t])
  have ha := integral_mono C.integrable_antidiagonal_cdf D.integrable_antidiagonal_cdf
    (fun t => h ![t, unitInterval.symm t])
  unfold giniGamma
  linarith

end ProbabilityTheory.Copula
