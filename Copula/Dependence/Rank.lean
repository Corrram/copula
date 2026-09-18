/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.Basic
import Copula.Rank.SpearmanCDF
import Copula.Rank.Benchmarks

/-! # Quadrant dependence and the signs of rank coefficients -/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem isPQD_iff_independence_le (C : Copula 2) :
    C.IsPQD ↔ ∀ u, (independence 2).cdf u ≤ C.cdf u := by
  constructor
  · intro h u
    have he : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
    simpa [cdf_independence, Fin.prod_univ_two, he] using h (u 0) (u 1)
  · intro h u v
    simpa [cdf_independence, Fin.prod_univ_two] using h ![u, v]

theorem IsPQD.spearmanRho_nonneg {C : Copula 2} (h : C.IsPQD) : 0 ≤ C.spearmanRho := by
  simpa using spearmanRho_mono ((isPQD_iff_independence_le C).mp h)

theorem IsPQD.spearmanFootrule_nonneg {C : Copula 2} (h : C.IsPQD) : 0 ≤ C.spearmanFootrule := by
  simpa using spearmanFootrule_mono ((isPQD_iff_independence_le C).mp h)

theorem IsPQD.giniGamma_nonneg {C : Copula 2} (h : C.IsPQD) : 0 ≤ C.giniGamma := by
  simpa using giniGamma_mono ((isPQD_iff_independence_le C).mp h)

theorem IsPQD.blomqvistBeta_nonneg {C : Copula 2} (h : C.IsPQD) : 0 ≤ C.blomqvistBeta := by
  simpa using blomqvistBeta_mono ((isPQD_iff_independence_le C).mp h)

/-- The PQD bound `rho ≤ 3 tau`, obtained by integrating `uv ≤ C(u,v)` against `dC`. -/
theorem IsPQD.spearmanRho_le_three_mul_kendallTau {C : Copula 2} (h : C.IsPQD) :
    C.spearmanRho ≤ 3 * C.kendallTau := by
  have hi := integral_mono
    (integrable_continuous_cube C.toMeasure (show Continuous (fun x : Fin 2 → I =>
      (x 0 : ℝ) * (x 1 : ℝ)) by fun_prop)) (C.integrable_cdf C.toMeasure)
    (fun x => by simpa only [cdf_independence, Fin.prod_univ_two] using
      (isPQD_iff_independence_le C).mp h x)
  unfold spearmanRho kendallTau
  linarith

theorem IsPQD.kendallTau_nonneg {C : Copula 2} (h : C.IsPQD) : 0 ≤ C.kendallTau := by
  linarith [h.spearmanRho_nonneg, h.spearmanRho_le_three_mul_kendallTau]

end ProbabilityTheory.Copula
