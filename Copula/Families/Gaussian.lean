/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Distribution.ProbabilityIntegralTransform
import Copula.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! # Gaussian copulas

A positive semidefinite correlation matrix defines a Gaussian copula by
applying the standard normal CDF to each coordinate. Singular correlation
matrices are permitted: the diagonal assumption makes each marginal atomless.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {d : ℕ}

theorem continuous_standardNormalCDF : Continuous (ProbabilityTheory.cdf (gaussianReal 0 1)) := by
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  exact continuous_cdf_of_atomless _

/-- The Gaussian copula associated to a correlation matrix. -/
noncomputable def gaussian (R : Matrix (Fin d) (Fin d) ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) : Copula d :=
  ofMap ⟨multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R, inferInstance⟩
    (fun x i => cdfUnit (gaussianReal 0 1) (x i))
    (Measurable.of_eval fun i => (measurable_cdfUnit _).comp (by fun_prop)) (by
      intro i
      have hm : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R).map (fun x => x i) =
          gaussianReal 0 1 := by
        simpa [hdiag, PiLp.zero_apply] using
          (measurePreserving_eval_multivariateGaussian hR (i := i)).map_eq
      calc
        _ = ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R).map (fun x => x i)).map
            (cdfUnit (gaussianReal 0 1)) :=
          (Measure.map_map (measurable_cdfUnit _) (by fun_prop)).symm
        _ = volume := by rw [hm]; exact map_cdfUnit _ continuous_standardNormalCDF)

end ProbabilityTheory.Copula
