/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.StudentT
import Mathlib.Probability.Distributions.Exponential

/-! # Further elliptical Gaussian scale mixture families

These are stochastic constructions with proved uniform marginals. They do not
claim elementary copula CDF or density formulas. All use an independent common
scale, so an identity dispersion matrix does not generally imply independence.
-/

open MeasureTheory Filter

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- Symmetric variance-gamma copula: gamma variance with shape and rate `κ`. -/
noncomputable def varianceGamma (R : Matrix (Fin d) (Fin d) ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (κ : ℝ) (hκ : 0 < κ) : Copula d :=
  gaussianScaleMixture R hR hdiag (gammaProbability κ κ hκ hκ) Real.sqrt
    (by fun_prop) (by
      filter_upwards [ae_pos_gammaMeasure κ κ] with t ht
      exact Real.sqrt_pos.2 ht)

/-- Symmetric multivariate Laplace copula, with an exponential common variance. -/
noncomputable def laplace (R : Matrix (Fin d) (Fin d) ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) : Copula d :=
  varianceGamma R hR hdiag 1 zero_lt_one

@[simp] theorem varianceGamma_one (R : Matrix (Fin d) (Fin d) ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) :
    varianceGamma R hR hdiag 1 zero_lt_one = laplace R hR hdiag := rfl

/-- Generalized slash copula: the common scale is `exp(E/q)` for `E ~ Exp(1)`.
Equivalently the scale is `U^(-1/q)` for a uniform `U`; `q = 1` is the usual slash law. -/
noncomputable def slash (R : Matrix (Fin d) (Fin d) ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (q : ℝ) (_hq : 0 < q) : Copula d :=
  gaussianScaleMixture R hR hdiag
    ⟨expMeasure 1, isProbabilityMeasure_expMeasure zero_lt_one⟩
    (fun t => Real.exp (t / q)) (by fun_prop)
    (Filter.Eventually.of_forall fun _ => Real.exp_pos _)

/-- Lognormal-scale Gaussian copulas. `τ` is the standard deviation of the log scale. -/
noncomputable def normalLognormal (R : Matrix (Fin d) (Fin d) ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (τ : NNReal) : Copula d :=
  gaussianScaleMixture R hR hdiag ⟨gaussianReal 0 (τ ^ 2), inferInstance⟩
    Real.exp (by fun_prop) (Filter.Eventually.of_forall fun _ => Real.exp_pos _)

end ProbabilityTheory.Copula
