/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Elliptical.ScaleMixture
import Copula.Distribution.GammaLaplace

/-! # Student-t and Cauchy copulas

For every positive real number `ν` of degrees of freedom, mix a centered Gaussian
vector by `G^(-1/2)`, where the independent precision `G` has gamma shape and rate
`ν/2`. No covariance moments or integrality of `ν` are required. The matrix `R`
is a dispersion/correlation parameter; it is not asserted to be a covariance
matrix of the resulting Student law when its moments do not exist.
-/

open MeasureTheory Filter

namespace ProbabilityTheory

/-- A gamma law bundled as a probability measure. -/
noncomputable def gammaProbability (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    ProbabilityMeasure ℝ := ⟨gammaMeasure a r, isProbabilityMeasure_gammaMeasure ha hr⟩

namespace Copula

variable {d : ℕ}

/-- The standard multivariate Student-t law used for the copula construction. -/
noncomputable def studentTLaw (R : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (hν : 0 < ν) :
    ProbabilityMeasure (Fin d → ℝ) :=
  gaussianScaleMixtureLaw R (gammaProbability (ν / 2) (ν / 2) (by positivity) (by positivity))
    (fun t => (Real.sqrt t)⁻¹)

/-- Student-t copulas, for every positive real number of degrees of freedom. -/
noncomputable def studentT (R : Matrix (Fin d) (Fin d) ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (ν : ℝ) (hν : 0 < ν) : Copula d :=
  gaussianScaleMixture R hR hdiag
    (gammaProbability (ν / 2) (ν / 2) (by positivity) (by positivity))
    (fun t => (Real.sqrt t)⁻¹) (by fun_prop) (by
      filter_upwards [ae_pos_gammaMeasure (ν / 2) (ν / 2)] with t ht
      exact inv_pos.mpr (Real.sqrt_pos.2 ht))

theorem isSklarCopula_studentT (R : Matrix (Fin d) (Fin d) ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (ν : ℝ) (hν : 0 < ν) :
    IsSklarCopula (studentTLaw R ν hν) (studentT R hR hdiag ν hν) :=
  isSklarCopula_gaussianScaleMixture _ _ _ _ _ _ _

/-- The Cauchy copula is the Student-t copula with one degree of freedom. -/
noncomputable def cauchy (R : Matrix (Fin d) (Fin d) ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) : Copula d :=
  studentT R hR hdiag 1 zero_lt_one

@[simp] theorem studentT_one (R : Matrix (Fin d) (Fin d) ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) :
    studentT R hR hdiag 1 zero_lt_one = cauchy R hR hdiag := rfl

end Copula
end ProbabilityTheory
