/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Frank
import Copula.Reflection.Bivariate

/-! # Negative-parameter bivariate Frank copulas

The negative branch is defined as the second-coordinate reflection of the
positive branch with opposite parameter. This gives an exact copula and a
closed-square CDF without applying logarithms to grounded zero coordinates.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The negative-parameter bivariate Frank copula. -/
noncomputable def frankNegative (θ : ℝ) (hθ : θ < 0) : Copula 2 :=
  (frank (-θ) (neg_pos.mpr hθ)).reflect {1}

/-- An exact closed-square CDF for the negative Frank branch. It uses the positive
Frank logarithm at the reflected second coordinate, including all boundary cases. -/
theorem frankNegative_cdf_full (θ : ℝ) (hθ : θ < 0) (u v : I) :
    (frankNegative θ hθ).cdf ![u, v] =
      (u : ℝ) - (if u = 0 ∨ unitInterval.symm v = 0 then 0 else
        -Real.log (1 - (1 - Real.exp (θ * (u : ℝ))) *
          (1 - Real.exp (θ * (unitInterval.symm v : ℝ))) /
          (1 - Real.exp θ)) / (-θ)) := by
  rw [frankNegative, cdf_reflect_second, frank_cdf_full]
  simp only [neg_neg]

end ProbabilityTheory.Copula