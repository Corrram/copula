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

private theorem frank_alg (e a b : ℝ) (he : e ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hp : 1 - e ≠ 0) :
    1 + ((a⁻¹ - 1) * (b⁻¹ - 1)) / (e⁻¹ - 1) =
      a⁻¹ * (1 - (1 - a) * (1 - e * b⁻¹) / (1 - e)) := by
  field_simp
  ring

private theorem frank_log_identity (θ x y : ℝ) (hθ : θ < 0)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x + Real.log (1 - (1 - Real.exp (θ * x)) *
      (1 - Real.exp (θ * (1 - y))) / (1 - Real.exp θ)) / (-θ) =
      -Real.log (1 + (Real.exp (-θ * x) - 1) *
        (Real.exp (-θ * y) - 1) / (Real.exp (-θ) - 1)) / θ := by
  have hθ0 : θ ≠ 0 := ne_of_lt hθ
  have he : Real.exp θ ≠ 0 := (Real.exp_pos θ).ne'
  have ha : Real.exp (θ * x) ≠ 0 := (Real.exp_pos (θ * x)).ne'
  have hb : Real.exp (θ * y) ≠ 0 := (Real.exp_pos (θ * y)).ne'
  have hp : 1 - Real.exp θ ≠ 0 := by
    have h := Real.exp_lt_one_iff.mpr hθ
    linarith
  have hux : Real.exp (-θ * x) = (Real.exp (θ * x))⁻¹ := by
    rw [show -θ * x = -(θ * x) by ring, Real.exp_neg]
  have huy : Real.exp (-θ * y) = (Real.exp (θ * y))⁻¹ := by
    rw [show -θ * y = -(θ * y) by ring, Real.exp_neg]
  have heinv : Real.exp (-θ) = (Real.exp θ)⁻¹ := Real.exp_neg θ
  have hevy : Real.exp (θ * (1 - y)) =
      Real.exp θ * (Real.exp (θ * y))⁻¹ := by
    rw [show θ * (1 - y) = θ + -(θ * y) by ring,
      Real.exp_add, Real.exp_neg]
  let A := 1 - (1 - Real.exp (θ * x)) *
      (1 - Real.exp (θ * (1 - y))) / (1 - Real.exp θ)
  let B := 1 + (Real.exp (-θ * x) - 1) *
      (Real.exp (-θ * y) - 1) / (Real.exp (-θ) - 1)
  have hAB : B = Real.exp (-θ * x) * A := by
    dsimp [A, B]
    rw [hux, huy, heinv, hevy]
    exact frank_alg _ _ _ he ha hb hp
  have hxexp : 1 ≤ Real.exp (-θ * x) := by
    apply Real.one_le_exp_iff.mpr
    exact mul_nonneg (le_of_lt (neg_pos.mpr hθ)) hx
  have hyexp : 1 ≤ Real.exp (-θ * y) := by
    apply Real.one_le_exp_iff.mpr
    exact mul_nonneg (le_of_lt (neg_pos.mpr hθ)) hy
  have hpexp : 0 < Real.exp (-θ) - 1 := by
    have h := Real.exp_lt_exp.mpr (neg_pos.mpr hθ)
    simpa using h
  have hB : 0 < B := by
    dsimp [B]
    have hprod : 0 ≤ (Real.exp (-θ * x) - 1) *
        (Real.exp (-θ * y) - 1) := mul_nonneg (by linarith) (by linarith)
    have hdiv := div_nonneg hprod hpexp.le
    linarith
  have hA : A ≠ 0 := by
    intro hz
    rw [hAB, hz, mul_zero] at hB
    exact (lt_irrefl 0) hB
  have hlog : Real.log B = -θ * x + Real.log A := by
    rw [hAB, Real.log_mul (Real.exp_pos _).ne' hA, Real.log_exp]
  rw [show 1 - (1 - Real.exp (θ * x)) *
      (1 - Real.exp (θ * (1 - y))) / (1 - Real.exp θ) = A by rfl,
    show 1 + (Real.exp (-θ * x) - 1) *
      (Real.exp (-θ * y) - 1) / (Real.exp (-θ) - 1) = B by rfl,
    hlog]
  field_simp
  ring
open scoped unitInterval
open ProbabilityTheory.Copula

/-- Table 1's Frank logarithmic CDF for every negative parameter, with all boundary values. -/
theorem frankNegative_cdf_source (θ : ℝ) (hθ : θ < 0) (u v : I) :
    (frankNegative θ hθ).cdf ![u, v] =
      -Real.log (1 + (Real.exp (-θ * (u : ℝ)) - 1) *
        (Real.exp (-θ * (v : ℝ)) - 1) / (Real.exp (-θ) - 1)) / θ := by
  rw [frankNegative_cdf_full]
  simp only [unitInterval.coe_symm_eq]
  have hlog := frank_log_identity θ (u : ℝ) (v : ℝ) hθ u.property.1 v.property.1
  by_cases hz : u = 0 ∨ unitInterval.symm v = 0
  · have hA : Real.log (1 - (1 - Real.exp (θ * (u : ℝ))) *
        (1 - Real.exp (θ * (1 - (v : ℝ)))) / (1 - Real.exp θ)) = 0 := by
      rcases hz with hu | hv
      · subst u
        simp
      · have hcv : 1 - (v : ℝ) = 0 := by
          have h := congrArg (fun x : I => (x : ℝ)) hv
          simpa [unitInterval.coe_symm_eq] using h
        simp [hcv]
    simpa [hz, hA] using hlog
  · simp only [ite_eq_right hz]
    convert hlog using 1; ring
end ProbabilityTheory.Copula