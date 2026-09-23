/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.ClaytonNegative

/-! # Exact signed conditional-monotonicity classification for Clayton copulas

The strict midpoint comparison with independence excludes the opposite
conditional monotonicity for each nonzero parameter branch.
-/

open Real
open scoped unitInterval

namespace ProbabilityTheory.Copula

private noncomputable def midI : I := ⟨1 / 2, by constructor <;> norm_num⟩

private theorem positive_clayton_mid_strict (θ : ℝ) (hθ : 0 < θ) :
    (midI : ℝ) * (midI : ℝ) < (clayton 2 θ hθ).cdf ![midI, midI] := by
  have hh : 0 < (midI : ℝ) := by norm_num [midI]
  have hh1 : (midI : ℝ) < 1 := by norm_num [midI]
  let x := (midI : ℝ) ^ (-θ)
  have hx : 1 < x := by
    have h := Real.rpow_lt_rpow_of_exponent_gt hh hh1 (show -θ < 0 by linarith)
    simpa [x] using h
  have hb : 0 < x + x - 1 := by linarith
  have hxy : x + x - 1 < x * x := by
    nlinarith [mul_pos (show 0 < x - 1 by linarith) (show 0 < x - 1 by linarith)]
  have hq : -1 / θ < 0 := div_neg_of_neg_of_pos (by norm_num) hθ
  have hlt : (x * x) ^ (-1 / θ) < (x + x - 1) ^ (-1 / θ) :=
    Real.rpow_lt_rpow_of_neg hb hxy hq
  have hpow : ((midI : ℝ) ^ (-θ)) ^ (-1 / θ) = (midI : ℝ) := by
    rw [← Real.rpow_mul hh.le]
    have he : (-θ) * (-1 / θ) = 1 := by field_simp
    rw [he, Real.rpow_one]
  have hmult : (x * x) ^ (-1 / θ) = (midI : ℝ) * (midI : ℝ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hh.le _) (Real.rpow_nonneg hh.le _)]
    exact congrArg₂ (· * ·) hpow hpow
  rw [hmult] at hlt
  rw [cdf_clayton_two_pos θ hθ midI midI hh hh]
  simpa [x, add_sub_assoc] using hlt

/-- Positive Clayton parameters are never conditionally decreasing. -/
theorem not_isCD_clayton_positive (θ : ℝ) (hθ : 0 < θ) :
    ¬(clayton 2 θ hθ).IsCD := by
  intro hCD
  exact (not_le_of_gt (positive_clayton_mid_strict θ hθ)) (hCD.isNQD midI midI)
private theorem negative_clayton_mid_strict (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0) :
    (claytonNegative θ hθ hn).cdf ![midI, midI] < (midI : ℝ) * (midI : ℝ) := by
  have hh : 0 < (midI : ℝ) := by norm_num [midI]
  have hh1 : (midI : ℝ) < 1 := by norm_num [midI]
  have hp : 0 < -θ := by linarith
  let x := (midI : ℝ) ^ (-θ)
  have hx0 : 0 < x := Real.rpow_pos_of_pos hh _
  have hx1 : x < 1 := by
    have h := Real.rpow_lt_rpow hh.le hh1 hp
    simpa [x] using h
  have hxy : x + x - 1 < x * x := by
    nlinarith [mul_pos (show 0 < 1 - x by linarith) (show 0 < 1 - x by linarith)]
  have hb : max 0 (x + x - 1) < x * x :=
    max_lt (mul_pos hx0 hx0) hxy
  have hq : 0 < (-θ)⁻¹ := inv_pos.mpr hp
  have hlt : (max 0 (x + x - 1)) ^ (-θ)⁻¹ < (x * x) ^ (-θ)⁻¹ :=
    Real.rpow_lt_rpow (by positivity) hb hq
  have hpow : ((midI : ℝ) ^ (-θ)) ^ (-θ)⁻¹ = (midI : ℝ) := by
    rw [← Real.rpow_mul hh.le]
    rw [mul_inv_cancel₀ hp.ne', Real.rpow_one]
  have hmult : (x * x) ^ (-θ)⁻¹ = (midI : ℝ) * (midI : ℝ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hh.le _) (Real.rpow_nonneg hh.le _)]
    exact congrArg₂ (· * ·) hpow hpow
  rw [hmult] at hlt
  have hh0 : midI ≠ 0 := by
    intro he
    have : (midI : ℝ) = 0 := congrArg Subtype.val he
    linarith
  rw [cdf_claytonNegative θ hθ hn ![midI, midI] (by
    intro i
    fin_cases i <;> simpa using hh0)]
  simpa [x, add_sub_assoc] using hlt

/-- Negative Clayton parameters are never conditionally increasing. -/
theorem not_isCI_clayton_negative (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0) :
    ¬(claytonNegative θ hθ hn).IsCI := by
  intro hCI
  exact (not_le_of_gt (negative_clayton_mid_strict θ hθ hn)) (hCI.isPQD midI midI)
end ProbabilityTheory.Copula
