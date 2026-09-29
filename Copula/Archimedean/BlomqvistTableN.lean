/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.BlomqvistTable
import Copula.Families.NelsenTable.N9
import Copula.Families.NelsenTable.N10
import Copula.Families.NelsenTable.N11
import Copula.Families.NelsenTable.N13
import Copula.Families.NelsenTable.N16
import Copula.Families.NelsenTable.N17
import Copula.Families.NelsenTable.N18
import Copula.Families.NelsenTable.N19
import Copula.Families.NelsenTable.N20
import Copula.Families.NelsenTable.N21
import Copula.Families.NelsenTable.N22

/-! # Blomqvist's beta of Nelsen's Table 4.1, families 9 to 22

Continuation of `Copula.Archimedean.BlomqvistTable`: `β = 4 C(1/2, 1/2) - 1` for the families
4.2.9, 10, 11, 13, 16, 17, 18, 19, 20, 21, 22 of Nelsen, *An Introduction to Copulas*, second
edition, Table 4.1 (families 12, 14, 15 are in the first file). In every case the value is
elementary.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

open BlomqvistTable

/-- Nelsen 9 (`0 < θ ≤ 1`): `β = exp (-θ (log 2)^2) - 1`. -/
theorem blomqvistBeta_nelsen9 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    (nelsen9 θ hθ h1).blomqvistBeta = Real.exp (-(θ * Real.log 2 ^ 2)) - 1 := by
  rw [blomqvistBeta, nelsen9_cdf_full]
  simp only [or_self, half_ne_zero, ↓reduceIte, half_val]
  rw [one_div, Real.log_inv]
  ring_nf

/-- Nelsen 10 (`0 < θ ≤ 1`): `β = (1 + (1 - 2^(-θ))^2)^(-1/θ) - 1`. -/
theorem blomqvistBeta_nelsen10 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    (nelsen10 θ hθ h1).blomqvistBeta =
      ((1 + (1 - ((2 : ℝ) ^ θ)⁻¹) ^ 2) ^ θ⁻¹)⁻¹ - 1 := by
  rw [blomqvistBeta, nelsen10_cdf_full]
  simp only [or_self, half_ne_zero, ↓reduceIte, half_val, half_rpow]
  have : 0 < (1 + (1 - ((2 : ℝ) ^ θ)⁻¹) ^ 2) ^ θ⁻¹ := by positivity
  field_simp
  ring


/-- Nelsen 11 (`0 < θ ≤ 1/2`): with `a = 2^(-θ)`, `β = 4 (4a - a^2 - 2)^(1/θ) - 1`. -/
theorem blomqvistBeta_nelsen11 (θ : ℝ) (hθ : 0 < θ) (h2 : θ ≤ 1 / 2) :
    (nelsen11 θ hθ h2).blomqvistBeta =
      4 * (4 * ((2 : ℝ) ^ θ)⁻¹ - (((2 : ℝ) ^ θ)⁻¹) ^ 2 - 2) ^ θ⁻¹ - 1 := by
  rw [blomqvistBeta, nelsen11_cdf_full]
  simp only [or_self, half_ne_zero, ↓reduceIte, half_val, half_rpow]
  set t := (2 : ℝ) ^ θ with ht
  have ht1 : 1 ≤ t := Real.one_le_rpow (by norm_num) hθ.le
  have ht2 : t < 3 / 2 := by
    have h : t ≤ (2 : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
    rw [← Real.sqrt_eq_rpow] at h
    have hs : Real.sqrt 2 < 3 / 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  have ha0 : 0 < t⁻¹ := inv_pos.mpr (by linarith)
  have ha1 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1
  have ha2 : 2 / 3 < t⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) (by linarith)]
    norm_num
    linarith
  have hpos : 0 ≤ t⁻¹ * t⁻¹ - 2 * (1 - t⁻¹) * (1 - t⁻¹) := by nlinarith
  rw [max_eq_left hpos]
  congr 3
  ring


/-- Nelsen 13 (`θ > 0`): `β = 4 exp (1 - (2 (1 + log 2)^θ - 1)^(1/θ)) - 1`. -/
theorem blomqvistBeta_nelsen13 (θ : ℝ) (hθ : 0 < θ) :
    (nelsen13 θ hθ).blomqvistBeta =
      4 * Real.exp (1 - (2 * (1 + Real.log 2) ^ θ - 1) ^ θ⁻¹) - 1 := by
  rw [blomqvistBeta, nelsen13_cdf_full]
  simp only [or_self, half_ne_zero, ↓reduceIte, half_val]
  rw [one_div, Real.log_inv]
  congr 4
  ring_nf

/-- Nelsen 16 (`θ ≥ 0`): `β = 2 (sqrt (9θ² + 4θ) - 3θ) - 1`. -/
theorem blomqvistBeta_nelsen16 (θ : ℝ) (hθ : 0 ≤ θ) :
    (nelsen16 θ hθ).blomqvistBeta = 2 * (√(9 * θ ^ 2 + 4 * θ) - 3 * θ) - 1 := by
  rw [blomqvistBeta, nelsen16_cdf_full]
  simp only [or_self, half_ne_zero, ↓reduceIte, half_val]
  have e : (1 / 2 + 1 / 2 - 1 - θ * (1 / (1 / 2) + 1 / (1 / 2) - 1)) ^ 2 + 4 * θ =
      9 * θ ^ 2 + 4 * θ := by ring
  rw [e]
  ring

/-- Nelsen 17 (`θ ≠ 0`): `β = 4 ((1 + ((3/2)^(-θ) - 1)^2 / (2^(-θ) - 1))^(-1/θ) - 1) - 1`. -/
theorem blomqvistBeta_nelsen17 (θ : ℝ) (hθ : θ ≠ 0) :
    (nelsen17 θ hθ).blomqvistBeta =
      4 * ((1 + (((3 : ℝ) / 2) ^ (-θ) - 1) ^ 2 / ((2 : ℝ) ^ (-θ) - 1)) ^ (-θ⁻¹) - 1) - 1 := by
  rw [blomqvistBeta, nelsen17_cdf_full]
  simp only [or_self, half_ne_zero, ↓reduceIte, half_val]
  rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num]
  ring_nf

/-- Nelsen 18 (`θ ≥ 2`): `β = (2θ - 3 log 2) / (2θ - log 2)`. -/
theorem blomqvistBeta_nelsen18 (θ : ℝ) (hθ : 2 ≤ θ) :
    (nelsen18 θ hθ).blomqvistBeta = (2 * θ - 3 * Real.log 2) / (2 * θ - Real.log 2) := by
  have hl : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith
  have hne1 : (unitHalf : I) ≠ 1 := by
    intro h; have := congrArg Subtype.val h; change (1 / 2 : ℝ) = 1 at this; norm_num at this
  have h := cdf_nelsen18 θ hθ unitHalf unitHalf half_ne_zero hne1 half_ne_zero hne1
  rw [blomqvistBeta, h]
  simp only [half_val]
  have hd : 0 < 2 * θ - Real.log 2 := by linarith
  have e1 : Real.log (Real.exp (θ / (1 / 2 - 1)) + Real.exp (θ / (1 / 2 - 1))) =
      Real.log 2 - 2 * θ := by
    rw [show θ / (1 / 2 - 1) = -(2 * θ) by ring, ← two_mul, Real.exp_neg,
      Real.log_mul (by norm_num) (by positivity), Real.log_inv, Real.log_exp]
    ring
  have e2 : 1 + θ / (Real.log 2 - 2 * θ) = (θ - Real.log 2) / (2 * θ - Real.log 2) := by
    rw [show Real.log 2 - 2 * θ = -(2 * θ - Real.log 2) by ring, div_neg]
    have hne := hd.ne'
    rw [eq_div_iff hne, add_mul, neg_mul, div_mul_cancel₀ _ hne]
    ring
  rw [e1, e2, max_eq_left (div_nonneg (by linarith) hd.le), eq_div_iff hd.ne']
  have := div_mul_cancel₀ (θ - Real.log 2) hd.ne'
  linear_combination 4 * this


/-- Nelsen 19 (`θ > 0`): `β = 4 θ / log (2 e^(2θ) - e^θ) - 1`. -/
theorem blomqvistBeta_nelsen19 (θ : ℝ) (hθ : 0 < θ) :
    (nelsen19 θ hθ).blomqvistBeta =
      4 * (θ / Real.log (2 * Real.exp (2 * θ) - Real.exp θ)) - 1 := by
  rw [blomqvistBeta, nelsen19_cdf_full]
  simp only [or_self, half_ne_zero, ↓reduceIte, half_val]
  rw [show θ / (1 / 2) = 2 * θ by ring, ← two_mul]

/-- Nelsen 20 (`θ > 0`): `β = 4 (log (2 exp (2^θ) - e))^(-1/θ) - 1`. -/
theorem blomqvistBeta_nelsen20 (θ : ℝ) (hθ : 0 < θ) :
    (nelsen20 θ hθ).blomqvistBeta =
      4 * Real.log (2 * Real.exp ((2 : ℝ) ^ θ) - Real.exp 1) ^ (-θ⁻¹) - 1 := by
  rw [blomqvistBeta, nelsen20_cdf_full]
  simp only [or_self, half_ne_zero, ↓reduceIte, half_val, half_rpow_neg]
  rw [← two_mul]

/-- Nelsen 21 (`θ ≥ 1`): with `p = (1 - 2^(-θ))^(1/θ)`, `β = 3 - 4 (1 - (2p - 1)^θ)^(1/θ)`. -/
theorem blomqvistBeta_nelsen21 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen21 θ hθ).blomqvistBeta =
      3 - 4 * (1 - (2 * (1 - ((2 : ℝ) ^ θ)⁻¹) ^ θ⁻¹ - 1) ^ θ) ^ θ⁻¹ := by
  have hθ0 : 0 < θ := by linarith
  rw [blomqvistBeta, nelsen21_cdf_full]
  simp only [or_self, half_ne_zero, ↓reduceIte, half_val]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, half_rpow]
  have ha : ((2 : ℝ) ^ θ)⁻¹ ≤ 1 / 2 := by
    have : (2 : ℝ) ≤ 2 ^ θ := by
      calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ 2 ^ θ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ
    rw [one_div]
    exact inv_anti₀ (by norm_num) this
  have hp : 1 / 2 ≤ (1 - ((2 : ℝ) ^ θ)⁻¹) ^ θ⁻¹ := by
    calc (1 / 2 : ℝ) = (1 / 2) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (1 / 2) ^ θ⁻¹ :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (inv_le_one_of_one_le₀ hθ)
      _ ≤ (1 - ((2 : ℝ) ^ θ)⁻¹) ^ θ⁻¹ :=
          Real.rpow_le_rpow (by norm_num) (by linarith) (inv_nonneg.mpr hθ0.le)
  rw [max_eq_left (by linarith), show 
    (1 - ((2 : ℝ) ^ θ)⁻¹) ^ θ⁻¹ + (1 - ((2 : ℝ) ^ θ)⁻¹) ^ θ⁻¹ - 1 =
      2 * (1 - ((2 : ℝ) ^ θ)⁻¹) ^ θ⁻¹ - 1 by ring]
  ring

/-- Nelsen 22 (`0 < θ ≤ 1`): with `b = 1 - 2^(-θ)`,
`β = 4 (1 - 2 b sqrt (1 - b^2))^(1/θ) - 1` if `2 b^2 ≤ 1` and `β = -1` otherwise. -/
theorem blomqvistBeta_nelsen22 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    (nelsen22 θ hθ h1).blomqvistBeta =
      if 2 * (1 - ((2 : ℝ) ^ θ)⁻¹) ^ 2 ≤ 1 then
        4 * (1 - 2 * (1 - ((2 : ℝ) ^ θ)⁻¹) * √(1 - (1 - ((2 : ℝ) ^ θ)⁻¹) ^ 2)) ^ θ⁻¹ - 1
      else -1 := by
  rw [blomqvistBeta, nelsen22_cdf_full]
  simp only [or_self, half_ne_zero, ↓reduceIte, half_val, half_rpow]
  set b := 1 - ((2 : ℝ) ^ θ)⁻¹ with hb
  have hc : b ^ 2 + b ^ 2 ≤ 1 ↔ 2 * b ^ 2 ≤ 1 := by
    constructor <;> intro h <;> linarith
  by_cases h : 2 * b ^ 2 ≤ 1
  · simp only [hc.mpr h, h, ↓reduceIte]
    ring_nf
  · simp only [mt hc.mp h, h, ↓reduceIte]
    ring

end ProbabilityTheory.Copula
