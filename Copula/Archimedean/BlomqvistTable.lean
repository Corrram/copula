/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Basic
import Copula.Rank.Nelsen7
import Copula.Families.Clayton.CDF
import Copula.Families.Clayton.Negative
import Copula.Families.Frank
import Copula.Families.FrankNegative
import Copula.Families.AMH
import Copula.Families.Joe
import Copula.Families.Nelsen
import Copula.Families.Nelsen7
import Copula.Families.Nelsen8

/-! # Blomqvist's beta of the classical Archimedean families

Blomqvist's beta is `β = 4 C(1/2, 1/2) - 1`, so for every family with an explicit CDF it is
obtained by evaluating the CDF at the centre of the unit square. This file treats the
families of Nelsen, *An Introduction to Copulas*, second edition, Table 4.1, numbers 1, 2, 3, 5,
6, 7, 8, 12, 14, 15 (Gumbel, number 4, is in `Copula.Rank.PowerDiagonal`); the remaining
families are in `Copula.Archimedean.BlomqvistTableN`.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace BlomqvistTable

theorem half_val : ((unitHalf : I) : ℝ) = 1 / 2 := rfl

theorem half_ne_zero : (unitHalf : I) ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  change (1 / 2 : ℝ) = 0 at this
  norm_num at this

theorem not_zero_or : ¬ ((unitHalf : I) = 0 ∨ (unitHalf : I) = 0) := by
  simp [half_ne_zero]

theorem half_rpow_neg (θ : ℝ) : ((1 / 2 : ℝ)) ^ (-θ) = (2 : ℝ) ^ θ := by
  rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num), inv_inv]

theorem half_rpow (θ : ℝ) : ((1 / 2 : ℝ)) ^ θ = ((2 : ℝ) ^ θ)⁻¹ := by
  rw [one_div, Real.inv_rpow (by norm_num)]

end BlomqvistTable

open BlomqvistTable

/-- Clayton, `θ > 0`: `β = 4 (2^(θ+1) - 1)^(-1/θ) - 1`. -/
theorem blomqvistBeta_clayton (θ : ℝ) (hθ : 0 < θ) :
    (clayton 2 θ hθ).blomqvistBeta = 4 * ((2 : ℝ) ^ (θ + 1) - 1) ^ (-1 / θ) - 1 := by
  have h := cdf_clayton (d := 2) θ hθ ![unitHalf, unitHalf]
    (by intro i; fin_cases i <;> simp [half_val])
  rw [blomqvistBeta, h]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, half_val,
    half_rpow_neg, Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num
  ring_nf


/-- Clayton, `-1 ≤ θ < 0`: the same formula `β = 4 (2^(θ+1) - 1)^(-1/θ) - 1`. -/
theorem blomqvistBeta_claytonNegative (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0) :
    (claytonNegative θ hθ hn).blomqvistBeta = 4 * ((2 : ℝ) ^ (θ + 1) - 1) ^ (-1 / θ) - 1 := by
  have h := cdf_claytonNegative θ hθ hn ![unitHalf, unitHalf]
    (by intro i; fin_cases i <;> simp [half_ne_zero])
  rw [blomqvistBeta, h]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, half_val, half_rpow_neg]
  have h2 : 0 ≤ (2 : ℝ) ^ θ + (2 : ℝ) ^ θ - 1 := by
    have : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ θ := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hθ
      simpa [Real.rpow_neg_one] using this
    linarith
  rw [max_eq_right h2, Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0), inv_eq_one_div,
    show (1 : ℝ) / -θ = -1 / θ by ring]
  ring_nf

/-- Two equal terms `(1/2)^θ` under a `θ`-th root: `(2 (1/2)^θ)^(1/θ) = 2^(1/θ) / 2`. -/
theorem two_half_rpow_inv (θ : ℝ) (hθ : 0 < θ) :
    (((1 : ℝ) - 1 / 2) ^ θ + (1 - 1 / 2) ^ θ) ^ θ⁻¹ = (2 : ℝ) ^ θ⁻¹ / 2 := by
  rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.inv_rpow (by norm_num), ← two_mul,
    show 2 * ((2 : ℝ) ^ θ)⁻¹ = 2 / 2 ^ θ by ring, Real.div_rpow (by norm_num) (by positivity), Real.rpow_rpow_inv (by norm_num) hθ.ne']


/-- Nelsen 2 (`θ ≥ 1`): `β = 3 - 2^(1/θ + 1)`. -/
theorem blomqvistBeta_nelsen2 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen2 θ hθ).blomqvistBeta = 3 - (2 : ℝ) ^ (θ⁻¹ + 1) := by
  have hθ0 : 0 < θ := by linarith
  rw [blomqvistBeta, nelsen2_cdf_full]
  simp only [or_self, half_ne_zero, ↓reduceIte, half_val, two_half_rpow_inv θ hθ0]
  have h2 : (2 : ℝ) ^ θ⁻¹ ≤ 2 := by
    calc (2 : ℝ) ^ θ⁻¹ ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (inv_le_one_of_one_le₀ hθ)
      _ = 2 := Real.rpow_one 2
  rw [max_eq_right (by linarith), Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- Ali--Mikhail--Haq (`-1 ≤ θ ≤ 1`): `β = θ / (4 - θ)`. -/
theorem blomqvistBeta_amh (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) :
    (amh θ hmin hmax).blomqvistBeta = θ / (4 - θ) := by
  rw [blomqvistBeta, cdf_amh]
  simp only [half_val]
  have : (0 : ℝ) < 4 - θ := by linarith
  rw [show 1 - θ * (1 - 1 / 2) * (1 - 1 / 2) = (4 - θ) / 4 by ring]
  field_simp
  ring

/-- Frank (`θ > 0`): `β = 4 log ((1 + e^(θ/2)) / 2) / θ - 1`. -/
theorem blomqvistBeta_frank (θ : ℝ) (hθ : 0 < θ) :
    (frank θ hθ).blomqvistBeta = 4 * Real.log ((1 + Real.exp (θ / 2)) / 2) / θ - 1 := by
  rw [blomqvistBeta, frank_cdf_full]
  simp only [or_self, half_ne_zero, ↓reduceIte, half_val]
  set E := Real.exp (θ / 2) with hE
  have hE1 : 1 < E := by rw [hE]; exact Real.one_lt_exp_iff.mpr (by linarith)
  have h1 : Real.exp (-θ * (1 / 2)) = E⁻¹ := by
    rw [hE, ← Real.exp_neg]; congr 1; ring
  have h2 : Real.exp (-θ) = E⁻¹ * E⁻¹ := by
    rw [hE, ← Real.exp_neg, ← Real.exp_add]; congr 1; ring
  have hE0 : 0 < E := by linarith
  have hEi : E⁻¹ < 1 := inv_lt_one_of_one_lt₀ hE1
  have hEp : 0 < E⁻¹ := inv_pos.mpr hE0
  have h3 : 1 - E⁻¹ * E⁻¹ ≠ 0 := by nlinarith
  have step : (1 - E⁻¹) * (1 - E⁻¹) / (1 - E⁻¹ * E⁻¹) = (E - 1) / (E + 1) := by
    rw [div_eq_div_iff h3 (by positivity)]
    field_simp
    ring
  have key : 1 - (1 - E⁻¹) * (1 - E⁻¹) / (1 - E⁻¹ * E⁻¹) = ((1 + E) / 2)⁻¹ := by
    rw [step]
    field_simp
    ring
  rw [h1, h2, key, Real.log_inv]
  ring


/-- Frank (`θ < 0`): `β = 1 + 4 log ((1 + e^(-θ/2)) / 2) / θ`. -/
theorem blomqvistBeta_frankNegative (θ : ℝ) (hθ : θ < 0) :
    (frankNegative θ hθ).blomqvistBeta =
      1 + 4 * Real.log ((1 + Real.exp (-θ / 2)) / 2) / θ := by
  rw [blomqvistBeta, frankNegative_cdf_full]
  have hs : unitInterval.symm unitHalf = unitHalf := by
    apply Subtype.ext
    change 1 - (1 / 2 : ℝ) = 1 / 2
    norm_num
  simp only [hs, or_self, half_ne_zero, ↓reduceIte, half_val]
  set E := Real.exp (-θ / 2) with hE
  have hE1 : 1 < E := by rw [hE]; exact Real.one_lt_exp_iff.mpr (by linarith)
  have hE0 : 0 < E := by linarith
  have h1 : Real.exp (θ * (1 / 2)) = E⁻¹ := by
    rw [hE, ← Real.exp_neg]; congr 1; ring
  have h2 : Real.exp θ = E⁻¹ * E⁻¹ := by
    rw [hE, ← Real.exp_neg, ← Real.exp_add]; congr 1; ring
  have hEi : E⁻¹ < 1 := inv_lt_one_of_one_lt₀ hE1
  have hEp : 0 < E⁻¹ := inv_pos.mpr hE0
  have h3 : 1 - E⁻¹ * E⁻¹ ≠ 0 := by nlinarith
  have step : (1 - E⁻¹) * (1 - E⁻¹) / (1 - E⁻¹ * E⁻¹) = (E - 1) / (E + 1) := by
    rw [div_eq_div_iff h3 (by positivity)]
    field_simp
    ring
  have key : 1 - (1 - E⁻¹) * (1 - E⁻¹) / (1 - E⁻¹ * E⁻¹) = ((1 + E) / 2)⁻¹ := by
    rw [step]
    field_simp
    ring
  rw [h1, h2, key, Real.log_inv]
  have : θ ≠ 0 := hθ.ne
  field_simp
  ring

/-- Joe (`θ ≥ 1`): `β = 3 - 2 (2 - 2^(-θ))^(1/θ)`. -/
theorem blomqvistBeta_joe (θ : ℝ) (hθ : 1 ≤ θ) :
    (joe θ hθ).blomqvistBeta = 3 - 2 * (2 - ((2 : ℝ) ^ θ)⁻¹) ^ θ⁻¹ := by
  have hθ0 : 0 < θ := by linarith
  rw [blomqvistBeta, joe_cdf_full]
  simp only [or_self, half_ne_zero, ↓reduceIte, half_val]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, half_rpow]
  set a := ((2 : ℝ) ^ θ)⁻¹ with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by
    rw [ha]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by norm_num) hθ0.le)
  have e1 : a + a - a * a = a * (2 - a) := by ring
  have e2 : a ^ θ⁻¹ = 1 / 2 := by
    rw [ha, ← half_rpow, Real.rpow_rpow_inv (by norm_num) hθ0.ne']
  rw [e1, Real.mul_rpow ha0 (by linarith), e2]
  ring

/-- Nelsen 7 (`θ ∈ [0, 1]`): `β = θ - 1`. -/
theorem blomqvistBeta_nelsen7 (θ : I) : (nelsen7 θ).blomqvistBeta = (θ : ℝ) - 1 := by
  rw [blomqvistBeta, cdf_nelsen7]
  simp only [half_val]
  rw [max_eq_right (by nlinarith [θ.property.1])]
  ring

/-- Nelsen 8 (`θ ≥ 1`): `β = (θ - 3) / (3θ - 1)`. -/
theorem blomqvistBeta_nelsen8 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen8 θ hθ).blomqvistBeta = (θ - 3) / (3 * θ - 1) := by
  rw [blomqvistBeta, nelsen8_cdf_full]
  simp only [half_val]
  have hd : (0 : ℝ) < 3 * θ - 1 := by linarith
  have hd2 : (0 : ℝ) < θ ^ 2 - (θ - 1) ^ 2 * (1 - 1 / 2) * (1 - 1 / 2) := by nlinarith
  have hd3 : θ ^ 2 - (θ - 1) ^ 2 * (1 - 1 / 2) * (1 - 1 / 2) ≠ 0 := hd2.ne'
  have e : (θ ^ 2 * (1 / 2) * (1 / 2) - (1 - 1 / 2) * (1 - 1 / 2)) /
      (θ ^ 2 - (θ - 1) ^ 2 * (1 - 1 / 2) * (1 - 1 / 2)) = (θ - 1) / (3 * θ - 1) := by
    rw [div_eq_div_iff hd3 hd.ne']
    nlinarith
  rw [e, max_eq_right (div_nonneg (by linarith) hd.le)]
  have hne := hd.ne'
  rw [eq_div_iff hne]
  linear_combination 4 * div_mul_cancel₀ (θ - 1) hne


/-- `(x^θ + x^θ)^(1/θ) = 2^(1/θ) x` for `x ≥ 0`. -/
theorem two_rpow_inv_mul (θ x : ℝ) (hθ : 0 < θ) (hx : 0 ≤ x) :
    (x ^ θ + x ^ θ) ^ θ⁻¹ = (2 : ℝ) ^ θ⁻¹ * x := by
  rw [← two_mul, Real.mul_rpow (by norm_num) (by positivity), Real.rpow_rpow_inv hx hθ.ne']

/-- Nelsen 12 (`θ ≥ 1`): `β = 4 / (1 + 2^(1/θ)) - 1`. -/
theorem blomqvistBeta_nelsen12 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen12 θ hθ).blomqvistBeta = 4 * (1 + (2 : ℝ) ^ θ⁻¹)⁻¹ - 1 := by
  have hθ0 : 0 < θ := by linarith
  rw [blomqvistBeta, nelsen12_cdf_full]
  simp only [or_self, half_ne_zero, ↓reduceIte, half_val]
  norm_num

/-- Nelsen 14 (`θ ≥ 1`): with `q = 2^(1/θ)`, `β = 4 (1 + q (q - 1))^(-θ) - 1`. -/
theorem blomqvistBeta_nelsen14 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen14 θ hθ).blomqvistBeta =
      4 * (1 + (2 : ℝ) ^ θ⁻¹ * ((2 : ℝ) ^ θ⁻¹ - 1)) ^ (-θ) - 1 := by
  have hθ0 : 0 < θ := by linarith
  rw [blomqvistBeta, nelsen14_cdf_full]
  simp only [or_self, half_ne_zero, ↓reduceIte, half_val]
  have hq : 1 ≤ (2 : ℝ) ^ θ⁻¹ := Real.one_le_rpow (by norm_num) (inv_nonneg.mpr hθ0.le)
  rw [half_rpow_neg, two_rpow_inv_mul θ _ hθ0 (by linarith)]

/-- Nelsen 15 (Genest--Ghoudi, `θ ≥ 1`): `β = 4 (2 - 2^(1/θ))^θ - 1`. -/
theorem blomqvistBeta_genestGhoudi (θ : ℝ) (hθ : 1 ≤ θ) :
    (genestGhoudi θ hθ).blomqvistBeta = 4 * (2 - (2 : ℝ) ^ θ⁻¹) ^ θ - 1 := by
  have hθ0 : 0 < θ := by linarith
  rw [blomqvistBeta, genestGhoudi_cdf_full]
  simp only [or_self, half_ne_zero, ↓reduceIte, half_val]
  have hq : 1 ≤ (2 : ℝ) ^ θ⁻¹ := Real.one_le_rpow (by norm_num) (inv_nonneg.mpr hθ0.le)
  have hq2 : (2 : ℝ) ^ θ⁻¹ ≤ 2 := by
    calc (2 : ℝ) ^ θ⁻¹ ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (inv_le_one_of_one_le₀ hθ)
      _ = 2 := Real.rpow_one 2
  have hp : 0 ≤ 1 - (1 / 2 : ℝ) ^ θ⁻¹ := by
    have : (1 / 2 : ℝ) ^ θ⁻¹ ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num)
      (inv_nonneg.mpr hθ0.le)
    linarith
  rw [two_rpow_inv_mul θ _ hθ0 hp, half_rpow]
  have e : (2 : ℝ) ^ θ⁻¹ * (1 - ((2 : ℝ) ^ θ⁻¹)⁻¹) = (2 : ℝ) ^ θ⁻¹ - 1 := by
    have : (2 : ℝ) ^ θ⁻¹ ≠ 0 := by positivity
    field_simp
  rw [e, max_eq_right (by linarith)]
  congr 3
  ring

end ProbabilityTheory.Copula
