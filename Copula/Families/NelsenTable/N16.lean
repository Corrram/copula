/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Ite
import Copula.Archimedean.Truncated

/-! # Nelsen's family 16

Nelsen, *An Introduction to Copulas*, second edition, Table 4.1, number 16 (Section 4.2):
generator `φ(t) = (θ / t + 1) (1 - t)` for `θ ≥ 0` and copula
`C(u, v) = (S + √(S² + 4θ)) / 2` with `S = u + v - 1 - θ (1/u + 1/v - 1)`.

Solving the quadratic `t² + (s - 1 + θ) t - θ = 0` gives the inverse generator
`ψ(s) = (1 - θ - s + √((1 - θ - s)² + 4θ)) / 2`. It is convex because `x ↦ √(x² + c)` is
convex (a Euclidean norm), and antitone because `x ↦ x + √(x² + c)` is monotone. No
derivatives are needed. The generator is strict for `θ > 0`; at `θ = 0` the same formulas
give `ψ(s) = max 0 (1 - s)` and the family is the lower Fréchet bound `W`, as in Nelsen's
table (`C_0 = W`).
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem nelsen16_u_pos (u : I) (hu : u ≠ 0) : 0 < (u : ℝ) :=
  lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))

/-- `x ↦ √(x² + c)` is convex for `c ≥ 0` (the inequality form). -/
theorem sqrt_sq_add_convex_ineq {c : ℝ} (hc : 0 ≤ c) (x y a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    √((a * x + b * y) ^ 2 + c) ≤ a * √(x ^ 2 + c) + b * √(y ^ 2 + c) := by
  have hP := Real.sq_sqrt (show 0 ≤ x ^ 2 + c by positivity)
  have hQ := Real.sq_sqrt (show 0 ≤ y ^ 2 + c by positivity)
  have hP0 := Real.sqrt_nonneg (x ^ 2 + c)
  have hQ0 := Real.sqrt_nonneg (y ^ 2 + c)
  have hPQ : x * y + c ≤ √(x ^ 2 + c) * √(y ^ 2 + c) := by
    rw [← Real.sqrt_mul (by positivity)]
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    nlinarith [sq_nonneg (x - y), mul_nonneg hc (sq_nonneg (x - y))]
  rw [Real.sqrt_le_left (by positivity)]
  have key : (a * √(x ^ 2 + c) + b * √(y ^ 2 + c)) ^ 2 - ((a * x + b * y) ^ 2 + c) =
      2 * (a * b) * (√(x ^ 2 + c) * √(y ^ 2 + c) - (x * y + c)) := by
    linear_combination a ^ 2 * hP + b ^ 2 * hQ + c * (a + b + 1) * hab
  nlinarith [mul_le_mul_of_nonneg_left hPQ (mul_nonneg ha hb)]

/-- `x ↦ x + √(x² + c)` is monotone. -/
theorem add_sqrt_sq_add_mono {c : ℝ} (hc : 0 ≤ c) {x y : ℝ} (hxy : x ≤ y) :
    x + √(x ^ 2 + c) ≤ y + √(y ^ 2 + c) := by
  have hQ := Real.sq_sqrt (show 0 ≤ y ^ 2 + c by positivity)
  have hQ0 := Real.sqrt_nonneg (y ^ 2 + c)
  have hY : -y ≤ √(y ^ 2 + c) :=
    le_trans (neg_le_abs y) (Real.abs_le_sqrt (by linarith))
  have h : √(x ^ 2 + c) ≤ √(y ^ 2 + c) + (y - x) := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hY (sub_nonneg.mpr hxy)]
  linarith

/-- `x + √(x² + c) ≥ 0`. -/
theorem add_sqrt_sq_add_nonneg {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : 0 ≤ x + √(x ^ 2 + c) := by
  have h := Real.abs_le_sqrt (show x ^ 2 ≤ x ^ 2 + c by linarith)
  linarith [neg_abs_le x]

/-- The inverse generator `s ↦ (1 - θ - s + √((1 - θ - s)² + 4θ)) / 2` of Nelsen's family 16,
for `θ ≥ 0`. Its generator is `u ↦ (θ / u + 1) (1 - u)`. -/
noncomputable def nelsen16Generator (θ : ℝ) (hθ : 0 ≤ θ) : BivariateGenerator where
  toFun s := (1 - θ - s + √((1 - θ - s) ^ 2 + 4 * θ)) / 2
  invFun u := (θ / (u : ℝ) + 1) * (1 - (u : ℝ))
  nonneg s _ := div_nonneg (add_sqrt_sq_add_nonneg (by linarith) _) zero_le_two
  antitone x _ y _ hxy := by
    apply div_le_div_of_nonneg_right _ zero_le_two
    exact add_sqrt_sq_add_mono (by linarith) (by linarith)
  convex := by
    refine ⟨convex_Ici _, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul]
    have he : 1 - θ - (a * x + b * y) = a * (1 - θ - x) + b * (1 - θ - y) := by
      linear_combination (1 - θ) * hab.symm
    rw [he]
    have h := sqrt_sq_add_convex_ineq (show 0 ≤ 4 * θ by linarith) (1 - θ - x) (1 - θ - y)
      a b ha hb hab
    nlinarith
  inv_nonneg u hu := by
    have hup := nelsen16_u_pos u hu
    exact mul_nonneg (by positivity) (sub_nonneg.mpr u.property.2)
  inv_antitone u v hu huv := by
    have hup := nelsen16_u_pos u hu
    have huv' : (u : ℝ) ≤ (v : ℝ) := huv
    have hvp : 0 < (v : ℝ) := lt_of_lt_of_le hup huv'
    show (θ / (v : ℝ) + 1) * (1 - (v : ℝ)) ≤ (θ / (u : ℝ) + 1) * (1 - (u : ℝ))
    apply mul_le_mul _ (by linarith) (sub_nonneg.mpr v.property.2) (by positivity)
    have := div_le_div_of_nonneg_left hθ hup huv'
    linarith
  inv_one := by simp
  right_inv u hu := by
    have hup := nelsen16_u_pos u hu
    show (1 - θ - (θ / (u : ℝ) + 1) * (1 - (u : ℝ)) +
      √((1 - θ - (θ / (u : ℝ) + 1) * (1 - (u : ℝ))) ^ 2 + 4 * θ)) / 2 = (u : ℝ)
    have hS : 1 - θ - (θ / (u : ℝ) + 1) * (1 - (u : ℝ)) = (u : ℝ) - θ / (u : ℝ) := by
      field_simp
      ring
    have hD : ((u : ℝ) - θ / (u : ℝ)) ^ 2 + 4 * θ = ((u : ℝ) + θ / (u : ℝ)) ^ 2 := by
      field_simp
      ring
    rw [hS, hD, Real.sqrt_sq (by positivity)]
    ring

/-- Nelsen's family 16 for `θ ≥ 0`. -/
noncomputable def nelsen16 (θ : ℝ) (hθ : 0 ≤ θ) : Copula 2 :=
  (nelsen16Generator θ hθ).copula

theorem isArchimedean_nelsen16 (θ : ℝ) (hθ : 0 ≤ θ) : IsArchimedean (nelsen16 θ hθ) :=
  (nelsen16Generator θ hθ).isArchimedean

/-- The CDF of Nelsen's family 16 on positive coordinates:
`C(u, v) = (S + √(S² + 4θ)) / 2` with `S = u + v - 1 - θ (1/u + 1/v - 1)`. -/
theorem cdf_nelsen16 (θ : ℝ) (hθ : 0 ≤ θ) (u v : I) (hu : u ≠ 0) (hv : v ≠ 0) :
    (nelsen16 θ hθ).cdf ![u, v] =
      ((u : ℝ) + (v : ℝ) - 1 - θ * (1 / (u : ℝ) + 1 / (v : ℝ) - 1) +
        √(((u : ℝ) + (v : ℝ) - 1 - θ * (1 / (u : ℝ) + 1 / (v : ℝ) - 1)) ^ 2 + 4 * θ)) / 2 := by
  have hup := nelsen16_u_pos u hu
  have hvp := nelsen16_u_pos v hv
  rw [nelsen16, BivariateGenerator.cdf_copula]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [BivariateGenerator.cdf, ite_or_of_not hu hv _ _]
  show (1 - θ - ((θ / (u : ℝ) + 1) * (1 - (u : ℝ)) + (θ / (v : ℝ) + 1) * (1 - (v : ℝ))) +
    √((1 - θ - ((θ / (u : ℝ) + 1) * (1 - (u : ℝ)) + (θ / (v : ℝ) + 1) * (1 - (v : ℝ)))) ^ 2 +
      4 * θ)) / 2 = _
  have hS : 1 - θ - ((θ / (u : ℝ) + 1) * (1 - (u : ℝ)) + (θ / (v : ℝ) + 1) * (1 - (v : ℝ))) =
      (u : ℝ) + (v : ℝ) - 1 - θ * (1 / (u : ℝ) + 1 / (v : ℝ) - 1) := by
    field_simp
    ring
  rw [hS]

/-- Nelsen's family 16 on the whole closed unit square, with grounded zero axes. -/
theorem nelsen16_cdf_full (θ : ℝ) (hθ : 0 ≤ θ) (u v : I) :
    (nelsen16 θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        ((u : ℝ) + (v : ℝ) - 1 - θ * (1 / (u : ℝ) + 1 / (v : ℝ) - 1) +
          √(((u : ℝ) + (v : ℝ) - 1 - θ * (1 / (u : ℝ) + 1 / (v : ℝ) - 1)) ^ 2 + 4 * θ)) / 2 := by
  by_cases hu : u = 0
  · subst u
    rw [ite_or_of_left rfl _ _]
    exact (nelsen16 θ hθ).cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl
  by_cases hv : v = 0
  · subst v
    rw [ite_or_of_right rfl _ _]
    exact (nelsen16 θ hθ).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
  rw [ite_or_of_not hu hv _ _]
  exact cdf_nelsen16 θ hθ u v hu hv

/-- At `θ = 0` the generator of family 16 is the truncated linear generator of `W`. -/
theorem nelsen16Generator_zero : nelsen16Generator 0 le_rfl = truncatedLinearGenerator := by
  have h1 : (nelsen16Generator 0 le_rfl).toFun = truncatedLinearGenerator.toFun := by
    funext s
    show (1 - 0 - s + √((1 - 0 - s) ^ 2 + 4 * 0)) / 2 = max 0 (1 - s)
    rw [mul_zero, add_zero, Real.sqrt_sq_eq_abs, sub_zero]
    rcases le_total 0 (1 - s) with h | h
    · rw [abs_of_nonneg h, max_eq_right h]
      ring
    · rw [abs_of_nonpos h, max_eq_left h]
      ring
  have h2 : (nelsen16Generator 0 le_rfl).invFun = truncatedLinearGenerator.invFun := by
    funext u
    show (0 / (u : ℝ) + 1) * (1 - (u : ℝ)) = 1 - (u : ℝ)
    rw [zero_div, zero_add, one_mul]
  cases h : nelsen16Generator 0 le_rfl
  cases h' : truncatedLinearGenerator
  rw [h, h'] at h1 h2
  simp only at h1 h2
  subst h1 h2
  rfl

/-- `C_0 = W`: at `θ = 0` Nelsen's family 16 is the lower Fréchet bound. -/
@[simp] theorem nelsen16_zero : nelsen16 0 le_rfl = countermonotonic := by
  rw [nelsen16, nelsen16Generator_zero, truncatedLinearGenerator_copula]

end ProbabilityTheory.Copula
