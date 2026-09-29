/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Ite
import Copula.Archimedean.Exponential
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Nelsen's family 17

Nelsen, *An Introduction to Copulas*, second edition, Table 4.1, number 17 (Section 4.2):
generator `φ(t) = -ln (((1 + t)^(-θ) - 1) / (2^(-θ) - 1))` for `θ ≠ 0` and copula
`C(u, v) = (1 + ((1 + u)^(-θ) - 1) ((1 + v)^(-θ) - 1) / (2^(-θ) - 1))^(-1/θ) - 1`.

With `d = 2^(-θ) - 1 > -1` and `q = -1/θ`, the inverse generator is
`ψ(s) = (1 + d e^(-s))^q - 1`. Its second derivative is
`ψ''(s) = q d e^(-s) (1 + d e^(-s))^(q - 2) (1 + q d e^(-s))`, which is nonnegative because
`q d = (1 - 2^(-θ)) / θ > 0` for every `θ ≠ 0`. This covers Nelsen's whole parameter range,
both signs of `θ` at once. At `θ = -1` the family is independence (`C_{-1} = Π`).
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem nelsen17_u_pos (u : I) (hu : u ≠ 0) : 0 < (u : ℝ) :=
  lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))

/-- The sign facts for the denominator `d = 2^(-θ) - 1`. -/
private theorem nelsen17_den_neg (θ : ℝ) (hθ : 0 < θ) : (2 : ℝ) ^ (-θ) - 1 < 0 := by
  have := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hθ)
  linarith

private theorem nelsen17_den_pos (θ : ℝ) (hθ : θ < 0) : 0 < (2 : ℝ) ^ (-θ) - 1 := by
  have := Real.one_lt_rpow one_lt_two (neg_pos.mpr hθ)
  linarith

private theorem nelsen17_den_ne (θ : ℝ) (hθ : θ ≠ 0) : (2 : ℝ) ^ (-θ) - 1 ≠ 0 := by
  rcases hθ.lt_or_gt with h | h
  · exact (nelsen17_den_pos θ h).ne'
  · exact (nelsen17_den_neg θ h).ne

/-- `q d > 0` with `q = -1/θ` and `d = 2^(-θ) - 1`. -/
private theorem nelsen17_qd_pos (θ : ℝ) (hθ : θ ≠ 0) : 0 < -θ⁻¹ * ((2 : ℝ) ^ (-θ) - 1) := by
  rcases hθ.lt_or_gt with h | h
  · exact mul_pos (neg_pos.mpr (inv_lt_zero.mpr h)) (nelsen17_den_pos θ h)
  · exact mul_pos_of_neg_of_neg (neg_neg_of_pos (inv_pos.mpr h)) (nelsen17_den_neg θ h)

/-- The base `1 + d e^(-s)` is positive for `s ≥ 0`. -/
private theorem nelsen17_base_pos (θ : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    0 < 1 + ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-s) := by
  have hx := Real.exp_pos (-s)
  have hx1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 := Real.rpow_pos_of_pos two_pos (-θ)
  have he : 1 + ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-s) =
      (1 - Real.exp (-s)) + Real.exp (-s) * (2 : ℝ) ^ (-θ) := by ring
  rw [he]
  nlinarith [mul_pos hx h2]

/-- Monotonicity of `x ↦ ((1 + x)^(-θ) - 1) / (2^(-θ) - 1)`. -/
private theorem nelsen17_ratio_mono (θ : ℝ) (hθ : θ ≠ 0) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ((1 + x) ^ (-θ) - 1) / ((2 : ℝ) ^ (-θ) - 1) ≤ ((1 + y) ^ (-θ) - 1) / ((2 : ℝ) ^ (-θ) - 1) := by
  rcases hθ.lt_or_gt with h | h
  · apply div_le_div_of_nonneg_right _ (nelsen17_den_pos θ h).le
    have := Real.rpow_le_rpow (by linarith : 0 ≤ 1 + x) (by linarith : 1 + x ≤ 1 + y)
      (neg_pos.mpr h).le
    linarith
  · apply div_le_div_of_nonpos_of_le (nelsen17_den_neg θ h).le
    have := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < 1 + x) (by linarith : 1 + x ≤ 1 + y)
      (neg_nonpos.mpr h.le)
    linarith

/-- The ratio `((1 + x)^(-θ) - 1) / (2^(-θ) - 1)` lies in `(0, 1]` for `0 < x ≤ 1`. -/
private theorem nelsen17_ratio_mem (θ : ℝ) (hθ : θ ≠ 0) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    0 < ((1 + x) ^ (-θ) - 1) / ((2 : ℝ) ^ (-θ) - 1) ∧
      ((1 + x) ^ (-θ) - 1) / ((2 : ℝ) ^ (-θ) - 1) ≤ 1 := by
  constructor
  · rcases hθ.lt_or_gt with h | h
    · apply div_pos _ (nelsen17_den_pos θ h)
      have := Real.one_lt_rpow (by linarith : 1 < 1 + x) (neg_pos.mpr h)
      linarith
    · apply div_pos_of_neg_of_neg _ (nelsen17_den_neg θ h)
      have := Real.rpow_lt_one_of_one_lt_of_neg (by linarith : 1 < 1 + x) (neg_neg_of_pos h)
      linarith
  · have h := nelsen17_ratio_mono θ hθ hx.le hx1
    rwa [show (1 : ℝ) + 1 = 2 by norm_num, div_self (nelsen17_den_ne θ hθ)] at h

private theorem nelsen17_hasDerivAt (θ : ℝ) {t : ℝ} (ht : 0 < 1 + ((2 : ℝ) ^ (-θ) - 1) *
    Real.exp (-t)) :
    HasDerivAt (fun x => (1 + ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-x)) ^ (-θ⁻¹) - 1)
      (-(-θ⁻¹ * ((2 : ℝ) ^ (-θ) - 1)) * (Real.exp (-t) *
        (1 + ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-t)) ^ (-θ⁻¹ - 1))) t := by
  have he : HasDerivAt (fun x => Real.exp (-x)) (Real.exp (-t) * (-1)) t :=
    (hasDerivAt_neg t).exp
  have h := ((he.const_mul ((2 : ℝ) ^ (-θ) - 1)).const_add 1).rpow_const (p := -θ⁻¹)
    (Or.inl ht.ne')
  refine (h.sub_const 1).congr_deriv ?_
  ring

private theorem nelsen17_hasDerivAt2 (θ : ℝ) {t : ℝ} (ht : 0 < 1 + ((2 : ℝ) ^ (-θ) - 1) *
    Real.exp (-t)) :
    HasDerivAt (fun x => -(-θ⁻¹ * ((2 : ℝ) ^ (-θ) - 1)) * (Real.exp (-x) *
        (1 + ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-x)) ^ (-θ⁻¹ - 1)))
      ((-θ⁻¹ * ((2 : ℝ) ^ (-θ) - 1)) * Real.exp (-t) *
        ((1 + ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-t)) ^ (-θ⁻¹ - 1) +
          (-θ⁻¹ - 1) * ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-t) *
            (1 + ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-t)) ^ (-θ⁻¹ - 1 - 1))) t := by
  have he : HasDerivAt (fun x => Real.exp (-x)) (Real.exp (-t) * (-1)) t :=
    (hasDerivAt_neg t).exp
  have h := ((he.const_mul ((2 : ℝ) ^ (-θ) - 1)).const_add 1).rpow_const (p := -θ⁻¹ - 1)
    (Or.inl ht.ne')
  refine ((he.mul h).const_mul (-(-θ⁻¹ * ((2 : ℝ) ^ (-θ) - 1)))).congr_deriv ?_
  ring

private theorem nelsen17_convexOn (θ : ℝ) (hθ : θ ≠ 0) :
    ConvexOn ℝ (Ici 0) (fun x => (1 + ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-x)) ^ (-θ⁻¹) - 1) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
    (f' := fun t => -(-θ⁻¹ * ((2 : ℝ) ^ (-θ) - 1)) * (Real.exp (-t) *
        (1 + ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-t)) ^ (-θ⁻¹ - 1)))
    (f'' := fun t => (-θ⁻¹ * ((2 : ℝ) ^ (-θ) - 1)) * Real.exp (-t) *
        ((1 + ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-t)) ^ (-θ⁻¹ - 1) +
          (-θ⁻¹ - 1) * ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-t) *
            (1 + ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-t)) ^ (-θ⁻¹ - 1 - 1))) ?_ ?_ ?_ ?_
  · intro t ht
    exact (nelsen17_hasDerivAt θ (nelsen17_base_pos θ ht)).continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact (nelsen17_hasDerivAt θ (nelsen17_base_pos θ ht0.le)).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact (nelsen17_hasDerivAt2 θ (nelsen17_base_pos θ ht0.le)).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    have hb := nelsen17_base_pos θ ht0.le
    have hqd := nelsen17_qd_pos θ hθ
    have hx := Real.exp_pos (-t)
    set B := 1 + ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-t) with hB
    have hsplit : B ^ (-θ⁻¹ - 1) = B ^ (-θ⁻¹ - 1 - 1) * B := by
      rw [← Real.rpow_add_one hb.ne']
      ring_nf
    have hq : 0 < B ^ (-θ⁻¹ - 1 - 1) := Real.rpow_pos_of_pos hb _
    show 0 ≤ (-θ⁻¹ * ((2 : ℝ) ^ (-θ) - 1)) * Real.exp (-t) *
        (B ^ (-θ⁻¹ - 1) + (-θ⁻¹ - 1) * ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-t) *
          B ^ (-θ⁻¹ - 1 - 1))
    have hinner : B ^ (-θ⁻¹ - 1) + (-θ⁻¹ - 1) * ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-t) *
        B ^ (-θ⁻¹ - 1 - 1) = B ^ (-θ⁻¹ - 1 - 1) *
          (1 + (-θ⁻¹ * ((2 : ℝ) ^ (-θ) - 1)) * Real.exp (-t)) := by
      rw [hsplit, hB]
      ring
    rw [hinner]
    exact mul_nonneg (mul_nonneg hqd.le hx.le) (mul_nonneg hq.le (by positivity))

/-- The inverse generator `s ↦ (1 + (2^(-θ) - 1) e^(-s))^(-1/θ) - 1` of Nelsen's family 17,
for `θ ≠ 0`. Its generator is `u ↦ -ln (((1 + u)^(-θ) - 1) / (2^(-θ) - 1))`. -/
noncomputable def nelsen17Generator (θ : ℝ) (hθ : θ ≠ 0) : BivariateGenerator where
  toFun s := (1 + ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-s)) ^ (-θ⁻¹) - 1
  invFun u := -Real.log (((1 + (u : ℝ)) ^ (-θ) - 1) / ((2 : ℝ) ^ (-θ) - 1))
  nonneg s hs := by
    have hs0 : 0 ≤ s := hs
    have hb := nelsen17_base_pos θ hs0
    have hx := Real.exp_pos (-s)
    have hx1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    apply sub_nonneg.mpr
    rcases hθ.lt_or_gt with h | h
    · apply Real.one_le_rpow _ (neg_nonneg.mpr (inv_nonpos.mpr h.le))
      nlinarith [nelsen17_den_pos θ h]
    · apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hb _
        (neg_nonpos.mpr (inv_nonneg.mpr h.le))
      nlinarith [nelsen17_den_neg θ h]
  antitone x hx y hy hxy := by
    have hx0 : 0 ≤ x := hx
    have hy0 : 0 ≤ y := hy
    have he : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    show (1 + ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-y)) ^ (-θ⁻¹) - 1 ≤
      (1 + ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-x)) ^ (-θ⁻¹) - 1
    apply sub_le_sub_right
    rcases hθ.lt_or_gt with h | h
    · apply Real.rpow_le_rpow (nelsen17_base_pos θ hy0).le _
        (neg_nonneg.mpr (inv_nonpos.mpr h.le))
      nlinarith [nelsen17_den_pos θ h]
    · apply Real.rpow_le_rpow_of_nonpos (nelsen17_base_pos θ hx0) _
        (neg_nonpos.mpr (inv_nonneg.mpr h.le))
      nlinarith [nelsen17_den_neg θ h]
  convex := nelsen17_convexOn θ hθ
  inv_nonneg u hu := by
    obtain ⟨h0, h1⟩ := nelsen17_ratio_mem θ hθ (nelsen17_u_pos u hu) u.property.2
    exact neg_nonneg.mpr (Real.log_nonpos h0.le h1)
  inv_antitone u v hu huv := by
    have hup := nelsen17_u_pos u hu
    obtain ⟨h0, _⟩ := nelsen17_ratio_mem θ hθ hup u.property.2
    exact neg_le_neg (Real.log_le_log h0 (nelsen17_ratio_mono θ hθ hup.le huv))
  inv_one := by
    rw [Set.Icc.coe_one, show (1 : ℝ) + 1 = 2 by norm_num, div_self (nelsen17_den_ne θ hθ),
      Real.log_one, neg_zero]
  right_inv u hu := by
    have hup := nelsen17_u_pos u hu
    obtain ⟨h0, _⟩ := nelsen17_ratio_mem θ hθ hup u.property.2
    show (1 + ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-(-Real.log
      (((1 + (u : ℝ)) ^ (-θ) - 1) / ((2 : ℝ) ^ (-θ) - 1))))) ^ (-θ⁻¹) - 1 = (u : ℝ)
    rw [neg_neg, Real.exp_log h0, mul_div_cancel₀ _ (nelsen17_den_ne θ hθ), add_sub_cancel,
      ← inv_neg, Real.rpow_rpow_inv (by linarith) (neg_ne_zero.mpr hθ)]
    ring

/-- Nelsen's family 17 for `θ ≠ 0`. -/
noncomputable def nelsen17 (θ : ℝ) (hθ : θ ≠ 0) : Copula 2 :=
  (nelsen17Generator θ hθ).copula

theorem isArchimedean_nelsen17 (θ : ℝ) (hθ : θ ≠ 0) : IsArchimedean (nelsen17 θ hθ) :=
  (nelsen17Generator θ hθ).isArchimedean

/-- The CDF of Nelsen's family 17 on positive coordinates:
`C(u, v) = (1 + ((1 + u)^(-θ) - 1) ((1 + v)^(-θ) - 1) / (2^(-θ) - 1))^(-1/θ) - 1`. -/
theorem cdf_nelsen17 (θ : ℝ) (hθ : θ ≠ 0) (u v : I) (hu : u ≠ 0) (hv : v ≠ 0) :
    (nelsen17 θ hθ).cdf ![u, v] =
      (1 + ((1 + (u : ℝ)) ^ (-θ) - 1) * ((1 + (v : ℝ)) ^ (-θ) - 1) /
        ((2 : ℝ) ^ (-θ) - 1)) ^ (-θ⁻¹) - 1 := by
  obtain ⟨hu0, _⟩ := nelsen17_ratio_mem θ hθ (nelsen17_u_pos u hu) u.property.2
  obtain ⟨hv0, _⟩ := nelsen17_ratio_mem θ hθ (nelsen17_u_pos v hv) v.property.2
  rw [nelsen17, BivariateGenerator.cdf_copula]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [BivariateGenerator.cdf, ite_or_of_not hu hv _ _]
  show (1 + ((2 : ℝ) ^ (-θ) - 1) * Real.exp (-(-Real.log
    (((1 + (u : ℝ)) ^ (-θ) - 1) / ((2 : ℝ) ^ (-θ) - 1)) + -Real.log
    (((1 + (v : ℝ)) ^ (-θ) - 1) / ((2 : ℝ) ^ (-θ) - 1))))) ^ (-θ⁻¹) - 1 = _
  rw [neg_add, neg_neg, neg_neg, Real.exp_add, Real.exp_log hu0, Real.exp_log hv0]
  congr 3
  field_simp [nelsen17_den_ne θ hθ]

/-- Nelsen's family 17 on the whole closed unit square, with grounded zero axes. -/
theorem nelsen17_cdf_full (θ : ℝ) (hθ : θ ≠ 0) (u v : I) :
    (nelsen17 θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        (1 + ((1 + (u : ℝ)) ^ (-θ) - 1) * ((1 + (v : ℝ)) ^ (-θ) - 1) /
          ((2 : ℝ) ^ (-θ) - 1)) ^ (-θ⁻¹) - 1 := by
  by_cases hu : u = 0
  · subst u
    rw [ite_or_of_left rfl _ _]
    exact (nelsen17 θ hθ).cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl
  by_cases hv : v = 0
  · subst v
    rw [ite_or_of_right rfl _ _]
    exact (nelsen17 θ hθ).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
  rw [ite_or_of_not hu hv _ _]
  exact cdf_nelsen17 θ hθ u v hu hv

/-- At `θ = -1` the generator of family 17 is the exponential generator of independence. -/
theorem nelsen17Generator_neg_one :
    nelsen17Generator (-1) (by norm_num) = exponentialGenerator := by
  have h1 : (nelsen17Generator (-1) (by norm_num)).toFun = exponentialGenerator.toFun := by
    funext s
    show (1 + ((2 : ℝ) ^ (-(-1 : ℝ)) - 1) * Real.exp (-s)) ^ (-(-1 : ℝ)⁻¹) - 1 = Real.exp (-s)
    norm_num
  have h2 : (nelsen17Generator (-1) (by norm_num)).invFun = exponentialGenerator.invFun := by
    funext u
    show -Real.log (((1 + (u : ℝ)) ^ (-(-1 : ℝ)) - 1) / ((2 : ℝ) ^ (-(-1 : ℝ)) - 1)) =
      -Real.log (u : ℝ)
    norm_num
  cases h : nelsen17Generator (-1) (by norm_num)
  cases h' : exponentialGenerator
  rw [h, h'] at h1 h2
  simp only at h1 h2
  subst h1 h2
  rfl

/-- `C_{-1} = Π`: at `θ = -1` Nelsen's family 17 is independence. -/
@[simp] theorem nelsen17_neg_one : nelsen17 (-1) (by norm_num) = independence 2 := by
  rw [nelsen17, nelsen17Generator_neg_one, exponentialGenerator_copula]

end ProbabilityTheory.Copula
