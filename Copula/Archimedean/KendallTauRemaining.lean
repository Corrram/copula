/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.KendallTauIntegral
import Copula.Families.NelsenTable.N10
import Copula.Families.NelsenTable.N11
import Copula.Families.NelsenTable.N17

/-! # Kendall's tau of families 10, 11 and 17 of Nelsen's Table 4.1

Explicit integral forms of `τ = 1 + 4 ∫₀¹ φ(t) / φ'(t) dt` (Nelsen, Corollary 5.1.4,
`BivariateGenerator.kendallTau_eq_of_hasDerivAt`) for three families whose Kendall integral is
not elementary:

* family 4.2.10, `0 < θ ≤ 1`, `φ(t) = log (2 t^{−θ} − 1)`:
  `τ = 1 − (2/θ) ∫₀¹ t (2 − t^θ) log (2 t^{−θ} − 1) dt` (`kendallTau_nelsen10`);
* family 4.2.11, `0 < θ ≤ 1/2`, `φ(t) = log (2 − t^θ)`:
  `τ = 1 − (4/θ) ∫₀¹ t^{1−θ} (2 − t^θ) log (2 − t^θ) dt` (`kendallTau_nelsen11`);
* family 4.2.17, `θ ≠ 0`, `φ(t) = −log (((1+t)^{−θ} − 1) / (2^{−θ} − 1))`:
  `τ = 1 − (4/θ) ∫₀¹ (1+t) (1 − (1+t)^θ) log (((1+t)^{−θ} − 1) / (2^{−θ} − 1)) dt`
  (`kendallTau_nelsen17`).
-/

open MeasureTheory Set Filter
open scoped unitInterval

namespace ProbabilityTheory.Copula

open KendallTauIntegral

/-- Nelsen, Table 4.1, family 10 (`0 < θ ≤ 1`):
`τ = 1 − (2/θ) ∫₀¹ t (2 − t^θ) log (2 t^{−θ} − 1) dt`. -/
theorem kendallTau_nelsen10 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    (nelsen10 θ hθ h1).kendallTau = 1 - 2 / θ * ∫ t in (0 : ℝ)..1,
      t * (2 - t ^ θ) * Real.log (2 * t ^ (-θ) - 1) := by
  have hq : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < 2 * t ^ (-θ) - 1 := fun t ht => by
    have := Real.one_lt_rpow_of_pos_of_lt_one_of_neg ht.1 ht.2 (neg_neg_of_pos hθ)
    linarith
  rw [nelsen10, BivariateGenerator.kendallTau_eq_of_hasDerivAt
    (φ := fun t => Real.log (2 * t ^ (-θ) - 1))
    (φ' := fun t => 2 * (-θ * t ^ (-θ - 1)) / (2 * t ^ (-θ) - 1))]
  · rw [integral_congr_Ioo (g := fun t => -(2 * θ)⁻¹ *
        (t * (2 - t ^ θ) * Real.log (2 * t ^ (-θ) - 1))) fun t ht => by
        have h0 := ht.1
        have hq0 := (hq t ht).ne'
        have hz := (Real.rpow_pos_of_pos h0 (-θ - 1)).ne'
        have e1 : t ^ (-θ) * t ^ θ = 1 := by
          rw [← Real.rpow_add h0, neg_add_cancel, Real.rpow_zero]
        have e2 : t ^ (-θ - 1) * t = t ^ (-θ) := by
          rw [← Real.rpow_add_one h0.ne']; congr 1; ring
        have hθ0 := hθ.ne'
        have hX := (Real.rpow_pos_of_pos h0 θ).ne'
        rw [div_eq_iff (div_ne_zero (mul_ne_zero two_ne_zero (mul_ne_zero (neg_ne_zero.mpr hθ0) hz)) hq0)]
        field_simp
        linear_combination (Real.log (2 * t ^ (-θ) - 1) * t ^ θ - 2 * Real.log (2 * t ^ (-θ) - 1)) * e2 +
          Real.log (2 * t ^ (-θ) - 1) * e1,
      intervalIntegral.integral_const_mul]
    field_simp
    ring
  · intro t ht
    rw [invFunReal_of_mem _ ht, nelsen10Generator_invFun]
  · intro t ht
    have h := ((((Real.hasDerivAt_rpow_const (p := -θ) (Or.inl ht.1.ne')).const_mul 2).sub_const
      1).log (hq t ht).ne')
    exact h
  · apply ContinuousOn.div
    · exact continuousOn_const.mul (continuousOn_const.mul
        (continuousOn_id.rpow_const fun t ht => Or.inl ht.1.ne'))
    · exact (continuousOn_const.mul (continuousOn_id.rpow_const
        fun t ht => Or.inl ht.1.ne')).sub continuousOn_const
    · exact fun t ht => (hq t ht).ne'
  · intro t ht
    exact div_ne_zero (mul_ne_zero two_ne_zero (mul_ne_zero (neg_ne_zero.mpr hθ.ne')
      (Real.rpow_pos_of_pos ht.1 _).ne')) (hq t ht).ne'

/-- Nelsen, Table 4.1, family 11 (`0 < θ ≤ 1/2`):
`τ = 1 − (4/θ) ∫₀¹ t^{1−θ} (2 − t^θ) log (2 − t^θ) dt`. -/
theorem kendallTau_nelsen11 (θ : ℝ) (hθ : 0 < θ) (h2 : θ ≤ 1 / 2) :
    (nelsen11 θ hθ h2).kendallTau = 1 - 4 / θ * ∫ t in (0 : ℝ)..1,
      t ^ (1 - θ) * (2 - t ^ θ) * Real.log (2 - t ^ θ) := by
  have hq : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < 2 - t ^ θ := fun t ht => by
    have := Real.rpow_lt_one ht.1.le ht.2 hθ
    linarith
  rw [nelsen11, BivariateGenerator.kendallTau_eq_of_hasDerivAt
    (φ := fun t => Real.log (2 - t ^ θ))
    (φ' := fun t => -(θ * t ^ (θ - 1)) / (2 - t ^ θ))]
  · rw [integral_congr_Ioo (g := fun t => -θ⁻¹ *
        (t ^ (1 - θ) * (2 - t ^ θ) * Real.log (2 - t ^ θ))) fun t ht => by
        have h0 := ht.1
        have hq0 := (hq t ht).ne'
        have hz := (Real.rpow_pos_of_pos h0 (θ - 1)).ne'
        have hw := (Real.rpow_pos_of_pos h0 (1 - θ)).ne'
        have e1 : t ^ (1 - θ) * t ^ (θ - 1) = 1 := by
          rw [← Real.rpow_add h0, show 1 - θ + (θ - 1) = 0 by ring, Real.rpow_zero]
        have hθ0 := hθ.ne'
        rw [div_eq_iff (div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hθ0 hz)) hq0)]
        field_simp
        linear_combination (-(2 - t ^ θ) * Real.log (2 - t ^ θ) * θ -
          Real.log (2 - t ^ θ) * (1 + θ * t ^ θ - 2 * θ)) * e1,
      intervalIntegral.integral_const_mul]
    ring
  · intro t ht
    rw [invFunReal_of_mem _ ht]
    rfl
  · intro t ht
    have h := ((((Real.hasDerivAt_rpow_const (p := θ) (Or.inl ht.1.ne')).const_sub 2)).log
      (hq t ht).ne')
    refine h.congr_deriv ?_
    ring
  · apply ContinuousOn.div
    · exact (continuousOn_const.mul (continuousOn_id.rpow_const
        fun t ht => Or.inl ht.1.ne')).neg
    · exact continuousOn_const.sub (continuousOn_id.rpow_const fun t ht => Or.inl ht.1.ne')
    · exact fun t ht => (hq t ht).ne'
  · intro t ht
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hθ.ne'
      (Real.rpow_pos_of_pos ht.1 _).ne')) (hq t ht).ne'

/-- For `θ ≠ 0` and `t > 0`, the ratio `((1+t)^{−θ} − 1) / (2^{−θ} − 1)` is positive. -/
private theorem nelsen17_ratio_pos (θ : ℝ) (hθ : θ ≠ 0) {t : ℝ} (ht : 0 < t) :
    0 < ((1 + t) ^ (-θ) - 1) / ((2 : ℝ) ^ (-θ) - 1) := by
  rcases hθ.lt_or_gt with h | h
  · apply div_pos
    · have := Real.one_lt_rpow (by linarith : 1 < 1 + t) (neg_pos.mpr h)
      linarith
    · have := Real.one_lt_rpow one_lt_two (neg_pos.mpr h)
      linarith
  · apply div_pos_of_neg_of_neg
    · have := Real.rpow_lt_one_of_one_lt_of_neg (by linarith : 1 < 1 + t) (neg_neg_of_pos h)
      linarith
    · have := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos h)
      linarith

/-- Nelsen, Table 4.1, family 17 (`θ ≠ 0`):
`τ = 1 − (4/θ) ∫₀¹ (1+t) (1 − (1+t)^θ) log (((1+t)^{−θ} − 1) / (2^{−θ} − 1)) dt`. -/
theorem kendallTau_nelsen17 (θ : ℝ) (hθ : θ ≠ 0) :
    (nelsen17 θ hθ).kendallTau = 1 - 4 / θ * ∫ t in (0 : ℝ)..1,
      (1 + t) * (1 - (1 + t) ^ θ) *
        Real.log (((1 + t) ^ (-θ) - 1) / ((2 : ℝ) ^ (-θ) - 1)) := by
  have hb : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < 1 + t := fun t ht => by linarith [ht.1]
  have hd : (2 : ℝ) ^ (-θ) - 1 ≠ 0 := by
    rcases hθ.lt_or_gt with h | h
    · have := Real.one_lt_rpow one_lt_two (neg_pos.mpr h)
      linarith
    · have := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos h)
      linarith
  have hf : ∀ t ∈ Ioo (0 : ℝ) 1, (1 + t) ^ (-θ) - 1 ≠ 0 := fun t ht h => by
    have := (nelsen17_ratio_pos θ hθ ht.1).ne'
    rw [h, zero_div] at this
    exact this rfl
  rw [nelsen17, BivariateGenerator.kendallTau_eq_of_hasDerivAt
    (φ := fun t => -Real.log (((1 + t) ^ (-θ) - 1) / ((2 : ℝ) ^ (-θ) - 1)))
    (φ' := fun t => θ * (1 + t) ^ (-θ - 1) / ((1 + t) ^ (-θ) - 1))]
  · rw [integral_congr_Ioo (g := fun t => -θ⁻¹ *
        ((1 + t) * (1 - (1 + t) ^ θ) *
          Real.log (((1 + t) ^ (-θ) - 1) / ((2 : ℝ) ^ (-θ) - 1)))) fun t ht => by
        have h0 := hb t ht
        have hf0 := hf t ht
        have hz := (Real.rpow_pos_of_pos h0 (-θ - 1)).ne'
        have e1 : (1 + t) ^ (-θ) * (1 + t) ^ θ = 1 := by
          rw [← Real.rpow_add h0, neg_add_cancel, Real.rpow_zero]
        have e2 : (1 + t) ^ (-θ - 1) * (1 + t) = (1 + t) ^ (-θ) := by
          rw [← Real.rpow_add_one h0.ne']; congr 1; ring
        rw [div_eq_iff (div_ne_zero (mul_ne_zero hθ hz) hf0)]
        field_simp
        linear_combination
          (Real.log (((1 + t) ^ (-θ) - 1) / ((2 : ℝ) ^ (-θ) - 1)) * (1 - (1 + t) ^ θ)) * e2 -
          Real.log (((1 + t) ^ (-θ) - 1) / ((2 : ℝ) ^ (-θ) - 1)) * e1,
      intervalIntegral.integral_const_mul]
    ring
  · intro t ht
    rw [invFunReal_of_mem _ ht]
    rfl
  · intro t ht
    have h0 := hb t ht
    have h := (((((hasDerivAt_id' t).const_add 1).rpow_const (p := -θ) (Or.inl h0.ne')).sub_const 1).div_const ((2 : ℝ) ^ (-θ) - 1)).log
      (div_ne_zero (hf t ht) hd) |>.neg
    refine h.congr_deriv ?_
    field_simp
  · apply ContinuousOn.div
    · exact continuousOn_const.mul ((continuousOn_const.add continuousOn_id).rpow_const
        fun t ht => Or.inl (hb t ht).ne')
    · exact ((continuousOn_const.add continuousOn_id).rpow_const
        fun t ht => Or.inl (hb t ht).ne').sub continuousOn_const
    · exact hf
  · intro t ht
    exact div_ne_zero (mul_ne_zero hθ (Real.rpow_pos_of_pos (hb t ht) _).ne') (hf t ht)

end ProbabilityTheory.Copula
