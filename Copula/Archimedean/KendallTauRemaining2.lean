/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.KendallTauIntegral
import Copula.Families.NelsenTable.N21
import Copula.Families.NelsenTable.N22
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! # Kendall's tau of families 21 and 22 of Nelsen's Table 4.1

Explicit integral forms of `τ = 1 + 4 ∫₀¹ φ(t) / φ'(t) dt` (Nelsen, Corollary 5.1.4,
`BivariateGenerator.kendallTau_eq_of_hasDerivAt`) for the two non-strict families with
non-elementary Kendall integral:

* family 4.2.21, `θ ≥ 1`, `φ(t) = 1 − (1 − (1 − t)^θ)^{1/θ}`, with `w(t) = 1 − (1 − t)^θ`:
  `τ = 1 − 4 ∫₀¹ (1 − t)^{1−θ} w(t)^{1 − 1/θ} (1 − w(t)^{1/θ}) dt` (`kendallTau_nelsen21`);
* family 4.2.22, `0 < θ ≤ 1`, `φ(t) = arcsin (1 − t^θ)`:
  `τ = 1 − (4/θ) ∫₀¹ t^{1 − θ/2} √(2 − t^θ) arcsin (1 − t^θ) dt` (`kendallTau_nelsen22`).
-/

open MeasureTheory Set Filter
open scoped unitInterval

namespace ProbabilityTheory.Copula

open KendallTauIntegral

/-- Nelsen, Table 4.1, family 21 (`θ ≥ 1`), with `w(t) = 1 − (1 − t)^θ`:
`τ = 1 − 4 ∫₀¹ (1 − t)^{1−θ} w(t)^{1 − 1/θ} (1 − w(t)^{1/θ}) dt`. -/
theorem kendallTau_nelsen21 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen21 θ hθ).kendallTau = 1 - 4 * ∫ t in (0 : ℝ)..1,
      (1 - t) ^ (1 - θ) * (1 - (1 - t) ^ θ) ^ (1 - θ⁻¹) *
        (1 - (1 - (1 - t) ^ θ) ^ θ⁻¹) := by
  have hθ0 : 0 < θ := by linarith
  have hs : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < 1 - t := fun t ht => by linarith [ht.2]
  have hw : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < 1 - (1 - t) ^ θ := fun t ht => by
    have := Real.rpow_lt_one (hs t ht).le (by linarith [ht.1]) hθ0
    linarith
  rw [nelsen21, BivariateGenerator.kendallTau_eq_of_hasDerivAt
    (φ := fun t => 1 - (1 - (1 - t) ^ θ) ^ θ⁻¹)
    (φ' := fun t => -((1 - (1 - t) ^ θ) ^ (θ⁻¹ - 1) * (1 - t) ^ (θ - 1)))]
  · rw [integral_congr_Ioo (g := fun t => -((1 - t) ^ (1 - θ) * (1 - (1 - t) ^ θ) ^ (1 - θ⁻¹) *
        (1 - (1 - (1 - t) ^ θ) ^ θ⁻¹))) fun t ht => by
        have h1 := hs t ht
        have h2 := hw t ht
        have hz := (Real.rpow_pos_of_pos h1 (θ - 1)).ne'
        have hy := (Real.rpow_pos_of_pos h2 (θ⁻¹ - 1)).ne'
        have e1 : (1 - t) ^ (θ - 1) * (1 - t) ^ (1 - θ) = 1 := by
          rw [← Real.rpow_add h1, show θ - 1 + (1 - θ) = 0 by ring, Real.rpow_zero]
        have e2 : (1 - (1 - t) ^ θ) ^ (θ⁻¹ - 1) * (1 - (1 - t) ^ θ) ^ (1 - θ⁻¹) = 1 := by
          rw [← Real.rpow_add h2, show θ⁻¹ - 1 + (1 - θ⁻¹) = 0 by ring, Real.rpow_zero]
        rw [div_eq_iff (neg_ne_zero.mpr (mul_ne_zero hy hz))]
        linear_combination
          (-(1 - (1 - (1 - t) ^ θ) ^ θ⁻¹) * ((1 - (1 - t) ^ θ) ^ (θ⁻¹ - 1) *
            (1 - (1 - t) ^ θ) ^ (1 - θ⁻¹))) * e1 - (1 - (1 - (1 - t) ^ θ) ^ θ⁻¹) * e2,
      intervalIntegral.integral_neg]
    ring
  · intro t ht
    rw [invFunReal_of_mem _ ht]
    rfl
  · intro t ht
    have hs' := hs t ht
    have hw' := hw t ht
    have h := ((((hasDerivAt_id' t).const_sub 1).rpow_const (p := θ)
      (Or.inl hs'.ne')).const_sub 1).rpow_const (p := θ⁻¹) (Or.inl hw'.ne') |>.const_sub 1
    refine h.congr_deriv ?_
    have := hθ0.ne'
    field_simp
  · apply ContinuousOn.neg
    apply ContinuousOn.mul
    · exact (continuousOn_const.sub ((continuousOn_const.sub continuousOn_id).rpow_const
        fun t ht => Or.inl (hs t ht).ne')).rpow_const fun t ht => Or.inl (hw t ht).ne'
    · exact (continuousOn_const.sub continuousOn_id).rpow_const fun t ht => Or.inl (hs t ht).ne'
  · intro t ht
    exact neg_ne_zero.mpr (mul_ne_zero (Real.rpow_pos_of_pos (hw t ht) _).ne'
      (Real.rpow_pos_of_pos (hs t ht) _).ne')

/-- Nelsen, Table 4.1, family 22 (`0 < θ ≤ 1`):
`τ = 1 − (4/θ) ∫₀¹ t^{1−θ/2} √(2 − t^θ) arcsin (1 − t^θ) dt`. -/
theorem kendallTau_nelsen22 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    (nelsen22 θ hθ h1).kendallTau = 1 - 4 / θ * ∫ t in (0 : ℝ)..1,
      t ^ (1 - θ / 2) * √(2 - t ^ θ) * Real.arcsin (1 - t ^ θ) := by
  have hX : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < t ^ θ ∧ t ^ θ < 1 := fun t ht =>
    ⟨Real.rpow_pos_of_pos ht.1 θ, Real.rpow_lt_one ht.1.le ht.2 hθ⟩
  have hS : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < 1 - (1 - t ^ θ) ^ 2 := fun t ht => by
    obtain ⟨a, b⟩ := hX t ht
    nlinarith
  have hsq : ∀ t ∈ Ioo (0 : ℝ) 1, √(1 - (1 - t ^ θ) ^ 2) = t ^ (θ / 2) * √(2 - t ^ θ) := by
    intro t ht
    obtain ⟨a, b⟩ := hX t ht
    have hH : t ^ (θ / 2) * t ^ (θ / 2) = t ^ θ := by
      rw [← Real.rpow_add ht.1]; congr 1; ring
    have : 1 - (1 - t ^ θ) ^ 2 = (t ^ (θ / 2)) ^ 2 * (2 - t ^ θ) := by
      rw [sq (t ^ (θ / 2)), hH]; ring
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.rpow_pos_of_pos ht.1 _).le]
  rw [nelsen22, BivariateGenerator.kendallTau_eq_of_hasDerivAt
    (φ := fun t => Real.arcsin (1 - t ^ θ))
    (φ' := fun t => 1 / √(1 - (1 - t ^ θ) ^ 2) * (-(θ * t ^ (θ - 1))))]
  · rw [integral_congr_Ioo (g := fun t => -θ⁻¹ *
        (t ^ (1 - θ / 2) * √(2 - t ^ θ) * Real.arcsin (1 - t ^ θ))) fun t ht => by
        obtain ⟨a, b⟩ := hX t ht
        have h0 := ht.1
        have hz := (Real.rpow_pos_of_pos h0 (θ - 1)).ne'
        have hH := (Real.rpow_pos_of_pos h0 (θ / 2)).ne'
        have hR : 0 < √(2 - t ^ θ) := Real.sqrt_pos.mpr (by linarith)
        have e1 : t ^ (θ - 1) * t ^ (1 - θ / 2) = t ^ (θ / 2) := by
          rw [← Real.rpow_add h0]; congr 1; ring
        have hθ0 := hθ.ne'
        rw [hsq t ht]
        rw [div_eq_iff (mul_ne_zero (by positivity) (neg_ne_zero.mpr (mul_ne_zero hθ0 hz)))]
        have hQ := (Real.rpow_pos_of_pos h0 (1 - θ / 2)).ne'
        rw [← e1]
        generalize t ^ (1 - θ / 2) = Q at *
        generalize t ^ (θ - 1) = P at *
        generalize t ^ (θ / 2) = H at *
        field_simp,
      intervalIntegral.integral_const_mul]
    ring
  · intro t ht
    rw [invFunReal_of_mem _ ht, nelsen22Generator_invFun]
  · intro t ht
    obtain ⟨a, b⟩ := hX t ht
    exact (Real.hasDerivAt_arcsin (x := 1 - t ^ θ) (by linarith) (by linarith)).comp t
      ((Real.hasDerivAt_rpow_const (p := θ) (Or.inl ht.1.ne')).const_sub 1)
  · apply ContinuousOn.mul
    · apply continuousOn_const.div
      · exact Real.continuous_sqrt.comp_continuousOn (continuousOn_const.sub
          ((continuousOn_const.sub (continuousOn_id.rpow_const
            fun t ht => Or.inl ht.1.ne')).pow 2))
      · exact fun t ht => (Real.sqrt_pos.mpr (hS t ht)).ne'
    · exact (continuousOn_const.mul (continuousOn_id.rpow_const
        fun t ht => Or.inl ht.1.ne')).neg
  · intro t ht
    exact mul_ne_zero (one_div_ne_zero (Real.sqrt_pos.mpr (hS t ht)).ne')
      (neg_ne_zero.mpr (mul_ne_zero hθ.ne' (Real.rpow_pos_of_pos ht.1 _).ne'))

end ProbabilityTheory.Copula
