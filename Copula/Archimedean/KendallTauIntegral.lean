/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.KendallTauGenerator
import Copula.Families.Joe
import Copula.Families.NelsenTable.N9
import Copula.Families.NelsenTable.N13
import Copula.Families.NelsenTable.N19
import Copula.Families.NelsenTable.N20

/-! # Kendall's tau of Table 4.1 families as explicit integrals

For several families of Nelsen, *An Introduction to Copulas*, second edition, Table 4.1, the
Kendall integral `τ = 1 + 4 ∫₀¹ φ(t) / φ'(t) dt` (Corollary 5.1.4,
`BivariateGenerator.kendallTau_eq_of_hasDerivAt`) is not elementary (it involves exponential
integrals, incomplete gamma functions or digamma values). This file records the explicit
integral form for each of them:

* family 4.2.6 (Joe), `θ ≥ 1`:
  `τ = 1 + (4/θ) ∫₀¹ (1 − (1−t)^θ) log(1 − (1−t)^θ) / (1−t)^{θ−1} dt` (`kendallTau_joe`);
* family 4.2.9, `0 < θ ≤ 1`: `τ = 1 − (4/θ) ∫₀¹ t (1 − θ log t) log(1 − θ log t) dt`
  (`kendallTau_nelsen9`);
* family 4.2.13, `θ > 0`: `τ = 1 − (4/θ) ∫₀¹ t ((1 − log t) − (1 − log t)^{1−θ}) dt`
  (`kendallTau_nelsen13`);
* family 4.2.19, `θ > 0`: `τ = 1 − (4/θ) ∫₀¹ t² (1 − e^{θ − θ/t}) dt` (`kendallTau_nelsen19`);
* family 4.2.20, `θ > 0`: `τ = 1 − (4/θ) ∫₀¹ t^{θ+1} (1 − e^{1 − t^{−θ}}) dt`
  (`kendallTau_nelsen20`).
-/

open MeasureTheory Set Filter
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace KendallTauIntegral

/-- Two integrands that agree on `(0, 1)` have the same integral over `[0, 1]`. -/
theorem integral_congr_Ioo {f g : ℝ → ℝ} (h : ∀ t ∈ Ioo (0 : ℝ) 1, f t = g t) :
    (∫ t in (0 : ℝ)..1, f t) = ∫ t in (0 : ℝ)..1, g t := by
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

/-- The real extension of a generator at an interior point is its value there. -/
theorem invFunReal_of_mem (g : BivariateGenerator) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    g.invFunReal t = g.invFun ⟨t, ht.1.le, ht.2.le⟩ := by
  rw [BivariateGenerator.invFunReal, projIcc_of_mem _ ⟨ht.1.le, ht.2.le⟩]

theorem log_neg {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : Real.log t < 0 :=
  Real.log_neg ht.1 ht.2

end KendallTauIntegral

open KendallTauIntegral

/-- Nelsen, Table 4.1, family 9 (`0 < θ ≤ 1`):
`τ = 1 − (4/θ) ∫₀¹ t (1 − θ log t) log(1 − θ log t) dt`. -/
theorem kendallTau_nelsen9 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    (nelsen9 θ hθ h1).kendallTau = 1 - 4 / θ * ∫ t in (0 : ℝ)..1,
      t * (1 - θ * Real.log t) * Real.log (1 - θ * Real.log t) := by
  have hq : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < 1 - θ * Real.log t := fun t ht => by
    nlinarith [log_neg ht]
  rw [nelsen9, BivariateGenerator.kendallTau_eq_of_hasDerivAt
    (φ := fun t => Real.log (1 - θ * Real.log t))
    (φ' := fun t => -θ / (t * (1 - θ * Real.log t)))]
  · rw [integral_congr_Ioo (g := fun t => -θ⁻¹ *
        (t * (1 - θ * Real.log t) * Real.log (1 - θ * Real.log t))) fun t ht => by
        have h0 := ht.1.ne'
        have hq0 := (hq t ht).ne'
        field_simp,
      intervalIntegral.integral_const_mul]
    ring
  · intro t ht
    rw [invFunReal_of_mem _ ht]
    rfl
  · intro t ht
    have h := (((Real.hasDerivAt_log ht.1.ne').const_mul θ).const_sub 1).log (hq t ht).ne'
    refine h.congr_deriv ?_
    have := (hq t ht).ne'
    field_simp
  · apply continuousOn_const.div
    · exact continuousOn_id.mul (continuousOn_const.sub
        (continuousOn_const.mul (Real.continuousOn_log.mono fun t ht => ht.1.ne')))
    · exact fun t ht => mul_ne_zero ht.1.ne' (hq t ht).ne'
  · intro t ht
    exact div_ne_zero (neg_ne_zero.mpr hθ.ne') (mul_ne_zero ht.1.ne' (hq t ht).ne')

/-- Nelsen, Table 4.1, family 13 (`θ > 0`):
`τ = 1 − (4/θ) ∫₀¹ t ((1 − log t) − (1 − log t)^{1−θ}) dt` (at `θ = 1`, independence,
the integrand is `−t log t` and `τ = 0`). -/
theorem kendallTau_nelsen13 (θ : ℝ) (hθ : 0 < θ) :
    (nelsen13 θ hθ).kendallTau = 1 - 4 / θ * ∫ t in (0 : ℝ)..1,
      t * ((1 - Real.log t) - (1 - Real.log t) ^ (1 - θ)) := by
  have hb : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < 1 - Real.log t := fun t ht => by
    linarith [log_neg ht]
  rw [nelsen13, BivariateGenerator.kendallTau_eq_of_hasDerivAt
    (φ := fun t => (1 - Real.log t) ^ θ - 1)
    (φ' := fun t => -θ * (1 - Real.log t) ^ (θ - 1) / t)]
  · rw [integral_congr_Ioo (g := fun t => -θ⁻¹ *
        (t * ((1 - Real.log t) - (1 - Real.log t) ^ (1 - θ)))) fun t ht => by
        have hbt := hb t ht
        have h0 := ht.1.ne'
        have hr := (Real.rpow_pos_of_pos hbt (θ - 1)).ne'
        have e1 : (1 - Real.log t) ^ θ = (1 - Real.log t) * (1 - Real.log t) ^ (θ - 1) := by
          have he : (1 - Real.log t) ^ θ = (1 - Real.log t) ^ ((1 : ℝ) + (θ - 1)) := by
            congr 1; ring
          rw [he, Real.rpow_add hbt, Real.rpow_one]
        have e2 : (1 - Real.log t) ^ (1 - θ) * (1 - Real.log t) ^ (θ - 1) = 1 := by
          rw [← Real.rpow_add hbt, show 1 - θ + (θ - 1) = 0 by ring, Real.rpow_zero]
        rw [div_eq_iff (div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hθ.ne') hr) h0), e1]
        field_simp
        linear_combination e2,
      intervalIntegral.integral_const_mul]
    ring
  · intro t ht
    rw [invFunReal_of_mem _ ht]
    rfl
  · intro t ht
    have h := (((Real.hasDerivAt_log ht.1.ne').const_sub 1).rpow_const
      (p := θ) (Or.inl (hb t ht).ne')).sub_const 1
    refine h.congr_deriv ?_
    field_simp
  · apply ContinuousOn.div _ continuousOn_id fun t ht => ht.1.ne'
    exact continuousOn_const.mul ((continuousOn_const.sub
      (Real.continuousOn_log.mono fun t ht => ht.1.ne')).rpow_const
        fun t ht => Or.inl (hb t ht).ne')
  · intro t ht
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hθ.ne')
      (Real.rpow_pos_of_pos (hb t ht) _).ne') ht.1.ne'

/-- Nelsen, Table 4.1, family 19 (`θ > 0`): `τ = 1 − (4/θ) ∫₀¹ t² (1 − e^{θ − θ/t}) dt`. -/
theorem kendallTau_nelsen19 (θ : ℝ) (hθ : 0 < θ) :
    (nelsen19 θ hθ).kendallTau = 1 - 4 / θ * ∫ t in (0 : ℝ)..1,
      t ^ 2 * (1 - Real.exp (θ - θ / t)) := by
  rw [nelsen19, BivariateGenerator.kendallTau_eq_of_hasDerivAt
    (φ := fun t => Real.exp (θ / t) - Real.exp θ)
    (φ' := fun t => -θ * Real.exp (θ / t) / t ^ 2)]
  · rw [integral_congr_Ioo (g := fun t => -θ⁻¹ * (t ^ 2 * (1 - Real.exp (θ - θ / t))))
        fun t ht => by
        have h0 := ht.1.ne'
        have he := (Real.exp_pos (θ / t)).ne'
        rw [Real.exp_sub]
        field_simp,
      intervalIntegral.integral_const_mul]
    ring
  · intro t ht
    rw [invFunReal_of_mem _ ht]
    rfl
  · intro t ht
    have h0 := ht.1.ne'
    have h := (((hasDerivAt_inv h0).const_mul θ).exp).sub_const (Real.exp θ)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
    · rw [← div_eq_mul_inv]
      field_simp
    · simp only [div_eq_mul_inv]
  · apply ContinuousOn.div _ (by fun_prop) fun t ht => pow_ne_zero 2 ht.1.ne'
    exact continuousOn_const.mul (Real.continuous_exp.comp_continuousOn
      (continuousOn_const.div continuousOn_id fun t ht => ht.1.ne'))
  · intro t ht
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hθ.ne') (Real.exp_pos _).ne')
      (pow_ne_zero 2 ht.1.ne')

/-- Nelsen, Table 4.1, family 20 (`θ > 0`):
`τ = 1 − (4/θ) ∫₀¹ t^{θ+1} (1 − e^{1 − t^{−θ}}) dt`. -/
theorem kendallTau_nelsen20 (θ : ℝ) (hθ : 0 < θ) :
    (nelsen20 θ hθ).kendallTau = 1 - 4 / θ * ∫ t in (0 : ℝ)..1,
      t ^ (θ + 1) * (1 - Real.exp (1 - t ^ (-θ))) := by
  rw [nelsen20, BivariateGenerator.kendallTau_eq_of_hasDerivAt
    (φ := fun t => Real.exp (t ^ (-θ)) - Real.exp 1)
    (φ' := fun t => -θ * t ^ (-θ - 1) * Real.exp (t ^ (-θ)))]
  · rw [integral_congr_Ioo (g := fun t => -θ⁻¹ * (t ^ (θ + 1) * (1 - Real.exp (1 - t ^ (-θ)))))
        fun t ht => by
        have he := (Real.exp_pos (t ^ (-θ))).ne'
        have hr := (Real.rpow_pos_of_pos ht.1 (-θ - 1)).ne'
        have e1 : t ^ (θ + 1) * t ^ (-θ - 1) = 1 := by
          rw [← Real.rpow_add ht.1, show θ + 1 + (-θ - 1) = 0 by ring, Real.rpow_zero]
        have e2 : Real.exp (1 - t ^ (-θ)) * Real.exp (t ^ (-θ)) = Real.exp 1 := by
          rw [← Real.exp_add, sub_add_cancel]
        rw [div_eq_iff (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hθ.ne') hr) he)]
        field_simp
        linear_combination (Real.exp 1 - Real.exp (t ^ (-θ))) * e1 +
          (t ^ (θ + 1) * t ^ (-θ - 1)) * e2,
      intervalIntegral.integral_const_mul]
    ring
  · intro t ht
    rw [invFunReal_of_mem _ ht]
    rfl
  · intro t ht
    have h := ((Real.hasDerivAt_rpow_const (p := -θ) (Or.inl ht.1.ne')).exp).sub_const
      (Real.exp 1)
    refine h.congr_deriv ?_
    ring
  · apply ContinuousOn.mul
    · exact continuousOn_const.mul (continuousOn_id.rpow_const fun t ht => Or.inl ht.1.ne')
    · exact Real.continuous_exp.comp_continuousOn
        (continuousOn_id.rpow_const fun t ht => Or.inl ht.1.ne')
  · intro t ht
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hθ.ne') (Real.rpow_pos_of_pos ht.1 _).ne')
      (Real.exp_pos _).ne'

/-- Nelsen, Table 4.1, family 6 (Joe, `θ ≥ 1`):
`τ = 1 + (4/θ) ∫₀¹ (1 − (1−t)^θ) log(1 − (1−t)^θ) / (1−t)^{θ−1} dt`. -/
theorem kendallTau_joe (θ : ℝ) (hθ : 1 ≤ θ) :
    (joe θ hθ).kendallTau = 1 + 4 / θ * ∫ t in (0 : ℝ)..1,
      (1 - (1 - t) ^ θ) * Real.log (1 - (1 - t) ^ θ) / (1 - t) ^ (θ - 1) := by
  have hθ0 : θ ≠ 0 := by linarith
  have hs : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < 1 - t := fun t ht => by linarith [ht.2]
  have hw : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < 1 - (1 - t) ^ θ := fun t ht => by
    have := Real.rpow_lt_one (hs t ht).le (by linarith [ht.1]) (by linarith : 0 < θ)
    linarith
  rw [joe, BivariateGenerator.kendallTau_eq_of_hasDerivAt
    (φ := fun t => -Real.log (1 - (1 - t) ^ θ))
    (φ' := fun t => -(θ * (1 - t) ^ (θ - 1)) / (1 - (1 - t) ^ θ))]
  · rw [integral_congr_Ioo (g := fun t => θ⁻¹ *
        ((1 - (1 - t) ^ θ) * Real.log (1 - (1 - t) ^ θ) / (1 - t) ^ (θ - 1))) fun t ht => by
        have hw0 := (hw t ht).ne'
        have hr := (Real.rpow_pos_of_pos (hs t ht) (θ - 1)).ne'
        field_simp,
      intervalIntegral.integral_const_mul]
    ring
  · intro t ht
    rw [invFunReal_of_mem _ ht]
    rfl
  · intro t ht
    have h := ((((hasDerivAt_id' t).const_sub 1).rpow_const (p := θ)
      (Or.inl (hs t ht).ne')).const_sub 1).log (hw t ht).ne' |>.neg
    refine h.congr_deriv ?_
    field_simp
  · apply ContinuousOn.div
    · exact (continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).rpow_const
        fun t ht => Or.inl (hs t ht).ne')).neg
    · exact continuousOn_const.sub ((continuousOn_const.sub continuousOn_id).rpow_const
        fun t ht => Or.inl (hs t ht).ne')
    · exact fun t ht => (hw t ht).ne'
  · intro t ht
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hθ0
      (Real.rpow_pos_of_pos (hs t ht) _).ne')) (hw t ht).ne'

end ProbabilityTheory.Copula
