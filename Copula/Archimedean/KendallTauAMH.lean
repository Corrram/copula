/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.KendallTauFamilies
import Copula.Families.AMH

/-! # Kendall's tau of the Ali–Mikhail–Haq family

For the Ali–Mikhail–Haq family (Nelsen, *An Introduction to Copulas*, second edition,
family 4.2.3), `-1 ≤ θ < 1`, `θ ≠ 0`,
`τ = 1 − 2 (θ + (1 − θ)² log(1 − θ)) / (3 θ²)` (`kendallTau_amh`; Nelsen, Section 5.1.1).

The inverse generator `ψ(s) = (1 − θ) / (eˢ − θ)` is strict and smooth
(`isC1_amhGenerator`). With `w = 1 − θ + θ t`, the Kendall integrand is
`φ(t)/φ'(t) = −t w (log w − log t) / (1 − θ)`, which is integrated with an explicit
antiderivative. For `θ = 0` the family is the independence copula (`amh_zero`), with `τ = 0`.
-/

open MeasureTheory Set Filter
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The derivative of the Ali–Mikhail–Haq inverse generator `(1 − θ) / (eˢ − θ)`. -/
noncomputable def amhGeneratorDeriv (θ : ℝ) (s : ℝ) : ℝ :=
  -(1 - θ) * Real.exp s / (Real.exp s - θ) ^ 2

private theorem amh_exp_sub_pos {θ : ℝ} (hmax : θ < 1) {s : ℝ} (hs : 0 ≤ s) :
    0 < Real.exp s - θ := by
  have := Real.one_le_exp hs
  linarith

/-- The Ali–Mikhail–Haq inverse generator is continuously differentiable on `(0, ∞)`. -/
theorem isC1_amhGenerator (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ < 1) :
    (amhGenerator θ hmin hmax).IsC1 (amhGeneratorDeriv θ) := by
  refine BivariateGenerator.IsC1.of_isStrict (fun s hs => ?_) ?_
  · have hne := (amh_exp_sub_pos hmax hs.le).ne'
    have h := (hasDerivAt_const s (1 - θ)).div ((Real.hasDerivAt_exp s).sub_const θ) hne
    refine h.congr_deriv ?_
    simp only [amhGeneratorDeriv]
    ring
  · apply ContinuousOn.div
    · exact (continuous_const.mul Real.continuous_exp).continuousOn
    · exact ((Real.continuous_exp.sub continuous_const).pow 2).continuousOn
    · intro s hs
      exact pow_ne_zero 2 (amh_exp_sub_pos hmax (le_of_lt hs)).ne'

/-- The antiderivative of `t w (log w − log t)`, `w = a + b t`, used for the AMH integral. -/
private noncomputable def amhPrimitive (a b : ℝ) (t : ℝ) : ℝ :=
  (1 / b ^ 2) * ((a + b * t) ^ 3 / 3 * Real.log (a + b * t) - (a + b * t) ^ 3 / 9 -
      a * ((a + b * t) ^ 2 / 2 * Real.log (a + b * t) - (a + b * t) ^ 2 / 4)) -
    (a / 2 * t * (t * Real.log t) + b / 3 * t ^ 2 * (t * Real.log t) -
      (a * t ^ 2 / 4 + b * t ^ 3 / 9))

private theorem hasDerivAt_amhPrimitive {a b t : ℝ} (hb : b ≠ 0) (ht : t ≠ 0)
    (hw : a + b * t ≠ 0) :
    HasDerivAt (amhPrimitive a b)
      (t * (a + b * t) * (Real.log (a + b * t) - Real.log t)) t := by
  have hwd : HasDerivAt (fun x => a + b * x) b t := by
    simpa using ((hasDerivAt_id t).const_mul b).const_add a
  have hlog := hwd.log hw
  have h3 := (hwd.pow 3).div_const 3
  have h2 := (hwd.pow 2).div_const 2
  have h9 := (hwd.pow 3).div_const 9
  have h4 := (hwd.pow 2).div_const 4
  have hA := ((h3.mul hlog).sub h9).sub ((h2.mul hlog).sub h4 |>.const_mul a)
  have hB := hA.const_mul (1 / b ^ 2)
  have htl := Real.hasDerivAt_mul_log ht
  have hC1 := ((hasDerivAt_id t).const_mul (a / 2)).mul htl
  have hC2 := (((hasDerivAt_pow 2 t).const_mul (b / 3))).mul htl
  have hC3 := ((hasDerivAt_pow 2 t).const_mul (a / 4)).add ((hasDerivAt_pow 3 t).const_mul (b / 9))
  have hD := hB.sub ((hC1.add hC2).sub hC3)
  refine (hD.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  · simp only [id_eq, Nat.cast_ofNat, Pi.pow_apply]
    field_simp
    ring
  · simp only [amhPrimitive, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
    ring

/-- `∫₀¹ t w (log w − log t) dt` for `w = a + b t > 0` on `[0, 1]`, `b ≠ 0`. -/
private theorem integral_amh (a b : ℝ) (hb : b ≠ 0) (ha : 0 < a) (hab : a + b = 1) :
    (∫ t in (0 : ℝ)..1, t * (a + b * t) * (Real.log (a + b * t) - Real.log t)) =
      amhPrimitive a b 1 - amhPrimitive a b 0 := by
  have hwpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < a + b * t := by
    intro t ht
    rcases le_or_gt 0 b with hb0 | hb0
    · nlinarith [ht.1]
    · nlinarith [ht.2]
  have hcont : ContinuousOn (amhPrimitive a b) (Icc 0 1) := by
    have hw : ContinuousOn (fun t : ℝ => a + b * t) (Icc 0 1) := by fun_prop
    have hlogw : ContinuousOn (fun t : ℝ => Real.log (a + b * t)) (Icc 0 1) :=
      hw.log fun t ht => (hwpos t ht).ne'
    have htl : ContinuousOn (fun t : ℝ => t * Real.log t) (Icc 0 1) :=
      Real.continuous_mul_log.continuousOn
    unfold amhPrimitive
    apply ContinuousOn.sub
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.sub
      · exact ((hw.pow 3).div_const 3).mul hlogw |>.sub ((hw.pow 3).div_const 9)
      · exact continuousOn_const.mul (((hw.pow 2).div_const 2).mul hlogw |>.sub
          ((hw.pow 2).div_const 4))
    · apply ContinuousOn.sub
      · exact ((continuousOn_const.mul continuousOn_id).mul htl).add
          ((continuousOn_const.mul (continuousOn_id.pow 2)).mul htl)
      · exact (by fun_prop : Continuous (fun t : ℝ => a * t ^ 2 / 4 + b * t ^ 3 / 9)).continuousOn
  have hint : IntervalIntegrable
      (fun t => t * (a + b * t) * (Real.log (a + b * t) - Real.log t)) volume 0 1 := by
    have hw : ContinuousOn (fun t : ℝ => a + b * t) (uIcc 0 1) := by fun_prop
    have hlogw : ContinuousOn (fun t : ℝ => Real.log (a + b * t)) (uIcc 0 1) :=
      hw.log fun t ht => (hwpos t (by rwa [uIcc_of_le zero_le_one] at ht)).ne'
    have hc : ContinuousOn (fun t => t * (a + b * t) * Real.log (a + b * t) -
        (a + b * t) * (t * Real.log t)) (uIcc 0 1) :=
      ((continuousOn_id.mul hw).mul hlogw).sub
        (hw.mul Real.continuous_mul_log.continuousOn)
    exact (hc.intervalIntegrable).congr (fun t _ => by ring)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont
    (fun t ht => hasDerivAt_amhPrimitive hb ht.1.ne'
      (hwpos t ⟨ht.1.le, ht.2.le⟩).ne') hint

/-- Kendall's tau of the Ali–Mikhail–Haq copula:
`τ = 1 − 2 (θ + (1 − θ)² log(1 − θ)) / (3 θ²)` for `-1 ≤ θ < 1`, `θ ≠ 0`. -/
theorem kendallTau_amh (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ < 1) (hθ : θ ≠ 0) :
    (amh θ hmin hmax.le).kendallTau =
      1 - 2 * (θ + (1 - θ) ^ 2 * Real.log (1 - θ)) / (3 * θ ^ 2) := by
  have ha : 0 < 1 - θ := by linarith
  have hamh : amh θ hmin hmax.le = (amhGenerator θ hmin hmax).copula := by
    rw [amh, dite_eq_right_of_eq_false (eq_false hmax.ne)]
  rw [hamh, (isC1_amhGenerator θ hmin hmax).kendallTau_eq]
  have hident : ∀ t ∈ uIoc (0 : ℝ) 1,
      (amhGenerator θ hmin hmax).invFunReal t *
        amhGeneratorDeriv θ ((amhGenerator θ hmin hmax).invFunReal t) =
      -(1 - θ)⁻¹ * (t * ((1 - θ) + θ * t) * (Real.log ((1 - θ) + θ * t) - Real.log t)) := by
    intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    have hφ : (amhGenerator θ hmin hmax).invFunReal t = Real.log (θ + (1 - θ) / t) :=
      (amhGenerator θ hmin hmax).invFunReal_coe ⟨t, ht.1.le, ht.2⟩
    have hw : 0 < (1 - θ) + θ * t := by
      rcases le_or_gt 0 θ with h0 | h0
      · nlinarith [ht.1]
      · nlinarith [ht.2]
    have ht0 : t ≠ 0 := ht.1.ne'
    have hA : θ + (1 - θ) / t = ((1 - θ) + θ * t) / t := by
      field_simp
      ring
    have hApos : 0 < θ + (1 - θ) / t := by rw [hA]; exact div_pos hw ht.1
    rw [hφ, amhGeneratorDeriv, Real.exp_log hApos, hA, Real.log_div hw.ne' ht.1.ne']
    have hden : ((1 - θ) + θ * t) / t - θ = (1 - θ) / t := by
      field_simp
      ring
    rw [hden]
    field_simp
  rw [intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => hident t ht),
    intervalIntegral.integral_const_mul, integral_amh (1 - θ) θ hθ ha (by ring)]
  simp only [amhPrimitive, mul_one, sub_add_cancel, Real.log_one, mul_zero, add_zero,
    Real.log_zero]
  field_simp
  ring

end ProbabilityTheory.Copula
