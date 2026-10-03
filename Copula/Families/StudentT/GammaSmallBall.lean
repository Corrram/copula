/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Small-ball behaviour of the gamma law

For a gamma law with shape `a > 0` and rate `b > 0` and `q ≥ 0`,

`K e^{-bq} q^a ≤ P(G < q) ≤ K q^a`,  `K = b^a / (a Γ(a))`,

so `P(G < q) ~ K q^a` as `q → 0⁺` (regular variation of the gamma law at the origin). With
`q = m² / x²` this gives `x^{2a} P(G < m²/x²) → K m^{2a}` as `x → ∞`, the form used for the tail
of Student-t scale mixtures `G^{-1/2} Z` (where `P(G^{-1/2} m ≥ x) = P(G ≤ m²/x²)`).

## Main results
* `gammaMeasure_real_Iio_le`, `le_gammaMeasure_real_Iio`: the two-sided small-ball bounds.
* `rpow_mul_gammaMeasure_real_Iio_le`, `tendsto_rpow_mul_gammaMeasure_real_Iio`: the scaled form.

## References
* P. Embrechts, A. McNeil, D. Straumann, *Correlation and dependence in risk management:
  properties and pitfalls*, in: Risk Management: Value at Risk and Beyond, CUP 2002.
-/

open MeasureTheory Set Real Filter
open scoped Topology

namespace ProbabilityTheory

/-- The small-ball constant `b^a / (a Γ(a))` of the gamma law with shape `a` and rate `b`. -/
noncomputable def gammaSmallBallConst (a b : ℝ) : ℝ := b ^ a / (a * Gamma a)

theorem gammaSmallBallConst_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < gammaSmallBallConst a b :=
  div_pos (rpow_pos_of_pos hb a) (mul_pos ha (Gamma_pos_of_pos ha))

/-- `P(G < q)` as an interval integral of the gamma density. -/
theorem gammaMeasure_real_Iio_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {q : ℝ} (hq : 0 ≤ q) :
    (gammaMeasure a b).real (Iio q) = ∫ x in (0 : ℝ)..q, gammaPDFReal a b x := by
  have : IsProbabilityMeasure (gammaMeasure a b) := isProbabilityMeasure_gammaMeasure ha hb
  have : NullSingletonClass (gammaMeasure a b) := by unfold gammaMeasure; infer_instance
  have hzero : ∀ x ∈ Iic q \ Icc 0 q, gammaPDFReal a b x = 0 := by
    intro x hx
    have hx0 : x < 0 := by
      by_contra h
      exact hx.2 ⟨not_lt.1 h, hx.1⟩
    simp [gammaPDFReal, not_le.2 hx0]
  rw [measureReal_congr Iio_ae_eq_Iic, ← cdf_eq_real, cdf_gammaMeasure_eq_integral ha hb,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic Icc_subset_Iic_self hzero,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hq]

private theorem gammaPDFReal_bounds {a b x q : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : x ∈ Icc 0 q) :
    b ^ a / Gamma a * x ^ (a - 1) * exp (-(b * q)) ≤ gammaPDFReal a b x ∧
      gammaPDFReal a b x ≤ b ^ a / Gamma a * x ^ (a - 1) := by
  have hc : 0 ≤ b ^ a / Gamma a * x ^ (a - 1) :=
    mul_nonneg (div_nonneg (rpow_nonneg hb.le a) (Gamma_pos_of_pos ha).le) (rpow_nonneg hx.1 _)
  rw [gammaPDFReal, ite_eq_left_of_eq_true _ _ (eq_true hx.1)]
  refine ⟨mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) hc,
    mul_le_of_le_one_right hc (exp_le_one_iff.2 ?_)⟩
  · nlinarith [hx.2]
  · nlinarith [hx.1]

private theorem intervalIntegrable_gammaKernel {a b : ℝ} (ha : 0 < a) (q : ℝ) :
    IntervalIntegrable (fun x => b ^ a / Gamma a * x ^ (a - 1)) volume 0 q :=
  (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < a - 1)).const_mul _

private theorem integral_gammaKernel {a b : ℝ} (ha : 0 < a) (q : ℝ) :
    ∫ x in (0 : ℝ)..q, b ^ a / Gamma a * x ^ (a - 1) = gammaSmallBallConst a b * q ^ a := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
    sub_add_cancel, zero_rpow ha.ne', sub_zero, gammaSmallBallConst]
  have := (Gamma_pos_of_pos ha).ne'
  field_simp

private theorem intervalIntegrable_gammaPDFReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {q : ℝ}
    (hq : 0 ≤ q) : IntervalIntegrable (gammaPDFReal a b) volume 0 q := by
  refine (intervalIntegrable_gammaKernel (b := b) ha q).mono_fun
    (measurable_gammaPDFReal a b).aestronglyMeasurable ?_
  rw [uIoc_of_le hq]
  refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun x hx => ?_)
  have h := gammaPDFReal_bounds ha hb (Ioc_subset_Icc_self hx)
  change ‖gammaPDFReal a b x‖ ≤ ‖b ^ a / Gamma a * x ^ (a - 1)‖
  rw [Real.norm_of_nonneg (gammaPDFReal_nonneg ha hb x),
    Real.norm_of_nonneg ((gammaPDFReal_nonneg ha hb x).trans h.2)]
  exact h.2

/-- Upper small-ball bound: `P(G < q) ≤ b^a q^a / (a Γ(a))`. -/
theorem gammaMeasure_real_Iio_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {q : ℝ} (hq : 0 ≤ q) :
    (gammaMeasure a b).real (Iio q) ≤ gammaSmallBallConst a b * q ^ a := by
  rw [gammaMeasure_real_Iio_eq ha hb hq, ← integral_gammaKernel ha q]
  exact intervalIntegral.integral_mono_on hq (intervalIntegrable_gammaPDFReal ha hb hq)
    (intervalIntegrable_gammaKernel ha q) fun x hx => (gammaPDFReal_bounds ha hb hx).2

/-- Lower small-ball bound: `b^a q^a e^{-bq} / (a Γ(a)) ≤ P(G < q)`. -/
theorem le_gammaMeasure_real_Iio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {q : ℝ} (hq : 0 ≤ q) :
    gammaSmallBallConst a b * q ^ a * exp (-(b * q)) ≤ (gammaMeasure a b).real (Iio q) := by
  rw [gammaMeasure_real_Iio_eq ha hb hq, ← integral_gammaKernel ha q,
    ← intervalIntegral.integral_mul_const]
  exact intervalIntegral.integral_mono_on hq ((intervalIntegrable_gammaKernel ha q).mul_const _)
    (intervalIntegrable_gammaPDFReal ha hb hq) fun x hx => (gammaPDFReal_bounds ha hb hx).1

/-- `(m²)^a = m^{2a}` for `m ≥ 0`. -/
theorem sq_rpow_eq_rpow_two_mul {m : ℝ} (hm : 0 ≤ m) (a : ℝ) : (m ^ 2) ^ a = m ^ (2 * a) := by
  rw [← rpow_natCast, ← rpow_mul hm]
  norm_num

/-- `x^{2a} (m²/x²)^a = m^{2a}` for `m ≥ 0` and `x > 0`. -/
theorem rpow_mul_div_sq_rpow {m x : ℝ} (hm : 0 ≤ m) (hx : 0 < x) (a : ℝ) :
    x ^ (2 * a) * (m ^ 2 / x ^ 2) ^ a = m ^ (2 * a) := by
  rw [div_rpow (sq_nonneg m) (sq_nonneg x), sq_rpow_eq_rpow_two_mul hm,
    sq_rpow_eq_rpow_two_mul hx.le]
  have := (rpow_pos_of_pos hx (2 * a)).ne'
  field_simp

/-- Scaled upper bound: `x^{2a} P(G < m²/x²) ≤ K m^{2a}`. -/
theorem rpow_mul_gammaMeasure_real_Iio_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {m x : ℝ}
    (hm : 0 ≤ m) (hx : 0 < x) :
    x ^ (2 * a) * (gammaMeasure a b).real (Iio (m ^ 2 / x ^ 2)) ≤
      gammaSmallBallConst a b * m ^ (2 * a) := by
  have h := gammaMeasure_real_Iio_le ha hb (div_nonneg (sq_nonneg m) (sq_nonneg x))
  calc x ^ (2 * a) * (gammaMeasure a b).real (Iio (m ^ 2 / x ^ 2))
      ≤ x ^ (2 * a) * (gammaSmallBallConst a b * (m ^ 2 / x ^ 2) ^ a) :=
        mul_le_mul_of_nonneg_left h (rpow_nonneg hx.le _)
    _ = gammaSmallBallConst a b * m ^ (2 * a) := by
        rw [mul_left_comm, rpow_mul_div_sq_rpow hm hx]

/-- Scaled lower bound: `K m^{2a} e^{-b m²/x²} ≤ x^{2a} P(G < m²/x²)`. -/
theorem le_rpow_mul_gammaMeasure_real_Iio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {m x : ℝ}
    (hm : 0 ≤ m) (hx : 0 < x) :
    gammaSmallBallConst a b * m ^ (2 * a) * exp (-(b * (m ^ 2 / x ^ 2))) ≤
      x ^ (2 * a) * (gammaMeasure a b).real (Iio (m ^ 2 / x ^ 2)) := by
  have h := le_gammaMeasure_real_Iio ha hb (div_nonneg (sq_nonneg m) (sq_nonneg x))
  calc gammaSmallBallConst a b * m ^ (2 * a) * exp (-(b * (m ^ 2 / x ^ 2)))
      = x ^ (2 * a) * (gammaSmallBallConst a b * (m ^ 2 / x ^ 2) ^ a *
          exp (-(b * (m ^ 2 / x ^ 2)))) := by
        rw [← rpow_mul_div_sq_rpow hm hx a]
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (rpow_nonneg hx.le _)

/-- **Regular variation of the gamma law at the origin**, scaled form:
`x^{2a} P(G < m²/x²) → b^a m^{2a} / (a Γ(a))` as `x → ∞`. -/
theorem tendsto_rpow_mul_gammaMeasure_real_Iio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {m : ℝ}
    (hm : 0 ≤ m) :
    Tendsto (fun x : ℝ => x ^ (2 * a) * (gammaMeasure a b).real (Iio (m ^ 2 / x ^ 2))) atTop
      (𝓝 (gammaSmallBallConst a b * m ^ (2 * a))) := by
  have hq : Tendsto (fun x : ℝ => m ^ 2 / x ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  have hexp : Tendsto (fun x : ℝ => gammaSmallBallConst a b * m ^ (2 * a) *
      exp (-(b * (m ^ 2 / x ^ 2)))) atTop (𝓝 (gammaSmallBallConst a b * m ^ (2 * a))) := by
    have hc : Continuous fun q : ℝ => exp (-(b * q)) := by fun_prop
    have h := (hc.tendsto 0).comp hq
    simp only [Function.comp_def, mul_zero, neg_zero, exp_zero] at h
    simpa using h.const_mul (gammaSmallBallConst a b * m ^ (2 * a))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hexp tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact le_rpow_mul_gammaMeasure_real_Iio ha hb hm hx
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact rpow_mul_gammaMeasure_real_Iio_le ha hb hm hx

end ProbabilityTheory
