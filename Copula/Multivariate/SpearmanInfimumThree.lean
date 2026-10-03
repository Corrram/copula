/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Multivariate.SpearmanInfimumDual
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The lower bound of trivariate Spearman's rho in closed form

For `d = 3` the dual bound of `Copula.Multivariate.SpearmanInfimumDual` has the closed form

`L₃(c) = c (1 - 2c)² log((1 - 2c)/c) - 2c + 31c²/2 - 36c³ + 27c⁴`   (`dualBound_three`),

valid for `0 < c ≤ 1/6`, so that `∫ C dΠ ≥ L₃(c)` and `ρ₃(C) = 8 ∫ C dΠ - 1 ≥ 8 L₃(c) - 1`
for every 3-copula (`dualBoundThree_le_integral_cdf`, `le_multivariateSpearmanRho_three`).

* The optimal parameter solves `log((1 - 2c)/c) = 3 - 9c` (the stationarity condition of `L₃`,
  equivalently Bernard–Jiang–Wang's `H(c) = D(c)` for the exponential distribution). Such a root
  `c₃ ∈ (1/12, 1/6)` exists (`exists_optimal_parameter`), and there the bound is the polynomial
  `m₃ = c₃ - 11c₃²/2 + 12c₃³ - 9c₃⁴` (`dualBoundThree_eq_of_optimal`,
  `le_multivariateSpearmanRho_three_optimal`). Numerically `c₃ ≈ 0.0945415778`,
  `m₃ ≈ 0.0548032411` and `8m₃ - 1 ≈ -0.5615740714`.
* A certified numerical consequence (`neg_056158_le_multivariateSpearmanRho_three`):
  `ρ₃(C) ≥ -0.56158` for every 3-copula, from `c = 7/74` and `log(60/7) > 2.14843`.

Together with the explicit copula of `Copula.Multivariate.SpearmanInfimumWitness`
(`ρ₃ = -631/1125 ≈ -0.560889`) this pins the infimum of `ρ₃` to `[-0.56158, -0.560888]`;
by the convex-order theory of Wang–Wang (2011) and Bernard–Jiang–Wang (2014) the infimum is
`8m₃ - 1` and is attained (not formalized).
-/

open MeasureTheory Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

namespace SpearmanInfimum

/-- The closed form `L₃(c) = c (1-2c)² log((1-2c)/c) - 2c + 31c²/2 - 36c³ + 27c⁴`. -/
noncomputable def dualBoundThree (c : ℝ) : ℝ :=
  c * (1 - 2 * c) ^ 2 * Real.log ((1 - 2 * c) / c) - 2 * c + 31 / 2 * c ^ 2 - 36 * c ^ 3 +
    27 * c ^ 4

/-- The antiderivative used to evaluate `L₃`. -/
private noncomputable def antiderThree (x : ℝ) : ℝ :=
  x * (1 - 2 * x) ^ 2 * Real.log (1 - 2 * x) + x ^ 2 - 4 / 3 * x ^ 3 +
    (-x + 11 / 2 * x ^ 2 - 12 * x ^ 3 + 9 * x ^ 4)

private theorem hasDerivAt_antiderThree {x : ℝ} (hx : x < 1 / 2) :
    HasDerivAt antiderThree (levelDeriv 3 x * (Real.log (1 - ((3 : ℕ) - 1) * x) + (3 : ℕ) * x - 1))
      x := by
  have hb : (1 : ℝ) - 2 * x ≠ 0 := by linarith
  have h1 : HasDerivAt (fun y : ℝ => 1 - 2 * y) (-2) x := by
    simpa using ((hasDerivAt_id x).const_mul 2).const_sub 1
  have h2 := ((hasDerivAt_id x).mul (h1.pow 2)).mul (h1.log hb)
  have h := (((h2.add (hasDerivAt_pow 2 x)).sub ((hasDerivAt_pow 3 x).const_mul (4 / 3 : ℝ))).add
    (((((hasDerivAt_id x).neg.add ((hasDerivAt_pow 2 x).const_mul (11 / 2 : ℝ))).sub
      ((hasDerivAt_pow 3 x).const_mul (12 : ℝ))).add ((hasDerivAt_pow 4 x).const_mul (9 : ℝ)))))
  unfold antiderThree levelDeriv
  convert h using 1
  · funext y
    simp only [id, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.pow_apply]
  · simp only [id, Pi.mul_apply, Pi.pow_apply]
    push_cast
    field_simp
    ring_nf

/-- **Closed form of the dual bound for `d = 3`**: `dualBound 3 c = L₃(c)` for `0 < c ≤ 1/6`. -/
theorem dualBound_three {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 6) :
    dualBound 3 c = dualBoundThree c := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) c, HasDerivAt antiderThree
      (levelDeriv 3 x * (Real.log (1 - ((3 : ℕ) - 1) * x) + (3 : ℕ) * x - 1)) x := by
    intro x hx
    rw [uIcc_of_le hc0.le] at hx
    exact hasDerivAt_antiderThree (by linarith [hx.2])
  have hint : IntervalIntegrable (fun x => levelDeriv 3 x *
      (Real.log (1 - ((3 : ℕ) - 1) * x) + (3 : ℕ) * x - 1)) volume 0 c := by
    apply ContinuousOn.intervalIntegrable
    apply (continuous_levelDeriv 3).continuousOn.mul
    refine ContinuousOn.sub (ContinuousOn.add (ContinuousOn.log (by fun_prop) ?_) (by fun_prop))
      continuousOn_const
    intro x hx
    rw [uIcc_of_le hc0.le] at hx
    push_cast
    linarith [hx.2]
  unfold dualBound
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hb : 0 < 1 - 2 * c := by linarith
  have hlev : level 3 c = c * (1 - 2 * c) ^ 2 := by
    unfold level
    norm_num
  rw [hlev, Real.log_mul hc0.ne' (pow_pos hb 2).ne', Real.log_pow]
  unfold antiderThree dualBoundThree
  rw [Real.log_div hb.ne' hc0.ne']
  push_cast
  norm_num
  ring

/-- **The dual lower bound for `d = 3`**: `∫ C dΠ ≥ L₃(c)` for `0 < c ≤ 1/6`. -/
theorem dualBoundThree_le_integral_cdf {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 6) (C : Copula 3) :
    dualBoundThree c ≤ ∫ u, C.cdf u ∂(independence 3).toMeasure := by
  rw [← dualBound_three hc0 hc]
  exact dualBound_le_integral_cdf (by norm_num) hc0.le (by push_cast; linarith) C

/-- `ρ₃(C) = 8 ∫ C dΠ - 1`. -/
theorem multivariateSpearmanRho_three_eq (C : Copula 3) :
    C.multivariateSpearmanRho = 8 * (∫ u, C.cdf u ∂(independence 3).toMeasure) - 1 := by
  rw [multivariateSpearmanRho]
  norm_num

/-- `L₃` at a root of the stationarity equation `log((1 - 2c)/c) = 3 - 9c`. -/
theorem dualBoundThree_eq_of_optimal {c : ℝ} (h : Real.log ((1 - 2 * c) / c) = 3 - 9 * c) :
    dualBoundThree c = c - 11 / 2 * c ^ 2 + 12 * c ^ 3 - 9 * c ^ 4 := by
  unfold dualBoundThree
  rw [h]
  ring

private theorem exp_two_quarter_lt_ten : Real.exp (9 / 4) < 10 := by
  have he := Real.exp_one_lt_d9
  have hq := Real.exp_bound_div_one_sub_of_interval (x := 1 / 4) (by norm_num) (by norm_num)
  have hsplit : Real.exp (9 / 4) = Real.exp 1 * Real.exp 1 * Real.exp (1 / 4) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  rw [hsplit]
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  have h1 : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 := by
    nlinarith
  have h2 : 0 < Real.exp (1 / 4) := Real.exp_pos _
  calc Real.exp 1 * Real.exp 1 * Real.exp (1 / 4) < 2.7182818286 * 2.7182818286 *
        Real.exp (1 / 4) := mul_lt_mul_of_pos_right h1 h2
    _ ≤ 2.7182818286 * 2.7182818286 * (1 / (1 - 1 / 4)) :=
        mul_le_mul_of_nonneg_left hq (by norm_num)
    _ < 10 := by norm_num

/-- **The optimal parameter exists**: some `c₃ ∈ (1/12, 1/6)` solves
`log((1 - 2c)/c) = 3 - 9c`. -/
theorem exists_optimal_parameter :
    ∃ c ∈ Ioo (1 / 12 : ℝ) (1 / 6), Real.log ((1 - 2 * c) / c) = 3 - 9 * c := by
  set f : ℝ → ℝ := fun c => Real.log ((1 - 2 * c) / c) - (3 - 9 * c) with hf
  have hcont : ContinuousOn f (Icc (1 / 12) (1 / 6)) := by
    apply ContinuousOn.sub _ (by fun_prop)
    apply ContinuousOn.log (ContinuousOn.div (by fun_prop) (by fun_prop) ?_) ?_
    · intro x hx; exact (show (0 : ℝ) < x by linarith [hx.1]).ne'
    · intro x hx
      exact (div_pos (by linarith [hx.2]) (by linarith [hx.1])).ne'
  have hlo : 0 < f (1 / 12) := by
    simp only [hf]
    have : (1 - 2 * (1 / 12 : ℝ)) / (1 / 12) = 10 := by norm_num
    rw [this]
    have h10 : 9 / 4 < Real.log 10 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).2 exp_two_quarter_lt_ten
    linarith
  have hhi : f (1 / 6) < 0 := by
    simp only [hf]
    have : (1 - 2 * (1 / 6 : ℝ)) / (1 / 6) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  -- intermediate value theorem for the decreasing function `f`
  have hivt := intermediate_value_Icc' (show (1 / 12 : ℝ) ≤ 1 / 6 by norm_num) hcont
  obtain ⟨c, hc, hfc⟩ := hivt ⟨hhi.le, hlo.le⟩
  refine ⟨c, ⟨?_, ?_⟩, by simp only [hf] at hfc; linarith⟩
  · rcases hc.1.eq_or_lt with h | h
    · rw [← h] at hfc; linarith
    · exact h
  · rcases hc.2.eq_or_lt with h | h
    · rw [h] at hfc; linarith
    · exact h

/-- **The optimal dual bound**: with `c₃` a root of `log((1-2c)/c) = 3 - 9c` in `(0, 1/6]`,
`ρ₃(C) ≥ 8 (c₃ - 11c₃²/2 + 12c₃³ - 9c₃⁴) - 1 ≈ -0.5615741` for every 3-copula. -/
theorem le_multivariateSpearmanRho_three_optimal {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 6)
    (hopt : Real.log ((1 - 2 * c) / c) = 3 - 9 * c) (C : Copula 3) :
    8 * (c - 11 / 2 * c ^ 2 + 12 * c ^ 3 - 9 * c ^ 4) - 1 ≤ C.multivariateSpearmanRho := by
  have h := dualBoundThree_le_integral_cdf hc0 hc C
  rw [dualBoundThree_eq_of_optimal hopt] at h
  rw [multivariateSpearmanRho_three_eq]
  linarith

/-- The bound `ρ₃(C) ≥ 8 L₃(c) - 1` for `0 < c ≤ 1/6`. -/
theorem le_multivariateSpearmanRho_three {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 6) (C : Copula 3) :
    8 * dualBoundThree c - 1 ≤ C.multivariateSpearmanRho := by
  have h := dualBoundThree_le_integral_cdf hc0 hc C
  rw [multivariateSpearmanRho_three_eq]
  linarith

private theorem exp_lt_sixty_sevenths : Real.exp 2.14843 < 60 / 7 := by
  have he := Real.exp_one_lt_d9
  have hb := Real.exp_bound (x := 0.14843) (by norm_num [abs_of_pos]) (n := 6) (by norm_num)
  have hsplit : Real.exp 2.14843 = Real.exp 1 * Real.exp 1 * Real.exp 0.14843 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  rw [hsplit]
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  have h1 : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 := by nlinarith
  have h2 : Real.exp 0.14843 ≤ 1.160013 := by
    have := (abs_le.1 hb).2
    norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at this
    linarith
  have h3 : 0 < Real.exp 0.14843 := Real.exp_pos _
  calc Real.exp 1 * Real.exp 1 * Real.exp 0.14843 < 2.7182818286 * 2.7182818286 *
        Real.exp 0.14843 := mul_lt_mul_of_pos_right h1 h3
    _ ≤ 2.7182818286 * 2.7182818286 * 1.160013 := mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ < 60 / 7 := by norm_num

/-- **Certified numerical lower bound**: `ρ₃(C) ≥ -0.56158` for every 3-copula (from `c = 7/74`).
The exact infimum is `≈ -0.5615741`; in particular no 3-copula has `ρ₃ ≤ -0.5616`. -/
theorem neg_056158_le_multivariateSpearmanRho_three (C : Copula 3) :
    (-0.56158 : ℝ) ≤ C.multivariateSpearmanRho := by
  have h := le_multivariateSpearmanRho_three (c := 7 / 74) (by norm_num) (by norm_num) C
  have hlog : 2.14843 < Real.log (60 / 7) :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 exp_lt_sixty_sevenths
  have hval : (1 - 2 * (7 / 74 : ℝ)) / (7 / 74) = 60 / 7 := by norm_num
  unfold dualBoundThree at h
  rw [hval] at h
  have hq : (0 : ℝ) < 7 / 74 * (1 - 2 * (7 / 74)) ^ 2 := by norm_num
  have := mul_lt_mul_of_pos_left hlog hq
  norm_num at h this ⊢
  linarith

end SpearmanInfimum

end ProbabilityTheory.Copula
