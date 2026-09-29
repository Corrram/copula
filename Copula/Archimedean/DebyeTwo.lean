/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.KendallTauFrankDebye

/-! # The Debye function of order two

`D₂(θ) = (2/θ²) ∫₀^θ t² / (e^t − 1) dt` (Nelsen, *An Introduction to Copulas*, second edition,
Example 5.8; Genest 1987). Together with the Debye function of order one (`debyeOne`) it gives
Spearman's rho of Frank's copula, `ρ = 1 − (12/θ)(D₁(θ) − D₂(θ))`
(`Copula.Archimedean.SpearmanRhoFrank`).

Basic properties: integrability of the integrand (`intervalIntegrable_debyeTwo_integrand`),
non-negativity for `θ ≥ 0` (`debyeTwo_nonneg`) and the reflection identity
`D₂(−x) = D₂(x) + 2x/3` (`debyeTwo_neg`).
-/

open MeasureTheory Set

namespace ProbabilityTheory.Copula

/-- The Debye function of order two, `D₂(θ) = (2/θ²) ∫₀^θ t² / (e^t − 1) dt`. -/
noncomputable def debyeTwo (θ : ℝ) : ℝ := 2 / θ ^ 2 * ∫ t in (0 : ℝ)..θ, t ^ 2 / (Real.exp t - 1)

/-- The integrand `t²/(e^t − 1)` of the second Debye function is interval integrable on
`[0, x]`. -/
theorem intervalIntegrable_debyeTwo_integrand {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun t => t ^ 2 / (Real.exp t - 1)) volume 0 x := by
  have h := (intervalIntegrable_debye_integrand hx).mul_continuousOn
    (g := fun t : ℝ => t) continuous_id.continuousOn
  refine h.congr fun t _ => ?_
  rw [div_mul_eq_mul_div]
  ring_nf

/-- `D₂(θ) ≥ 0` for `θ ≥ 0`. -/
theorem debyeTwo_nonneg {θ : ℝ} (hθ : 0 ≤ θ) : 0 ≤ debyeTwo θ := by
  unfold debyeTwo
  refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hθ fun t ht => ?_)
  have : 0 ≤ Real.exp t - 1 := by linarith [Real.add_one_le_exp t, ht.1]
  positivity

/-- Reflection identity of the second Debye function: `D₂(−x) = D₂(x) + 2x/3`. -/
theorem debyeTwo_neg {x : ℝ} (hx : 0 < x) : debyeTwo (-x) = debyeTwo x + 2 * x / 3 := by
  have hflip : (∫ t in (0 : ℝ)..-x, t ^ 2 / (Real.exp t - 1)) =
      -∫ s in (0 : ℝ)..x, (-s) ^ 2 / (Real.exp (-s) - 1) := by
    rw [intervalIntegral.integral_comp_neg (fun t => t ^ 2 / (Real.exp t - 1)), neg_zero,
      intervalIntegral.integral_symm]
  have hid : ∀ s ∈ uIoc (0 : ℝ) x,
      (-s) ^ 2 / (Real.exp (-s) - 1) = -(s ^ 2) - s ^ 2 / (Real.exp s - 1) := by
    intro s hs
    rw [uIoc_of_le hx.le] at hs
    have he : Real.exp s - 1 ≠ 0 := by
      have := Real.add_one_lt_exp hs.1.ne'
      intro h; linarith [hs.1]
    have hE : Real.exp s * Real.exp (-s) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hn : Real.exp (-s) - 1 ≠ 0 := by
      have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hs.1)
      intro h; linarith [hs.1]
    rw [div_eq_iff hn]
    field_simp
    linear_combination (s ^ 2) * hE
  have hI : ∫ s in (0 : ℝ)..x, (-s) ^ 2 / (Real.exp (-s) - 1) =
      -(x ^ 3 / 3) - ∫ s in (0 : ℝ)..x, s ^ 2 / (Real.exp s - 1) := by
    rw [intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun s hs => hid s hs),
      intervalIntegral.integral_sub (f := fun s : ℝ => -(s ^ 2))
        (g := fun s => s ^ 2 / (Real.exp s - 1))
        ((by fun_prop : Continuous fun s : ℝ => -(s ^ 2)).intervalIntegrable _ _)
        (intervalIntegrable_debyeTwo_integrand hx), intervalIntegral.integral_neg, integral_pow]
    norm_num
  unfold debyeTwo
  rw [hflip, hI]
  have hx0 : x ≠ 0 := hx.ne'
  field_simp
  ring

end ProbabilityTheory.Copula
