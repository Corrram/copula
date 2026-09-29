/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.SpearmanRhoAMH
import Mathlib.NumberTheory.ZetaValues

/-! # Spearman's rho of the AMH copula at the endpoints of the parameter range

By `spearmanRho_amh`, `ρ_θ = 12 ∑ₖ θᵏ / ((k+1)² (k+2)²) − 3` for `|θ| ≤ 1`. Using the partial
fraction decomposition
`1 / ((k+1)² (k+2)²) = 1/(k+1)² + 1/(k+2)² − 2 / ((k+1)(k+2))`
we evaluate the series at the two endpoints (Nelsen, Example 5.7):

* `θ = 1`: `ρ = 4 π² − 39 ≈ 0.4784`, using `∑ 1/n² = π²/6` (`hasSum_zeta_two`);
* `θ = −1`: `ρ = 33 − 48 log 2 ≈ −0.2711`, the minimum of `ρ` over the AMH family, using the
  integral `∑ (−1)ᵏ / ((k+1)(k+2)) = ∫₀¹ (1−t)/(1+t) dt = 2 log 2 − 1` and the reflection
  `∑ (−1)ᵏ/(k+1)² + ∑ (−1)ᵏ/(k+2)² = 1`.
-/

open MeasureTheory Set Filter Real
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

namespace SpearmanAMHEndpoints

theorem partial_fraction (k : ℕ) :
    1 / (((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) ^ 2) =
      1 / ((k : ℝ) + 1) ^ 2 + 1 / ((k : ℝ) + 2) ^ 2 - 2 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
  have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((k : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

theorem summable_sq : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff 1).mpr
    ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
  simpa using this

theorem hasSum_telescope : HasSum (fun k : ℕ => 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) 1 := by
  have hnn : ∀ k : ℕ, 0 ≤ 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := fun k => by positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hpart : ∀ n : ℕ, ∑ i ∈ Finset.range n, 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)) =
      1 - 1 / ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((n : ℝ) + 1 + 1) ≠ 0 := by positivity
      have h3 : ((n : ℝ) + 2) ≠ 0 := by positivity
      field_simp
      ring
  simp_rw [hpart]
  have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this


theorem integral_pow_one_sub (k : ℕ) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ k * (1 - t) = 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have e : (fun t : ℝ => t ^ k * (1 - t)) = fun t : ℝ => t ^ k - t ^ (k + 1) := by
    funext t; ring
  rw [e, intervalIntegral.integral_sub ((continuous_pow k).intervalIntegrable _ _)
    ((continuous_pow (k + 1)).intervalIntegrable _ _), integral_pow, integral_pow]
  field_simp
  push_cast
  ring

theorem integral_frac : ∫ t in Ioc (0 : ℝ) 1, (1 - t) / (1 + t) = 2 * Real.log 2 - 1 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, (1 + t) ≠ 0 := fun t ht => by linarith [ht.1]
  have hint : IntervalIntegrable (fun t : ℝ => 1 / (1 + t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact (continuousAt_const.div (by fun_prop) (hne t ht)).continuousWithinAt
  have e : ∀ t ∈ uIcc (0 : ℝ) 1, (1 - t) / (1 + t) = 2 * (1 / (1 + t)) - 1 := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have := hne t ht
    field_simp
    ring
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_sub (hint.const_mul 2)
    intervalIntegrable_const, intervalIntegral.integral_const_mul]
  have h := intervalIntegral.integral_comp_add_left (fun x : ℝ => 1 / x) (a := 0) (b := 1) 1
  simp only [add_zero] at h
  rw [h, integral_one_div_of_pos one_pos (by norm_num)]
  norm_num

theorem hasSum_alt :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))))
      (2 * Real.log 2 - 1) := by
  have hF : ∀ k : ℕ, Integrable (fun t : ℝ => (-t) ^ k * (1 - t))
      (volume.restrict (Ioc (0 : ℝ) 1)) := fun k =>
    (by fun_prop : Continuous fun t : ℝ => (-t) ^ k * (1 - t)).integrableOn_Ioc
  have hnorm : ∀ k : ℕ, ∫ t, ‖(-t) ^ k * (1 - t)‖ ∂(volume.restrict (Ioc (0 : ℝ) 1)) =
      1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    intro k
    rw [← integral_pow_one_sub k]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [norm_mul, norm_pow, norm_neg, Real.norm_of_nonneg ht.1.le,
      Real.norm_of_nonneg (by linarith [ht.2])]
  have hsum := hasSum_integral_of_summable_integral_norm hF
    (by simp_rw [hnorm]; exact hasSum_telescope.summable)
  have hterm : ∀ k : ℕ, ∫ t, (-t) ^ k * (1 - t) ∂(volume.restrict (Ioc (0 : ℝ) 1)) =
      (-1 : ℝ) ^ k * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
    intro k
    rw [← integral_pow_one_sub k, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    rw [neg_pow]; ring
  have htsum : ∫ t, ∑' k : ℕ, (-t) ^ k * (1 - t) ∂(volume.restrict (Ioc (0 : ℝ) 1)) =
      2 * Real.log 2 - 1 := by
    rw [← integral_frac]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · simp [h1]
    · have habs : |-t| < 1 := by rw [abs_neg, abs_of_pos ht.1]; exact h1
      rw [tsum_mul_right, (hasSum_geometric_of_abs_lt_one habs).tsum_eq]
      rw [sub_neg_eq_add]
      ring
  simp_rw [hterm] at hsum
  rwa [htsum] at hsum

end SpearmanAMHEndpoints

open SpearmanAMHEndpoints in
/-- The AMH series at `θ = 1`: `∑ 1/((k+1)²(k+2)²) = π²/3 − 3`. -/
theorem hasSum_amh_one :
    HasSum (fun k : ℕ => 1 / (((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) ^ 2)) (π ^ 2 / 3 - 3) := by
  have hz : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hasSum_zeta_two
    simpa using this
  have hz2 : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 2) ^ 2) (π ^ 2 / 6 - 1) := by
    have := (hasSum_nat_add_iff' (f := fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) 1).mpr hz
    convert this using 2
    · push_cast; ring_nf
    · simp
  have := (hz.add hz2).sub (hasSum_telescope.mul_left 2)
  convert this using 1
  · funext k; exact partial_fraction k
  · ring

/-- **Spearman's rho of the AMH copula at `θ = 1`**: `ρ = 4 π² − 39`. -/
theorem spearmanRho_amh_one :
    (amh 1 (by norm_num) le_rfl).spearmanRho = 4 * π ^ 2 - 39 := by
  rw [spearmanRho_amh]
  have h := hasSum_amh_one.tsum_eq
  simp only [one_pow]
  rw [h]
  ring


open SpearmanAMHEndpoints in
/-- The AMH series at `θ = -1`: `∑ (-1)ᵏ/((k+1)²(k+2)²) = 3 − 4 log 2`. -/
theorem hasSum_amh_neg_one :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k / (((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) ^ 2))
      (3 - 4 * Real.log 2) := by
  have hA : Summable fun k : ℕ => (-1 : ℝ) ^ k * (1 / ((k : ℝ) + 1) ^ 2) :=
    summable_sq.of_norm_bounded (fun k => by simp)
  have hB := (hasSum_nat_add_iff' (f := fun k : ℕ => (-1 : ℝ) ^ k * (1 / ((k : ℝ) + 1) ^ 2)) 1).mpr
    hA.hasSum
  have hB' : HasSum (fun k : ℕ => (-1 : ℝ) ^ k * (1 / ((k : ℝ) + 2) ^ 2))
      (1 - ∑' k : ℕ, (-1 : ℝ) ^ k * (1 / ((k : ℝ) + 1) ^ 2)) := by
    convert hB.neg using 1
    · funext k
      push_cast
      rw [pow_succ]
      ring_nf
    · simp
  have := (hA.hasSum.add hB').sub (hasSum_alt.mul_left 2)
  convert this using 1
  · funext k
    rw [div_eq_mul_one_div, partial_fraction k]
    ring
  · ring

/-- **Spearman's rho of the AMH copula at `θ = −1`**: `ρ = 33 − 48 log 2 ≈ −0.2711`. -/
theorem spearmanRho_amh_neg_one :
    (amh (-1) le_rfl (by norm_num)).spearmanRho = 33 - 48 * Real.log 2 := by
  rw [spearmanRho_amh, hasSum_amh_neg_one.tsum_eq]
  ring

end ProbabilityTheory.Copula
