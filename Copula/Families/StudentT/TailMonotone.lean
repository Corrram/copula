/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Elliptical.StudentTTail.TailDependence

/-! # Monotonicity of the Student-t tail-dependence coefficient

The tail-dependence coefficient of the bivariate Student-t copula with `ν > 0` degrees of
freedom and correlation `r ∈ [−1, 1]` has the angular form (`studentTTailCoeff`)

`λ(ν, r) = ∫_a^{π/2} cos^ν θ dθ / ∫_0^{π/2} cos^ν θ dθ`,  `a = arccos(r) / 2`.

We prove the classical qualitative behaviour of `λ` (Embrechts–McNeil–Straumann 2002,
Demarta–McNeil 2005, Fig. 1):

* `λ(ν, ·)` is strictly increasing on `[−1, 1]`: the lower limit `arccos(r)/2` decreases.
* `λ(·, r)` is strictly decreasing on `(0, ∞)` for `r ∈ (−1, 1)`. Writing `N_ν = ∫_a^{π/2} cos^ν`,
  `B_ν = ∫_0^a cos^ν` and `c = cos(a)^{μ−ν}` for `ν < μ`, the factor `cos^{μ−ν}` is `≤ c` on
  `[a, π/2]` and `≥ c` on `[0, a]` (strictly at `0`), so `N_μ ≤ c N_ν` and `c B_ν < B_μ`; hence
  `N_μ B_ν < N_ν B_μ`, which is `λ(μ, r) < λ(ν, r)` (a Chebyshev-type ratio argument).
* `λ(ν, r) → 0` as `ν → ∞` for every `r < 1`, consistent with the tail independence of the
  Gaussian copula (`hasLowerTailDependence_bivariateGaussian`): indeed
  `λ(ν, r) ≤ ((π − 2a)/a) · (cos a / cos(a/2))^ν`.
* `λ(ν, r) → 1 − arccos(r)/π` as `ν → 0⁺` (dominated convergence); this is the supremum of the
  coefficient over `ν` (`studentTTailCoeff_lt_limit`).

## Main results
* `studentTTailCoeff_strictMonoOn`, `studentTTailCoeff_monotone`: monotonicity in `r`.
* `studentTTailCoeff_strictAntiOn`: strict monotonicity in `ν`.
* `tendsto_studentTTailCoeff_atTop`: `λ(ν, r) → 0` as `ν → ∞` (`r < 1`).
* `tendsto_studentTTailCoeff_nhdsGT_zero`: `λ(ν, r) → 1 − arccos(r)/π` as `ν → 0⁺`.

## References
* P. Embrechts, A. McNeil, D. Straumann, *Correlation and dependence in risk management:
  properties and pitfalls*, CUP 2002.
* S. Demarta, A. McNeil, *The t copula and related copulas*, Int. Stat. Rev. 73 (2005).
-/

open MeasureTheory Set Real Filter
open scoped Topology

namespace ProbabilityTheory.Copula

private theorem continuous_cos_rpow {ν : ℝ} (hν : 0 < ν) : Continuous fun θ => cos θ ^ ν :=
  continuous_cos.rpow_const fun _ => Or.inr hν.le

private theorem intervalIntegrable_cos_rpow' {ν : ℝ} (hν : 0 < ν) (a b : ℝ) :
    IntervalIntegrable (fun θ => cos θ ^ ν) volume a b :=
  (continuous_cos_rpow hν).intervalIntegrable a b

private theorem cos_nonneg_of_mem {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 2) : 0 ≤ cos θ :=
  cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], h1⟩

private theorem half_arccos_nonneg (r : ℝ) : 0 ≤ arccos r / 2 :=
  div_nonneg (arccos_nonneg r) zero_le_two

private theorem half_arccos_le (r : ℝ) : arccos r / 2 ≤ π / 2 :=
  div_le_div_of_nonneg_right (arccos_le_pi r) zero_le_two

private theorem denom_pos {ν : ℝ} (hν : 0 < ν) : 0 < ∫ θ in (0 : ℝ)..π / 2, cos θ ^ ν :=
  integral_cos_rpow_pos hν le_rfl (by linarith [pi_pos])

/-! ### Monotonicity in the correlation -/

/-- The numerator `∫_a^{π/2} cos^ν` is antitone in the lower limit `a ∈ [0, π/2]`. -/
private theorem integral_cos_rpow_sub {ν a b : ℝ} (hν : 0 < ν) :
    (∫ θ in a..π / 2, cos θ ^ ν) - ∫ θ in b..π / 2, cos θ ^ ν = ∫ θ in a..b, cos θ ^ ν := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := b)
    (intervalIntegrable_cos_rpow' hν a b) (intervalIntegrable_cos_rpow' hν b (π / 2))]
  ring

/-- **Monotonicity in `r`**: `λ(ν, ·)` is monotone on `ℝ` (it is constant outside `[−1, 1]`). -/
theorem studentTTailCoeff_monotone {ν : ℝ} (hν : 0 < ν) : Monotone (studentTTailCoeff ν) := by
  intro r s hrs
  have has : arccos s / 2 ≤ arccos r / 2 :=
    div_le_div_of_nonneg_right (antitone_arccos hrs) zero_le_two
  rw [studentTTailCoeff, studentTTailCoeff]
  refine div_le_div_of_nonneg_right ?_ (denom_pos hν).le
  rw [← sub_nonneg, integral_cos_rpow_sub hν]
  exact intervalIntegral.integral_nonneg has fun θ hθ =>
    rpow_nonneg (cos_nonneg_of_mem ((half_arccos_nonneg s).trans hθ.1)
      (hθ.2.trans (half_arccos_le r))) _

/-- **Strict monotonicity in `r`**: `λ(ν, ·)` is strictly increasing on `[−1, 1]`
(Embrechts–McNeil–Straumann 2002). -/
theorem studentTTailCoeff_strictMonoOn {ν : ℝ} (hν : 0 < ν) :
    StrictMonoOn (studentTTailCoeff ν) (Icc (-1) 1) := by
  intro r hr s hs hrs
  have has : arccos s / 2 < arccos r / 2 := by
    have := strictAntiOn_arccos hr hs hrs
    linarith
  rw [studentTTailCoeff, studentTTailCoeff]
  refine div_lt_div_of_pos_right ?_ (denom_pos hν)
  rw [← sub_pos, integral_cos_rpow_sub hν]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_cos_rpow' hν _ _)
    (fun θ hθ => rpow_pos_of_pos (cos_pos_of_mem_Ioo ⟨?_, ?_⟩) _) has
  · linarith [half_arccos_nonneg s, hθ.1, pi_pos]
  · linarith [half_arccos_le r, hθ.2]

/-! ### Monotonicity in the degrees of freedom -/

/-- The key ratio inequality: for `0 < a < π/2` and `0 < ν < μ`,
`∫_a^{π/2} cos^μ · ∫_0^a cos^ν < ∫_a^{π/2} cos^ν · ∫_0^a cos^μ`. -/
theorem integral_cos_rpow_ratio_lt {a ν μ : ℝ} (ha0 : 0 < a) (ha : a < π / 2) (hν : 0 < ν)
    (hνμ : ν < μ) :
    (∫ θ in a..π / 2, cos θ ^ μ) * (∫ θ in (0 : ℝ)..a, cos θ ^ ν) <
      (∫ θ in a..π / 2, cos θ ^ ν) * ∫ θ in (0 : ℝ)..a, cos θ ^ μ := by
  have hπ := pi_pos
  have hμ : 0 < μ := hν.trans hνμ
  have hca : 0 < cos a := cos_pos_of_mem_Ioo ⟨by linarith, ha⟩
  have hca1 : cos a < 1 := by
    have := cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) ha0
    rwa [cos_zero] at this
  set c := cos a ^ (μ - ν) with hc
  have hsplit : ∀ θ, 0 ≤ cos θ → cos θ ^ μ = cos θ ^ ν * cos θ ^ (μ - ν) := fun θ h => by
    rw [← rpow_add' h (by linarith : ν + (μ - ν) ≠ 0)]
    ring_nf
  -- upper part: `cos^{μ−ν} ≤ c`
  have hN : (∫ θ in a..π / 2, cos θ ^ μ) ≤ c * ∫ θ in a..π / 2, cos θ ^ ν := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on ha.le (intervalIntegrable_cos_rpow' hμ _ _)
      ((intervalIntegrable_cos_rpow' hν _ _).const_mul c) fun θ hθ => ?_
    have h0 : 0 ≤ cos θ := cos_nonneg_of_mem (ha0.le.trans hθ.1) hθ.2
    have hle : cos θ ≤ cos a := cos_le_cos_of_nonneg_of_le_pi ha0.le (by linarith [hθ.2]) hθ.1
    rw [hsplit θ h0, mul_comm c]
    exact mul_le_mul_of_nonneg_left (rpow_le_rpow h0 hle (by linarith)) (rpow_nonneg h0 _)
  -- lower part: `cos^{μ−ν} ≥ c`, strictly at `0`
  have hB : c * (∫ θ in (0 : ℝ)..a, cos θ ^ ν) < ∫ θ in (0 : ℝ)..a, cos θ ^ μ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt ha0
      ((continuous_const.mul (continuous_cos_rpow hν)).continuousOn)
      (continuous_cos_rpow hμ).continuousOn (fun θ hθ => ?_) ⟨0, ⟨le_rfl, ha0.le⟩, ?_⟩
    · have h0 : 0 ≤ cos θ := cos_nonneg_of_mem hθ.1.le (by linarith [hθ.2])
      have hle : cos a ≤ cos θ := cos_le_cos_of_nonneg_of_le_pi hθ.1.le (by linarith) hθ.2
      rw [hsplit θ h0, mul_comm c]
      exact mul_le_mul_of_nonneg_left (rpow_le_rpow hca.le hle (by linarith)) (rpow_nonneg h0 _)
    · simp only [cos_zero, one_rpow, mul_one]
      exact rpow_lt_one hca.le hca1 (by linarith)
  have hNpos : 0 < ∫ θ in a..π / 2, cos θ ^ ν := integral_cos_rpow_pos hν ha0.le ha
  have hB0 : 0 ≤ ∫ θ in (0 : ℝ)..a, cos θ ^ ν :=
    intervalIntegral.integral_nonneg ha0.le fun θ hθ =>
      rpow_nonneg (cos_nonneg_of_mem hθ.1 (by linarith [hθ.2])) _
  calc (∫ θ in a..π / 2, cos θ ^ μ) * (∫ θ in (0 : ℝ)..a, cos θ ^ ν)
      ≤ (c * ∫ θ in a..π / 2, cos θ ^ ν) * (∫ θ in (0 : ℝ)..a, cos θ ^ ν) :=
        mul_le_mul_of_nonneg_right hN hB0
    _ = (∫ θ in a..π / 2, cos θ ^ ν) * (c * ∫ θ in (0 : ℝ)..a, cos θ ^ ν) := by ring
    _ < (∫ θ in a..π / 2, cos θ ^ ν) * ∫ θ in (0 : ℝ)..a, cos θ ^ μ :=
        mul_lt_mul_of_pos_left hB hNpos

/-- **Strict monotonicity in `ν`**: for `r ∈ (−1, 1)`, the tail-dependence coefficient
`λ(ν, r)` of the t copula is strictly decreasing in the degrees of freedom `ν > 0`
(Embrechts–McNeil–Straumann 2002, Demarta–McNeil 2005). -/
theorem studentTTailCoeff_strictAntiOn {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    StrictAntiOn (fun ν => studentTTailCoeff ν r) (Ioi 0) := by
  intro ν hν μ hμ hνμ
  have hν : 0 < ν := hν
  have hμ : 0 < μ := hμ
  set a := arccos r / 2 with ha_def
  have ha0 : 0 < a := by
    have := arccos_pos.2 hr.2
    positivity
  have ha : a < π / 2 := by
    have : arccos r < π := arccos_lt_pi.2 hr.1
    linarith
  have hsplit : ∀ κ : ℝ, 0 < κ → (∫ θ in (0 : ℝ)..π / 2, cos θ ^ κ) =
      (∫ θ in (0 : ℝ)..a, cos θ ^ κ) + ∫ θ in a..π / 2, cos θ ^ κ := fun κ hκ =>
    (intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_cos_rpow' hκ 0 a)
      (intervalIntegrable_cos_rpow' hκ a (π / 2))).symm
  change studentTTailCoeff μ r < studentTTailCoeff ν r
  rw [studentTTailCoeff, studentTTailCoeff, div_lt_div_iff₀ (denom_pos hμ) (denom_pos hν),
    hsplit μ hμ, hsplit ν hν]
  have := integral_cos_rpow_ratio_lt ha0 ha hν hνμ
  nlinarith [this]

/-! ### Limits in the degrees of freedom -/

/-- An explicit exponential bound: for `0 < a ≤ π/2` and `ν > 0`,
`∫_a^{π/2} cos^ν / ∫_0^{π/2} cos^ν ≤ ((π − 2a)/a) (cos a / cos (a/2))^ν`. -/
theorem integral_cos_rpow_ratio_le {a ν : ℝ} (ha0 : 0 < a) (ha : a ≤ π / 2) (hν : 0 < ν) :
    (∫ θ in a..π / 2, cos θ ^ ν) / (∫ θ in (0 : ℝ)..π / 2, cos θ ^ ν) ≤
      (π - 2 * a) / a * (cos a / cos (a / 2)) ^ ν := by
  have hπ := pi_pos
  have hc2 : 0 < cos (a / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hca : 0 ≤ cos a := cos_nonneg_of_mem ha0.le ha
  have hN : (∫ θ in a..π / 2, cos θ ^ ν) ≤ (π / 2 - a) * cos a ^ ν := by
    have h := intervalIntegral.integral_mono_on ha (intervalIntegrable_cos_rpow' hν _ _)
      (intervalIntegrable_const (c := cos a ^ ν)) fun θ hθ =>
        rpow_le_rpow (cos_nonneg_of_mem (ha0.le.trans hθ.1) hθ.2)
          (cos_le_cos_of_nonneg_of_le_pi ha0.le (by linarith [hθ.2]) hθ.1) hν.le
    rwa [intervalIntegral.integral_const, smul_eq_mul] at h
  have hD : (a / 2) * cos (a / 2) ^ ν ≤ ∫ θ in (0 : ℝ)..π / 2, cos θ ^ ν := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := a / 2)
      (intervalIntegrable_cos_rpow' hν _ _) (intervalIntegrable_cos_rpow' hν _ _)]
    have h1 := intervalIntegral.integral_mono_on (by linarith : (0 : ℝ) ≤ a / 2)
      (intervalIntegrable_const (c := cos (a / 2) ^ ν)) (intervalIntegrable_cos_rpow' hν _ _)
      fun θ hθ => rpow_le_rpow hc2.le
        (cos_le_cos_of_nonneg_of_le_pi hθ.1 (by linarith) hθ.2) hν.le
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
    have h2 : 0 ≤ ∫ θ in a / 2..π / 2, cos θ ^ ν :=
      intervalIntegral.integral_nonneg (by linarith) fun θ hθ =>
        rpow_nonneg (cos_nonneg_of_mem (by linarith [hθ.1]) hθ.2) _
    linarith
  have hpow : 0 < cos (a / 2) ^ ν := rpow_pos_of_pos hc2 ν
  have hDpos : 0 < (a / 2) * cos (a / 2) ^ ν := by positivity
  rw [div_rpow hca hc2.le, div_le_iff₀ (hDpos.trans_le hD)]
  calc (∫ θ in a..π / 2, cos θ ^ ν) ≤ (π / 2 - a) * cos a ^ ν := hN
    _ = (π - 2 * a) / a * (cos a ^ ν / cos (a / 2) ^ ν) * ((a / 2) * cos (a / 2) ^ ν) := by
        field_simp
    _ ≤ (π - 2 * a) / a * (cos a ^ ν / cos (a / 2) ^ ν) *
          ∫ θ in (0 : ℝ)..π / 2, cos θ ^ ν := by
        refine mul_le_mul_of_nonneg_left hD ?_
        have : 0 ≤ π - 2 * a := by linarith
        positivity

/-- **Gaussian limit**: for `r < 1`, `λ(ν, r) → 0` as `ν → ∞`, consistent with the tail
independence of the Gaussian copula (the t law converges to the normal law as `ν → ∞`). -/
theorem tendsto_studentTTailCoeff_atTop {r : ℝ} (hr : r < 1) :
    Tendsto (fun ν => studentTTailCoeff ν r) atTop (𝓝 0) := by
  have hπ := pi_pos
  set a := arccos r / 2 with ha_def
  have ha0 : 0 < a := by
    have := arccos_pos.2 hr
    positivity
  have ha : a ≤ π / 2 := half_arccos_le r
  have hc2 : 0 < cos (a / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hca : 0 ≤ cos a := cos_nonneg_of_mem ha0.le ha
  have hq1 : cos a / cos (a / 2) < 1 := by
    rw [div_lt_one hc2]
    exact cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  have hq0 : -1 < cos a / cos (a / 2) := by
    have : 0 ≤ cos a / cos (a / 2) := div_nonneg hca hc2.le
    linarith
  have hlim : Tendsto (fun ν : ℝ => (π - 2 * a) / a * (cos a / cos (a / 2)) ^ ν) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_atTop_of_base_lt_one _ hq0 hq1).const_mul ((π - 2 * a) / a)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with ν hν
    exact div_nonneg (intervalIntegral.integral_nonneg ha fun θ hθ =>
      rpow_nonneg (cos_nonneg_of_mem (ha0.le.trans hθ.1) hθ.2) _) (denom_pos hν).le
  · filter_upwards [eventually_gt_atTop 0] with ν hν
    exact integral_cos_rpow_ratio_le ha0 ha hν

/-- `∫_a^b cos^ν → b − a` as `ν → 0⁺`, for `0 ≤ a ≤ b ≤ π/2` (dominated convergence). -/
private theorem tendsto_integral_cos_rpow_nhdsGT_zero {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ π / 2) :
    Tendsto (fun ν : ℝ => ∫ θ in a..b, cos θ ^ ν) (𝓝[>] 0) (𝓝 (b - a)) := by
  have hπ := pi_pos
  have hconst : (∫ _ in a..b, (1 : ℝ)) = b - a := by simp
  rw [← hconst]
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
    ?_ ?_ intervalIntegrable_const ?_
  · exact Eventually.of_forall fun ν =>
      (continuous_cos.measurable.pow_const ν).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ν hν
    refine ae_of_all _ fun θ hθ => ?_
    rw [uIoc_of_le hab] at hθ
    have h0 : 0 ≤ cos θ := cos_nonneg_of_mem (ha0.trans hθ.1.le) (hθ.2.trans hb)
    rw [Real.norm_of_nonneg (rpow_nonneg h0 _)]
    exact rpow_le_one h0 (cos_le_one θ) (le_of_lt hν)
  · -- off the null set `{π/2}` the base is positive
    have hnull : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ π / 2 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hnull] with θ hθne hθ
    rw [uIoc_of_le hab] at hθ
    have hpos : 0 < cos θ :=
      cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], lt_of_le_of_ne (hθ.2.trans hb) hθne⟩
    have h := ((continuousAt_const_rpow (b := 0) hpos.ne').tendsto).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h

/-- **Cauchy-type limit**: `λ(ν, r) → 1 − arccos(r)/π` as `ν → 0⁺`. -/
theorem tendsto_studentTTailCoeff_nhdsGT_zero (r : ℝ) :
    Tendsto (fun ν : ℝ => studentTTailCoeff ν r) (𝓝[>] 0) (𝓝 (1 - arccos r / π)) := by
  have hπ := pi_pos
  have hN := tendsto_integral_cos_rpow_nhdsGT_zero (half_arccos_nonneg r) (half_arccos_le r) le_rfl
  have hD := tendsto_integral_cos_rpow_nhdsGT_zero le_rfl (by linarith : (0 : ℝ) ≤ π / 2) le_rfl
  have h := hN.div hD (by linarith : π / 2 - 0 ≠ 0)
  have hval : (π / 2 - arccos r / 2) / (π / 2 - 0) = 1 - arccos r / π := by
    field_simp
    ring
  rw [hval] at h
  exact h

/-- For `r ∈ (−1, 1)` and `ν > 0`, `λ(ν, r) < 1 − arccos(r)/π`: the `ν → 0⁺` limit is the strict
supremum of the coefficient over the degrees of freedom. -/
theorem studentTTailCoeff_lt_limit {ν r : ℝ} (hν : 0 < ν) (hr : r ∈ Ioo (-1 : ℝ) 1) :
    studentTTailCoeff ν r < 1 - arccos r / π := by
  have hanti := studentTTailCoeff_strictAntiOn hr
  have hν2 : 0 < ν / 2 := by positivity
  have hlt : studentTTailCoeff ν r < studentTTailCoeff (ν / 2) r :=
    hanti (show ν / 2 ∈ Ioi (0 : ℝ) from hν2) (show ν ∈ Ioi (0 : ℝ) from hν) (by linarith)
  have hle : studentTTailCoeff (ν / 2) r ≤ 1 - arccos r / π := by
    refine ge_of_tendsto (tendsto_studentTTailCoeff_nhdsGT_zero r) ?_
    filter_upwards [Ioo_mem_nhdsGT hν2] with κ hκ
    exact hanti.antitoneOn (show κ ∈ Ioi (0 : ℝ) from hκ.1)
      (show ν / 2 ∈ Ioi (0 : ℝ) from hν2) hκ.2.le
  exact hlt.trans_le hle

end ProbabilityTheory.Copula
