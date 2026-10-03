/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Elliptical.StudentTTail.MixtureTail
import Copula.TailDependence.Basic

/-! # Tail dependence of the Student-t copula

For the bivariate Student-t copula `C_{ν,r}` with `ν > 0` degrees of freedom and correlation
`r ∈ [−1, 1]`, the lower and upper tail-dependence coefficients coincide and equal

`λ = ∫_{a}^{π/2} cos^ν θ dθ / ∫_0^{π/2} cos^ν θ dθ`,  `a = arccos(r) / 2`

(Hult–Lindskog 2002, angular form). In particular `λ > 0` for every `r > −1`: in contrast to the
Gaussian copula (`hasLowerTailDependence_bivariateGaussian`), the t copula is tail dependent even
for negative correlations. The closed form `λ = 2 t_{ν+1}(−√((ν+1)(1−r)/(1+r)))` of Embrechts,
McNeil and Straumann is derived in `Copula.Elliptical.StudentTTail`.

## Proof
`C(F(x), F(x)) / F(x) = P(X ≤ x, Y ≤ x) / P(X ≤ x)` by Sklar's theorem, where `F` is the marginal
CDF. Both probabilities are regularly varying with index `−ν` as `x → −∞`
(`Copula.Elliptical.StudentTTail.MixtureTail`), so their ratio converges to the ratio of the
Gaussian tail moments `E[max(min(Z₁, Z₂), 0)^ν] / E[max(Z₁, 0)^ν]`, evaluated in polar coordinates
(`Copula.Elliptical.StudentTTail.Polar`). The upper tail follows from radial symmetry.

## Main results
* `studentTTailCoeff ν r`: the angular expression above.
* `hasLowerTailDependence_studentT`, `hasUpperTailDependence_studentT`.
* `studentTTailCoeff_pos` (`r > −1`), `studentTTailCoeff_neg_one`, `studentTTailCoeff_one`,
  `studentTTailCoeff_le_one`, `studentTTailCoeff_eq_zero_iff`.

## References
* P. Embrechts, A. McNeil, D. Straumann, *Correlation and dependence in risk management:
  properties and pitfalls*, CUP 2002.
* H. Hult, F. Lindskog, *Multivariate extremes, aggregation and dependence in elliptical
  distributions*, Adv. Appl. Probab. 34 (2002).
* S. Demarta, A. McNeil, *The t copula and related copulas*, Int. Stat. Rev. 73 (2005).
-/

open MeasureTheory Set Real Filter
open scoped unitInterval Topology ENNReal NNReal

namespace ProbabilityTheory.Copula

/-- The tail-dependence coefficient of the bivariate Student-t copula, in angular form:
`λ(ν, r) = ∫_{arccos(r)/2}^{π/2} cos^ν θ dθ / ∫_0^{π/2} cos^ν θ dθ`. -/
noncomputable def studentTTailCoeff (ν r : ℝ) : ℝ :=
  (∫ θ in arccos r / 2..π / 2, cos θ ^ ν) / ∫ θ in (0 : ℝ)..π / 2, cos θ ^ ν

private theorem cos_rpow_pos_of_mem {ν θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < π / 2) :
    0 < cos θ ^ ν :=
  rpow_pos_of_pos (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], h1⟩) ν

private theorem intervalIntegrable_cos_rpow {ν : ℝ} (hν : 0 < ν) (a b : ℝ) :
    IntervalIntegrable (fun θ => cos θ ^ ν) volume a b :=
  (continuous_cos.rpow_const fun _ => Or.inr hν.le).intervalIntegrable a b

/-- `∫_a^{π/2} cos^ν > 0` for `0 ≤ a < π/2`. -/
theorem integral_cos_rpow_pos {ν a : ℝ} (hν : 0 < ν) (ha0 : 0 ≤ a) (ha : a < π / 2) :
    0 < ∫ θ in a..π / 2, cos θ ^ ν :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_cos_rpow hν _ _)
    (fun _ hθ => cos_rpow_pos_of_mem (ha0.trans hθ.1.le) hθ.2) ha

theorem normalTailMoment_pos {ν : ℝ} (hν : 0 < ν) : 0 < normalTailMoment ν := by
  rw [normalTailMoment_eq hν]
  have := gaussianRadialMoment_pos (by linarith : -2 < ν)
  have := integral_cos_rpow_pos hν le_rfl (by linarith [pi_pos] : (0 : ℝ) < π / 2)
  positivity

/-- Passing from a limit along marginal quantiles `x → −∞` to the limit `t → 0⁺`. -/
theorem tendsto_nhdsGT_zero_of_tendsto_cdfUnit {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hc : Continuous (ProbabilityTheory.cdf μ)) {R : I → ℝ} {l : ℝ}
    (hpos : ∀ᶠ x in atBot, 0 < ProbabilityTheory.cdf μ x)
    (h : Tendsto (fun x => R (cdfUnit μ x)) atBot (𝓝 l)) :
    Tendsto R (𝓝[>] (0 : I)) (𝓝 l) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨X₀, hX₀⟩ := eventually_atBot.1
    ((h.eventually (Metric.ball_mem_nhds l hε)).and hpos)
  refine ⟨ProbabilityTheory.cdf μ X₀, (hX₀ X₀ le_rfl).2, fun {t} ht hdist => ?_⟩
  have ht0 : 0 < (t : ℝ) := ht
  rw [Subtype.dist_eq, Real.dist_eq, Icc.coe_zero, sub_zero, abs_of_pos ht0] at hdist
  obtain ⟨a, ha⟩ := eventually_atBot.1
    ((ProbabilityTheory.tendsto_cdf_atBot μ).eventually (gt_mem_nhds ht0))
  obtain ⟨x, hx⟩ : (t : ℝ) ∈ range (ProbabilityTheory.cdf μ) :=
    mem_range_of_exists_le_of_exists_ge hc ⟨a, (ha a le_rfl).le⟩ ⟨X₀, hdist.le⟩
  have hxX : x ≤ X₀ := by
    by_contra hlt
    have := ProbabilityTheory.monotone_cdf μ (not_le.1 hlt).le
    linarith
  have hxt : cdfUnit μ x = t := Subtype.ext hx
  have := (hX₀ x hxX).1
  rwa [hxt] at this

section StudentT

private theorem marginal_studentTLaw_one {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) {ν : ℝ} (hν : 0 < ν) :
    marginal (studentTLaw (corrMatrix r) ν hν) 1 =
      marginal (studentTLaw (corrMatrix r) ν hν) 0 := by
  have hs : Measurable fun t : ℝ => (√t)⁻¹ := by fun_prop
  have h := gaussianScaleMixtureLaw_map_swapCoord hr
    (gammaProbability (ν / 2) (ν / 2) (by positivity) (by positivity)) hs
  have h' := congrArg ProbabilityMeasure.toMeasure h
  change (studentTLaw (corrMatrix r) ν hν).toMeasure.map swapCoord =
    (studentTLaw (corrMatrix r) ν hν).toMeasure at h'
  rw [marginal, marginal]
  conv_lhs => rw [← h']
  rw [Measure.map_map (measurable_pi_apply 1) measurable_swapCoord]
  rfl

private theorem cdf_marginal_studentTLaw {r ν : ℝ} (hν : 0 < ν) (x : ℝ) :
    ProbabilityTheory.cdf (marginal (studentTLaw (corrMatrix r) ν hν) 0) x =
      (studentTLaw (corrMatrix r) ν hν).toMeasure.real {z | z 0 ≤ x} := by
  rw [cdf_eq_real, marginal, map_measureReal_apply (measurable_pi_apply 0) measurableSet_Iic]
  rfl

private theorem diagonal_studentT_cdfUnit {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) {ν : ℝ} (hν : 0 < ν)
    (x : ℝ) :
    (studentT (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r) ν hν).diagonal
        (cdfUnit (marginal (studentTLaw (corrMatrix r) ν hν) 0) x) =
      (studentTLaw (corrMatrix r) ν hν).toMeasure.real {z | z 0 ≤ x ∧ z 1 ≤ x} := by
  have hsk := isSklarCopula_studentT (corrMatrix r) (posSemidef_corrMatrix hr)
    (corrMatrix_diag r) ν hν ![x, x]
  have hmt : marginalTransform (studentTLaw (corrMatrix r) ν hν) ![x, x] =
      ![cdfUnit (marginal (studentTLaw (corrMatrix r) ν hν) 0) x,
        cdfUnit (marginal (studentTLaw (corrMatrix r) ν hν) 0) x] := by
    funext i
    fin_cases i
    · rfl
    · simp [marginalTransform, marginal_studentTLaw_one hr hν]
  rw [diagonal, ← hmt, hsk]
  congr 1
  ext z
  simp [Pi.le_def, Fin.forall_fin_two]

/-- **Lower tail dependence of the Student-t copula** (Embrechts–McNeil–Straumann 2002,
Hult–Lindskog 2002): `λ_L = ∫_{arccos(r)/2}^{π/2} cos^ν / ∫_0^{π/2} cos^ν`. -/
theorem hasLowerTailDependence_studentT {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) {ν : ℝ} (hν : 0 < ν) :
    (studentT (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r) ν
      hν).HasLowerTailDependence (studentTTailCoeff ν r) := by
  set L := studentTLaw (corrMatrix r) ν hν
  set C := studentT (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r) ν hν
  have hc : Continuous (ProbabilityTheory.cdf (marginal L 0)) :=
    continuous_gaussianScaleMixtureLaw_marginal _ (posSemidef_corrMatrix hr) (corrMatrix_diag r)
      _ _ (by fun_prop) (by
        filter_upwards [ae_pos_gammaMeasure (ν / 2) (ν / 2)] with t ht
        exact inv_pos.mpr (Real.sqrt_pos.2 ht)) 0
  have hA := tendsto_rpow_mul_studentTLaw_lowerOrthant hr hν
  have hB := tendsto_rpow_mul_studentTLaw_lowerTail hr hν
  have hKT : 0 < studentTTailConst ν * normalTailMoment ν :=
    mul_pos (studentTTailConst_pos hν) (normalTailMoment_pos hν)
  -- the ratio along `y → ∞`, with `x = −y`
  have hratio : Tendsto (fun y : ℝ => C.lowerTailRatio (cdfUnit (marginal L 0) (-y))) atTop
      (𝓝 (studentTTailCoeff ν r)) := by
    have h := hA.div hB hKT.ne'
    rw [mul_div_mul_left _ _ (studentTTailConst_pos hν).ne',
      normalJointTailMoment_div_normalTailMoment hν hr] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    rw [Pi.div_apply, lowerTailRatio, diagonal_studentT_cdfUnit hr hν, coe_cdfUnit,
      cdf_marginal_studentTLaw hν,
      mul_div_mul_left _ _ (rpow_pos_of_pos hy ν).ne']
  have hpos : ∀ᶠ x in atBot, 0 < ProbabilityTheory.cdf (marginal L 0) x := by
    have h1 : ∀ᶠ y in atTop, 0 < y ^ ν * L.toMeasure.real {z | z 0 ≤ -y} :=
      hB.eventually (lt_mem_nhds hKT)
    have h2 := tendsto_neg_atBot_atTop.eventually (h1.and (eventually_gt_atTop 0))
    filter_upwards [h2] with x hx
    rw [neg_neg] at hx
    rw [cdf_marginal_studentTLaw hν]
    exact pos_of_mul_pos_right hx.1 (rpow_nonneg hx.2.le _)
  refine tendsto_nhdsGT_zero_of_tendsto_cdfUnit hc hpos ?_
  have := hratio.comp tendsto_neg_atBot_atTop
  simpa [Function.comp_def] using this

/-- **Upper tail dependence of the Student-t copula**: `λ_U = λ_L`, by radial symmetry. -/
theorem hasUpperTailDependence_studentT {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) {ν : ℝ} (hν : 0 < ν) :
    (studentT (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r) ν
      hν).HasUpperTailDependence (studentTTailCoeff ν r) := by
  unfold HasUpperTailDependence upperTailRatio
  rw [show (studentT (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r) ν
    hν).survivalCopula = _ from isRadiallySymmetric_studentT hr ν hν]
  exact hasLowerTailDependence_studentT hr hν

end StudentT

/-! ### Properties of the coefficient -/

/-- The Student-t copula is tail dependent for every `r > −1`: `λ(ν, r) > 0`. -/
theorem studentTTailCoeff_pos {ν r : ℝ} (hν : 0 < ν) (hr : -1 < r) : 0 < studentTTailCoeff ν r := by
  have ha : arccos r / 2 < π / 2 := by
    have : arccos r < π := by
      rw [arccos_lt_pi]
      exact hr
    linarith
  exact div_pos (integral_cos_rpow_pos hν (div_nonneg (arccos_nonneg r) zero_le_two) ha)
    (integral_cos_rpow_pos hν le_rfl (by linarith [pi_pos]))

/-- For `r = −1` (the countermonotonic case) there is no tail dependence. -/
theorem studentTTailCoeff_neg_one (ν : ℝ) : studentTTailCoeff ν (-1) = 0 := by
  simp [studentTTailCoeff, arccos_neg_one]

/-- For `r = 1` (the comonotonic case) the coefficient is `1`. -/
theorem studentTTailCoeff_one {ν : ℝ} (hν : 0 < ν) : studentTTailCoeff ν 1 = 1 := by
  rw [studentTTailCoeff, arccos_one, zero_div]
  exact div_self (integral_cos_rpow_pos hν le_rfl (by linarith [pi_pos])).ne'

/-- The coefficient vanishes exactly in the countermonotonic case `r = −1`. -/
theorem studentTTailCoeff_eq_zero_iff {ν r : ℝ} (hν : 0 < ν) (hr : r ∈ Icc (-1 : ℝ) 1) :
    studentTTailCoeff ν r = 0 ↔ r = -1 := by
  refine ⟨fun h => ?_, fun h => h ▸ studentTTailCoeff_neg_one ν⟩
  by_contra hne
  exact (studentTTailCoeff_pos hν (lt_of_le_of_ne hr.1 (Ne.symm hne))).ne' h

/-- The coefficient is at most `1`. -/
theorem studentTTailCoeff_le_one {ν r : ℝ} (hν : 0 < ν) : studentTTailCoeff ν r ≤ 1 := by
  have hπ := pi_pos
  have ha0 : 0 ≤ arccos r / 2 := div_nonneg (arccos_nonneg r) zero_le_two
  have haπ : arccos r / 2 ≤ π / 2 := div_le_div_of_nonneg_right (arccos_le_pi r) zero_le_two
  have hD := integral_cos_rpow_pos hν le_rfl (by linarith : (0 : ℝ) < π / 2)
  rw [studentTTailCoeff, div_le_one hD,
    ← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := arccos r / 2) (c := π / 2)
      (intervalIntegrable_cos_rpow hν _ _) (intervalIntegrable_cos_rpow hν _ _)]
  have : 0 ≤ ∫ θ in (0 : ℝ)..arccos r / 2, cos θ ^ ν :=
    intervalIntegral.integral_nonneg ha0 fun θ hθ =>
      rpow_nonneg (cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _
  linarith

end ProbabilityTheory.Copula
