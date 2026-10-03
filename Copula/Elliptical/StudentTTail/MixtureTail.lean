/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Elliptical.StudentTTail.Polar
import Copula.Elliptical.ScaleMixtureSymmetry
import Copula.Families.StudentT.GammaSmallBall

/-! # Regularly varying tails of the bivariate Student-t law

Let `(X, Y) = G^{-1/2} (Z₁, Z₂)` with `(Z₁, Z₂) ~ bivariateNormal r` independent of
`G ~ Gamma(ν/2, ν/2)` (the library's `studentTLaw (corrMatrix r) ν`). For `y > 0` and a
positively homogeneous functional `f`,

`P(f(X, Y) ≥ y) = E[P(G < max(f(Z), 0)² / y²)]`,

and the small-ball behaviour of the gamma law (`Copula.Families.StudentT.GammaSmallBall`) together
with dominated convergence gives

`y^ν P(f(X, Y) ≥ y) → K E[max(f(Z), 0)^ν]`,  `K = (ν/2)^{ν/2} / ((ν/2) Γ(ν/2))`.

Applied to `f = min(−x, −y)` and `f = −x` this yields the regularly varying joint and marginal
lower tails of the Student-t law, with limits `K · normalJointTailMoment ν r` and
`K · normalTailMoment ν`.

## References
* P. Embrechts, A. McNeil, D. Straumann, *Correlation and dependence in risk management:
  properties and pitfalls*, CUP 2002.
* H. Hult, F. Lindskog, *Multivariate extremes, aggregation and dependence in elliptical
  distributions*, Adv. Appl. Probab. 34 (2002).
-/

open MeasureTheory Set Real Filter
open scoped Topology ENNReal NNReal

namespace ProbabilityTheory.Copula

/-- For `y > 0`: `{t | y ≤ t^{-1/2} m} = (0, max(m, 0)²/y²]`. -/
theorem setOf_le_inv_sqrt_mul {y : ℝ} (hy : 0 < y) (m : ℝ) :
    {t : ℝ | y ≤ (√t)⁻¹ * m} = Ioc 0 (max m 0 ^ 2 / y ^ 2) := by
  ext t
  simp only [mem_ofPred_eq, mem_Ioc]
  rcases le_or_gt t 0 with ht | ht
  · rw [Real.sqrt_eq_zero'.2 ht, inv_zero, zero_mul]
    constructor
    · intro h
      linarith
    · intro h
      linarith [h.1]
  · have hs : 0 < √t := Real.sqrt_pos.2 ht
    rw [inv_mul_eq_div, le_div_iff₀ hs]
    rcases le_or_gt m 0 with hm | hm
    · have h0 : (0 : ℝ) ^ 2 / y ^ 2 = 0 := by simp
      rw [max_eq_right hm, h0]
      constructor
      · intro h
        nlinarith [mul_pos hy hs]
      · intro h
        linarith [h.2]
    · rw [max_eq_left hm.le, mul_comm, ← le_div_iff₀ hy,
        Real.sqrt_le_left (div_nonneg hm.le hy.le), div_pow]
      exact ⟨fun h => ⟨ht, h⟩, fun h => h.2⟩

/-- `P(0 < G ≤ q) = P(G < q)` for a gamma variable. -/
theorem gammaMeasure_real_Ioc_eq {a b : ℝ} (q : ℝ) :
    (gammaMeasure a b).real (Ioc 0 q) = (gammaMeasure a b).real (Iio q) := by
  have : NullSingletonClass (gammaMeasure a b) := by unfold gammaMeasure; infer_instance
  rw [measureReal_congr (Iio_ae_eq_Iic (μ := gammaMeasure a b) (a := q))]
  apply measureReal_congr
  rw [eventuallyEqSet_iff]
  filter_upwards [ae_pos_gammaMeasure a b] with t ht
  simp [ht]

theorem monotone_gammaMeasure_real_Iio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Monotone fun q => (gammaMeasure a b).real (Iio q) := by
  have : IsProbabilityMeasure (gammaMeasure a b) := isProbabilityMeasure_gammaMeasure ha hb
  exact fun q q' h => measureReal_mono (Iio_subset_Iio h)

/-- **Orthant probabilities of the Student-t law as Gaussian integrals.** For `y > 0` and a
measurable, positively homogeneous `f`,
`P(y ≤ f(X, Y)) = E[P(G < max(f(Z₁, Z₂), 0)² / y²)]`. -/
theorem studentTLaw_real_le_eq {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) {ν : ℝ} (hν : 0 < ν) {y : ℝ}
    (hy : 0 < y) (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (hhom : ∀ c : ℝ, 0 ≤ c → ∀ p : ℝ × ℝ, f (c * p.1, c * p.2) = c * f p) :
    (studentTLaw (corrMatrix r) ν hν).toMeasure.real {z | y ≤ f (z 0, z 1)} =
      ∫ p, (gammaMeasure (ν / 2) (ν / 2)).real (Iio (max (f p) 0 ^ 2 / y ^ 2))
        ∂bivariateNormal r := by
  have hs : Measurable fun t : ℝ => (√t)⁻¹ := by fun_prop
  have hS : MeasurableSet {z : Fin 2 → ℝ | y ≤ f (z 0, z 1)} :=
    measurableSet_le measurable_const (hf.comp (by fun_prop))
  have hγ : IsProbabilityMeasure (gammaMeasure (ν / 2) (ν / 2)) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by positivity)
  have hsec : ∀ p : ℝ × ℝ, Prod.mk p ⁻¹' (scalePair (fun t => (√t)⁻¹) ⁻¹'
      {z : Fin 2 → ℝ | y ≤ f (z 0, z 1)}) = Ioc 0 (max (f p) 0 ^ 2 / y ^ 2) := by
    intro p
    rw [← setOf_le_inv_sqrt_mul hy]
    ext t
    simp only [mem_preimage, mem_ofPred_eq, scalePair, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hhom _ (inv_nonneg.2 (Real.sqrt_nonneg t))]
  have hmeas : Measurable fun p : ℝ × ℝ =>
      (gammaMeasure (ν / 2) (ν / 2)).real (Iio (max (f p) 0 ^ 2 / y ^ 2)) :=
    (monotone_gammaMeasure_real_Iio (by positivity) (by positivity)).measurable.comp
      (by fun_prop)
  rw [studentTLaw, gaussianScaleMixtureLaw_corrMatrix_eq hr _ hs, measureReal_def,
    Measure.map_apply (measurable_scalePair hs) hS,
    Measure.prod_apply (hS.preimage (measurable_scalePair hs)),
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => measureReal_nonneg)
      hmeas.aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun p => ?_
  rw [hsec p, ← gammaMeasure_real_Ioc_eq, ofReal_measureReal]
  rfl

/-- **Dominated convergence for the scaled gamma tails.** If `max(f, 0)^{2a}` is integrable, then
`y^{2a} E[P(G < max(f, 0)²/y²)] → K E[max(f, 0)^{2a}]`. -/
theorem tendsto_rpow_mul_integral_gammaMeasure_real_Iio {E : Type*} [MeasurableSpace E]
    {P : Measure E} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {f : E → ℝ} (hf : Measurable f)
    (hint : Integrable (fun p => max (f p) 0 ^ (2 * a)) P) :
    Tendsto (fun y : ℝ => y ^ (2 * a) *
        ∫ p, (gammaMeasure a b).real (Iio (max (f p) 0 ^ 2 / y ^ 2)) ∂P) atTop
      (𝓝 (gammaSmallBallConst a b * ∫ p, max (f p) 0 ^ (2 * a) ∂P)) := by
  simp_rw [← integral_const_mul]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun p => gammaSmallBallConst a b * max (f p) 0 ^ (2 * a)) ?_ ?_ (hint.const_mul _) ?_
  · exact Eventually.of_forall fun y => (measurable_const.mul
      ((monotone_gammaMeasure_real_Iio ha hb).measurable.comp
        (by fun_prop))).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop 0] with y hy
    refine ae_of_all _ fun p => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (rpow_nonneg hy.le _) measureReal_nonneg)]
    exact rpow_mul_gammaMeasure_real_Iio_le ha hb (le_max_right _ _) hy
  · exact ae_of_all _ fun p => tendsto_rpow_mul_gammaMeasure_real_Iio ha hb (le_max_right _ _)

/-- The small-ball constant of the Student-t mixing law `Gamma(ν/2, ν/2)`. -/
noncomputable def studentTTailConst (ν : ℝ) : ℝ := gammaSmallBallConst (ν / 2) (ν / 2)

theorem studentTTailConst_pos {ν : ℝ} (hν : 0 < ν) : 0 < studentTTailConst ν :=
  gammaSmallBallConst_pos (by positivity) (by positivity)

private theorem two_mul_half (ν : ℝ) : 2 * (ν / 2) = ν := by ring

private theorem integrable_of_le_abs_fst {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) {ν : ℝ} (hν : 0 < ν)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f) (hle : ∀ p : ℝ × ℝ, f p ≤ |p.1|) :
    Integrable (fun p => max (f p) 0 ^ ν) (bivariateNormal r) :=
  (integrable_abs_fst_rpow_bivariateNormal hr hν).mono'
    ((hf.max measurable_const).pow_const ν).aestronglyMeasurable
    (ae_of_all _ fun p => by
      rw [Real.norm_of_nonneg (rpow_nonneg (le_max_right _ _) _)]
      exact rpow_le_rpow (le_max_right _ _) (max_le (hle p) (abs_nonneg _)) hν.le)

/-- The joint lower tail of the Student-t law is regularly varying with index `−ν`:
`y^ν P(X ≤ −y, Y ≤ −y) → K E[max(min(Z₁, Z₂), 0)^ν]`. -/
theorem tendsto_rpow_mul_studentTLaw_lowerOrthant {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) {ν : ℝ}
    (hν : 0 < ν) :
    Tendsto (fun y : ℝ => y ^ ν *
        (studentTLaw (corrMatrix r) ν hν).toMeasure.real {z | z 0 ≤ -y ∧ z 1 ≤ -y}) atTop
      (𝓝 (studentTTailConst ν * normalJointTailMoment ν r)) := by
  set f : ℝ × ℝ → ℝ := fun p => min (-p.1) (-p.2) with hf_def
  have hf : Measurable f := by fun_prop
  have hhom : ∀ c : ℝ, 0 ≤ c → ∀ p : ℝ × ℝ, f (c * p.1, c * p.2) = c * f p := by
    intro c hc p
    simp only [hf_def, ← mul_neg, mul_min_of_nonneg _ _ hc]
  have hint := integrable_of_le_abs_fst hr hν hf fun p =>
    (min_le_left _ _).trans (neg_le_abs p.1)
  have hlim := tendsto_rpow_mul_integral_gammaMeasure_real_Iio (P := bivariateNormal r)
    (a := ν / 2) (b := ν / 2) (by positivity) (by positivity) hf
    (by rw [two_mul_half]; exact hint)
  rw [two_mul_half] at hlim
  have hmom : ∫ p, max (f p) 0 ^ ν ∂bivariateNormal r = normalJointTailMoment ν r := by
    conv_lhs => rw [← bivariateNormal_map_neg hr]
    rw [integral_map (by fun_prop) ((by fun_prop : Measurable fun p : ℝ × ℝ =>
      max (f p) 0).pow_const ν).aestronglyMeasurable, normalJointTailMoment]
    simp only [hf_def, neg_neg]
  rw [studentTTailConst, ← hmom]
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [← studentTLaw_real_le_eq hr hν hy f hf hhom]
  congr 2
  ext z
  simp only [mem_ofPred_eq, hf_def, le_min_iff, le_neg]

/-- The marginal lower tail of the Student-t law: `y^ν P(X ≤ −y) → K E[max(Z, 0)^ν]`. -/
theorem tendsto_rpow_mul_studentTLaw_lowerTail {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) {ν : ℝ}
    (hν : 0 < ν) :
    Tendsto (fun y : ℝ => y ^ ν *
        (studentTLaw (corrMatrix r) ν hν).toMeasure.real {z | z 0 ≤ -y}) atTop
      (𝓝 (studentTTailConst ν * normalTailMoment ν)) := by
  set f : ℝ × ℝ → ℝ := fun p => -p.1 with hf_def
  have hf : Measurable f := by fun_prop
  have hhom : ∀ c : ℝ, 0 ≤ c → ∀ p : ℝ × ℝ, f (c * p.1, c * p.2) = c * f p := by
    intro c _ p
    simp only [hf_def, mul_neg]
  have hint := integrable_of_le_abs_fst hr hν hf fun p => neg_le_abs p.1
  have hlim := tendsto_rpow_mul_integral_gammaMeasure_real_Iio (P := bivariateNormal r)
    (a := ν / 2) (b := ν / 2) (by positivity) (by positivity) hf
    (by rw [two_mul_half]; exact hint)
  rw [two_mul_half] at hlim
  have hmom : ∫ p, max (f p) 0 ^ ν ∂bivariateNormal r = normalTailMoment ν := by
    conv_lhs => rw [← bivariateNormal_map_neg hr]
    rw [integral_map (by fun_prop) ((by fun_prop : Measurable fun p : ℝ × ℝ =>
      max (f p) 0).pow_const ν).aestronglyMeasurable, ← integral_max_fst_rpow_bivariateNormal hr]
    simp only [hf_def, neg_neg]
  rw [studentTTailConst, ← hmom]
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [← studentTLaw_real_le_eq hr hν hy f hf hhom]
  congr 2
  ext z
  simp only [mem_ofPred_eq, hf_def, le_neg]

end ProbabilityTheory.Copula
