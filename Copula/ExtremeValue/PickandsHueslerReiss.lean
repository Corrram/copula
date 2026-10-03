/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Copula.ExtremeValue.PickandsCoefficients

/-! # The Hüsler–Reiss extreme-value copula

Let `Φ` be the standard normal distribution function (`ProbabilityTheory.cdf (gaussianReal 0 1)`)
and `λ > 0`. With the logit `z(t) = log t - log(1 - t)`, the Hüsler–Reiss Pickands function is

`A(t) = (1 - t) Φ(λ - z(t)/(2λ)) + t Φ(λ + z(t)/(2λ))`,  `0 < t < 1`,

with `A(0) = A(1) = 1` (`hueslerReissPickands`). Because `(1 - t) φ(λ - z/(2λ)) = t φ(λ + z/(2λ))`,
its derivative is `A'(t) = Φ(λ + z(t)/(2λ)) - Φ(λ - z(t)/(2λ))`, which is nondecreasing and lies in
`[-1, 1]`; hence `A` is convex, continuous at the endpoints (limits of `Φ` at `±∞`), and
`max(t, 1 - t) ≤ A(t) ≤ 1` (mean value theorem). So `A` is a Pickands function
(`isPickandsFunction_hueslerReissPickands`) and defines the Hüsler–Reiss copula `hueslerReiss`,
symmetric (`A(1 - t) = A(t)`), with `A(1/2) = Φ(λ)` and upper tail dependence coefficient
`λ_U = 2 (1 - Φ(λ))` (`hasUpperTailDependence_hueslerReiss`).

References: J. Hüsler and R.-D. Reiss, *Maxima of normal random vectors: between independence and
complete dependence* (1989); G. Gudendorf and J. Segers, *Extreme-value copulas* (2010);
H. Joe, *Dependence Modeling with Copulas* (2014).
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

namespace HueslerReiss

/-- The standard normal distribution function `Φ`. -/
noncomputable def stdNormalCDF (x : ℝ) : ℝ := ProbabilityTheory.cdf (gaussianReal 0 1) x

/-- The standard normal density `φ`. -/
noncomputable def stdNormalPDF (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

theorem stdNormalCDF_nonneg (x : ℝ) : 0 ≤ stdNormalCDF x := ProbabilityTheory.cdf_nonneg _ x

theorem stdNormalCDF_le_one (x : ℝ) : stdNormalCDF x ≤ 1 := ProbabilityTheory.cdf_le_one _ x

theorem monotone_stdNormalCDF : Monotone stdNormalCDF :=
  (ProbabilityTheory.cdf (gaussianReal 0 1)).mono

theorem continuous_stdNormalPDF : Continuous stdNormalPDF := by
  have : stdNormalPDF = fun x => (√(2 * Real.pi * ((1 : NNReal) : ℝ)))⁻¹ *
      Real.exp (-(x - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ))) := by
    funext x
    rw [stdNormalPDF, gaussianPDFReal_def]
  rw [this]
  fun_prop

/-- `Φ' = φ`. -/
theorem hasDerivAt_stdNormalCDF (x : ℝ) : HasDerivAt stdNormalCDF (stdNormalPDF x) x := by
  have hint := integrable_gaussianPDFReal 0 1
  have hΦ : ∀ y, stdNormalCDF y = ∫ s in Iic y, gaussianPDFReal 0 1 s := by
    intro y
    rw [stdNormalCDF, cdf_eq_real, measureReal_def,
      gaussianReal_apply_eq_integral 0 one_ne_zero, ENNReal.toReal_ofReal
        (setIntegral_nonneg measurableSet_Iic fun s _ => gaussianPDFReal_nonneg 0 1 s)]
  have key : stdNormalCDF = fun y => stdNormalCDF 0 + ∫ s in (0 : ℝ)..y, stdNormalPDF s := by
    funext y
    have h := intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := y) hint.integrableOn
      hint.integrableOn
    rw [hΦ, hΦ]
    simp only [stdNormalPDF]
    linarith
  rw [key]
  exact ((continuous_stdNormalPDF.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add _

/-- The logit `log t - log (1 - t)`. -/
noncomputable def logit (t : ℝ) : ℝ := Real.log t - Real.log (1 - t)

theorem logit_one_sub (t : ℝ) : logit (1 - t) = -logit t := by
  rw [logit, logit, sub_sub_cancel]
  ring

theorem hasDerivAt_logit {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt logit (t⁻¹ + (1 - t)⁻¹) t := by
  have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := (hasDerivAt_id' t).const_sub 1
  have h2 := (Real.hasDerivAt_log (by linarith [ht.2] : (1 - t) ≠ 0)).comp t h1
  have h3 := (Real.hasDerivAt_log ht.1.ne').sub h2
  convert h3 using 1
  · funext s
    rfl
  · ring

theorem logit_mono {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) (hst : s ≤ t) :
    logit s ≤ logit t := by
  have h1 := Real.log_le_log hs.1 hst
  have h2 := Real.log_le_log (by linarith [ht.2] : (0 : ℝ) < 1 - t) (by linarith : 1 - t ≤ 1 - s)
  rw [logit, logit]
  linarith

/-- The Gaussian density identity behind the Hüsler–Reiss derivative. -/
theorem pdf_identity {lam t : ℝ} (hlam : 0 < lam) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1 - t) * stdNormalPDF (lam - logit t / (2 * lam)) =
      t * stdNormalPDF (lam + logit t / (2 * lam)) := by
  have h1t : 0 < 1 - t := by linarith [ht.2]
  have hz : Real.exp (logit t) = t / (1 - t) := by
    rw [logit, Real.exp_sub, Real.exp_log ht.1, Real.exp_log h1t]
  simp only [stdNormalPDF, gaussianPDFReal_def, NNReal.coe_one, sub_zero]
  have hsplit : Real.exp (-(lam - logit t / (2 * lam)) ^ 2 / (2 * 1)) =
      Real.exp (-(lam + logit t / (2 * lam)) ^ 2 / (2 * 1)) * Real.exp (logit t) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hsplit, hz]
  field_simp

/-- The Hüsler–Reiss function on `(0,1)`. -/
noncomputable def hrInner (lam t : ℝ) : ℝ :=
  (1 - t) * stdNormalCDF (lam - logit t / (2 * lam)) +
    t * stdNormalCDF (lam + logit t / (2 * lam))

theorem inner_one_sub (lam t : ℝ) : hrInner lam (1 - t) = hrInner lam t := by
  rw [hrInner, hrInner, logit_one_sub, sub_sub_cancel]
  ring_nf

theorem hasDerivAt_inner {lam t : ℝ} (hlam : 0 < lam) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (hrInner lam)
      (stdNormalCDF (lam + logit t / (2 * lam)) - stdNormalCDF (lam - logit t / (2 * lam))) t := by
  have hz := hasDerivAt_logit ht
  set z' := t⁻¹ + (1 - t)⁻¹
  have ha : HasDerivAt (fun s => lam - logit s / (2 * lam)) (-(z' / (2 * lam))) t := by
    simpa using (hz.div_const (2 * lam)).const_sub lam
  have hb : HasDerivAt (fun s => lam + logit s / (2 * lam)) (z' / (2 * lam)) t := by
    simpa using (hz.div_const (2 * lam)).const_add lam
  have hPa := (hasDerivAt_stdNormalCDF (lam - logit t / (2 * lam))).comp t ha
  have hPb := (hasDerivAt_stdNormalCDF (lam + logit t / (2 * lam))).comp t hb
  have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := (hasDerivAt_id' t).const_sub 1
  have hsum := (h1.mul hPa).add ((hasDerivAt_id t).mul hPb)
  refine hsum.congr_deriv ?_
  have hid := pdf_identity hlam ht
  simp only [Function.comp, id]
  linear_combination (-(z' / (2 * lam))) * hid

/-- The Hüsler–Reiss Pickands function (`λ > 0`). -/
noncomputable def _root_.ProbabilityTheory.Copula.hueslerReissPickands (lam t : ℝ) : ℝ :=
  if t ∈ Ioo (0 : ℝ) 1 then hrInner lam t else 1

theorem pickands_eq_inner {lam t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    hueslerReissPickands lam t = hrInner lam t := ite_eq_left ht

theorem pickands_one_sub (lam t : ℝ) :
    hueslerReissPickands lam (1 - t) = hueslerReissPickands lam t := by
  unfold hueslerReissPickands
  have hiff : (1 - t ∈ Ioo (0 : ℝ) 1) ↔ t ∈ Ioo (0 : ℝ) 1 := by
    simp only [mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  by_cases h : t ∈ Ioo (0 : ℝ) 1
  · rw [ite_eq_left (hiff.2 h), ite_eq_left h, inner_one_sub]
  · rw [ite_eq_right (mt hiff.1 h), ite_eq_right h]

theorem hasDerivAt_pickands {lam t : ℝ} (hlam : 0 < lam) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (hueslerReissPickands lam)
      (stdNormalCDF (lam + logit t / (2 * lam)) - stdNormalCDF (lam - logit t / (2 * lam))) t := by
  refine (hasDerivAt_inner hlam ht).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact pickands_eq_inner hs

theorem continuousWithinAt_zero {lam : ℝ} (hlam : 0 < lam) :
    ContinuousWithinAt (hueslerReissPickands lam) (Icc 0 1) 0 := by
  have hIcc : Icc (0 : ℝ) 1 = insert 0 (Ioc 0 1) := by
    rw [Set.insert_eq, Set.union_comm, Ioc_union_left zero_le_one]
  rw [hIcc, continuousWithinAt_insert_self, ContinuousWithinAt,
    show hueslerReissPickands lam 0 = 1 by simp [hueslerReissPickands]]
  have hle : 𝓝[Ioc (0 : ℝ) 1] 0 ≤ 𝓝[>] 0 := nhdsWithin_mono _ Ioc_subset_Ioi_self
  have hlog : Tendsto Real.log (𝓝[Ioc (0 : ℝ) 1] 0) atBot :=
    Real.tendsto_log_nhdsGT_zero.mono_left hle
  have hlog1 : Tendsto (fun s : ℝ => Real.log (1 - s)) (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 0) := by
    have h : Tendsto (fun s : ℝ => Real.log (1 - s)) (𝓝 0) (𝓝 (Real.log (1 - 0))) :=
      ((Real.continuousAt_log (by norm_num)).comp
        ((continuous_const.sub continuous_id).continuousAt))
    rw [sub_zero, Real.log_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hz : Tendsto logit (𝓝[Ioc (0 : ℝ) 1] 0) atBot :=
    (hlog.atBot_add hlog1.neg).congr fun s => by rw [logit]; ring
  have ha : Tendsto (fun s => lam - logit s / (2 * lam)) (𝓝[Ioc (0 : ℝ) 1] 0) atTop := by
    have h1 : Tendsto (fun s => -logit s / (2 * lam)) (𝓝[Ioc (0 : ℝ) 1] 0) atTop :=
      (tendsto_neg_atBot_atTop.comp hz).atTop_div_const (by positivity)
    have h2 := tendsto_atTop_add_const_left _ lam h1
    refine h2.congr fun s => ?_
    ring
  have hΦ : Tendsto (fun s => stdNormalCDF (lam - logit s / (2 * lam)))
      (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 1) := (tendsto_cdf_atTop (gaussianReal 0 1)).comp ha
  have hlow : Tendsto (fun s => (1 - s) * stdNormalCDF (lam - logit s / (2 * lam)))
      (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 1) := by
    have h1 : Tendsto (fun s : ℝ => 1 - s) (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 1) := by
      have h : Tendsto (fun s : ℝ => 1 - s) (𝓝 0) (𝓝 (1 - 0)) :=
        (continuous_const.sub continuous_id).tendsto 0
      rw [sub_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    simpa using h1.mul hΦ
  have hev : ∀ᶠ s in 𝓝[Ioc (0 : ℝ) 1] 0, s ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num :
      (0 : ℝ) < 1))] with s hs hs1
    exact ⟨hs.1, hs1⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hev] with s hs
    rw [pickands_eq_inner hs, hrInner]
    have := mul_nonneg hs.1.le (stdNormalCDF_nonneg (lam + logit s / (2 * lam)))
    linarith
  · filter_upwards [hev] with s hs
    rw [pickands_eq_inner hs, hrInner]
    have h1 := mul_le_mul_of_nonneg_left (stdNormalCDF_le_one (lam - logit s / (2 * lam)))
      (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s)
    have h2 := mul_le_mul_of_nonneg_left (stdNormalCDF_le_one (lam + logit s / (2 * lam)))
      hs.1.le
    linarith

theorem continuousOn_pickands {lam : ℝ} (hlam : 0 < lam) :
    ContinuousOn (hueslerReissPickands lam) (Icc 0 1) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    exact continuousWithinAt_zero hlam
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · subst h1
    have hc := (continuousWithinAt_zero hlam).comp_of_eq
      ((continuous_sub_left (1 : ℝ)).continuousWithinAt (s := Icc (0 : ℝ) 1) (x := 1))
      (fun s hs => by
        simp only [mem_Icc]
        constructor <;> linarith [hs.1, hs.2]) (by norm_num)
    have he : (hueslerReissPickands lam ∘ fun s : ℝ => 1 - s) = hueslerReissPickands lam := by
      funext s
      exact pickands_one_sub lam s
    rwa [he] at hc
  · exact (hasDerivAt_pickands hlam ⟨h0, h1⟩).continuousAt.continuousWithinAt

theorem deriv_pickands_mem {lam t : ℝ} (hlam : 0 < lam) (ht : t ∈ Ioo (0 : ℝ) 1) :
    -1 ≤ deriv (hueslerReissPickands lam) t ∧ deriv (hueslerReissPickands lam) t ≤ 1 := by
  rw [(hasDerivAt_pickands hlam ht).deriv]
  have h1 := stdNormalCDF_nonneg (lam + logit t / (2 * lam))
  have h2 := stdNormalCDF_le_one (lam + logit t / (2 * lam))
  have h3 := stdNormalCDF_nonneg (lam - logit t / (2 * lam))
  have h4 := stdNormalCDF_le_one (lam - logit t / (2 * lam))
  constructor <;> linarith

end HueslerReiss

open HueslerReiss

/-- The Hüsler–Reiss function is a Pickands dependence function for every `λ > 0`. -/
theorem isPickandsFunction_hueslerReissPickands {lam : ℝ} (hlam : 0 < lam) :
    IsPickandsFunction (hueslerReissPickands lam) := by
  have hcont := continuousOn_pickands hlam
  have hdiff : DifferentiableOn ℝ (hueslerReissPickands lam) (Ioo 0 1) := fun t ht =>
    (hasDerivAt_pickands hlam ht).differentiableAt.differentiableWithinAt
  have h0 : hueslerReissPickands lam 0 = 1 := by simp [hueslerReissPickands]
  have h1 : hueslerReissPickands lam 1 = 1 := by simp [hueslerReissPickands]
  refine ⟨?_, fun t ht => ?_, fun t ht => ?_⟩
  · refine MonotoneOn.convexOn_of_deriv (convex_Icc 0 1) hcont (by rwa [interior_Icc]) ?_
    rw [interior_Icc]
    intro s hs t ht hst
    rw [(hasDerivAt_pickands hlam hs).deriv, (hasDerivAt_pickands hlam ht).deriv]
    have hz := logit_mono hs ht hst
    have hb := monotone_stdNormalCDF (show lam + logit s / (2 * lam) ≤ lam + logit t / (2 * lam) by
      have := div_le_div_of_nonneg_right hz (by positivity : (0 : ℝ) ≤ 2 * lam)
      linarith)
    have ha := monotone_stdNormalCDF (show lam - logit t / (2 * lam) ≤ lam - logit s / (2 * lam) by
      have := div_le_div_of_nonneg_right hz (by positivity : (0 : ℝ) ≤ 2 * lam)
      linarith)
    linarith
  · by_cases hti : t ∈ Ioo (0 : ℝ) 1
    · rw [pickands_eq_inner hti, hrInner]
      have h1 := mul_le_mul_of_nonneg_left (stdNormalCDF_le_one (lam - logit t / (2 * lam)))
        (by linarith [hti.2] : (0 : ℝ) ≤ 1 - t)
      have h2 := mul_le_mul_of_nonneg_left (stdNormalCDF_le_one (lam + logit t / (2 * lam)))
        hti.1.le
      linarith
    · simp [hueslerReissPickands, hti]
  · apply max_le
    · -- `A(t) ≥ t` from `A' ≤ 1` on `[t, 1]`
      rcases eq_or_lt_of_le ht.2 with htt | htt
      · rw [htt, h1]
      obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope (hueslerReissPickands lam) htt
        (hcont.mono (Icc_subset_Icc ht.1 le_rfl))
        (hdiff.mono (Ioo_subset_Ioo ht.1 le_rfl))
      have hcI : c ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hc.1, ht.1], hc.2⟩
      have hb := (deriv_pickands_mem hlam hcI).2
      rw [hcd, h1, div_le_one (by linarith)] at hb
      linarith
    · -- `A(t) ≥ 1 - t` from `A' ≥ -1` on `[0, t]`
      rcases eq_or_lt_of_le ht.1 with htt | htt
      · rw [← htt, h0]
        norm_num
      obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope (hueslerReissPickands lam) htt
        (hcont.mono (Icc_subset_Icc le_rfl ht.2))
        (hdiff.mono (Ioo_subset_Ioo le_rfl ht.2))
      have hcI : c ∈ Ioo (0 : ℝ) 1 := ⟨hc.1, by linarith [hc.2, ht.2]⟩
      have hb := (deriv_pickands_mem hlam hcI).1
      rw [hcd, h0, sub_zero, le_div_iff₀ htt] at hb
      linarith

/-- The Hüsler–Reiss copula, `λ > 0`. -/
noncomputable def hueslerReiss (lam : ℝ) (hlam : 0 < lam) : Copula 2 :=
  pickandsCopula (hueslerReissPickands lam) (isPickandsFunction_hueslerReissPickands hlam)

theorem isExtremeValue_hueslerReiss {lam : ℝ} (hlam : 0 < lam) :
    (hueslerReiss lam hlam).IsExtremeValue :=
  isExtremeValue_pickandsCopula _

theorem hueslerReissPickands_half (lam : ℝ) :
    hueslerReissPickands lam (1 / 2) = stdNormalCDF lam := by
  rw [pickands_eq_inner ⟨by norm_num, by norm_num⟩, hrInner, logit,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, sub_self, zero_div, sub_zero, add_zero]
  ring

/-- Upper tail dependence of the Hüsler–Reiss copula: `λ_U = 2 (1 - Φ(λ))`. -/
theorem hasUpperTailDependence_hueslerReiss {lam : ℝ} (hlam : 0 < lam) :
    (hueslerReiss lam hlam).HasUpperTailDependence (2 * (1 - stdNormalCDF lam)) := by
  have h := hasUpperTailDependence_pickandsCopula (isPickandsFunction_hueslerReissPickands hlam)
  rwa [hueslerReissPickands_half] at h

/-- The Hüsler–Reiss copula is exchangeable: `A(1 - t) = A(t)`. -/
theorem hueslerReiss_transpose_cdf {lam : ℝ} (hlam : 0 < lam) (u v : I) :
    (hueslerReiss lam hlam).cdf ![u, v] = (hueslerReiss lam hlam).cdf ![v, u] := by
  rw [hueslerReiss, cdf_pickandsCopula_two, cdf_pickandsCopula_two, pickandsCDF, pickandsCDF,
    pickandsTail_swap (hueslerReissPickands lam) (-Real.log v)]
  have hfun : (fun t => hueslerReissPickands lam (1 - t)) = hueslerReissPickands lam := by
    funext t
    exact pickands_one_sub lam t
  rw [hfun]
  simp only [or_comm]

end ProbabilityTheory.Copula
