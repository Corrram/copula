/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rearrangement.LevelSet

/-! # Integral form of the rearrangement lemma

Integral consequences of the primitive comparison lemma. With `F = primDev h v` and
`G = rearrDev h v`:

* `∫ |F| ≤ ∫ G` and `∫ F² ≤ ∫ G²` (the `L¹` and `L²` cases of `∫ φ(|F|) ≤ ∫ φ(G)`), obtained from
  the level-set inequality `λ{|F| > y} ≤ λ{G > y}` through the layer-cake formula;
* the sup-norm statement `|F| ≤ max G` is `abs_primDev_le_max` in `Copula.Rearrangement.Primitive`;
* both integral inequalities are strict when `F` takes both signs.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-! ## Comparison of integrals through level sets -/

section Layercake

variable {a b : I → ℝ}

theorem integrableOn_measureReal_gt (a : I → ℝ) :
    IntegrableOn (fun t : ℝ => volume.real {u : I | t < a u}) (Ioc (0 : ℝ) 1) := by
  apply Measure.integrableOn_of_bounded (M := 1)
  · simp
  · exact (Antitone.measurable
      (fun s t hst => measureReal_mono (fun u (hu : t < a u) => (lt_of_le_of_lt hst hu : s < a u))
        )).aestronglyMeasurable
  · exact Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one

theorem integral_eq_integral_measureReal_gt (ha0 : ∀ u, 0 ≤ a u) (ha1 : ∀ u, a u ≤ 1)
    (ham : Measurable a) :
    (∫ u, a u) = ∫ t in Ioc (0 : ℝ) 1, volume.real {u : I | t < a u} := by
  have := integral_Iic_eq_layercake ha0 ha1 ham univ
  simpa only [Measure.restrict_univ, univ_inter] using this

/-- Comparison of integrals of `[0,1]`-valued functions through their upper level sets. -/
theorem integral_le_of_measure_gt_le (ha0 : ∀ u, 0 ≤ a u) (ha1 : ∀ u, a u ≤ 1)
    (ham : Measurable a) (hb0 : ∀ u, 0 ≤ b u) (hb1 : ∀ u, b u ≤ 1) (hbm : Measurable b)
    (hle : ∀ y, 0 < y → volume.real {u : I | y < a u} ≤ volume.real {u : I | y < b u}) :
    (∫ u, a u) ≤ ∫ u, b u := by
  rw [integral_eq_integral_measureReal_gt ha0 ha1 ham,
    integral_eq_integral_measureReal_gt hb0 hb1 hbm]
  exact setIntegral_mono_on (integrableOn_measureReal_gt a) (integrableOn_measureReal_gt b)
    measurableSet_Ioc (fun t ht => hle t ht.1)

/-- Strict comparison: a strict level-set inequality for all small levels gives a strict
inequality of integrals. -/
theorem integral_lt_of_measure_gt_lt (ha0 : ∀ u, 0 ≤ a u) (ha1 : ∀ u, a u ≤ 1)
    (ham : Measurable a) (hb0 : ∀ u, 0 ≤ b u) (hb1 : ∀ u, b u ≤ 1) (hbm : Measurable b)
    (hle : ∀ y, 0 < y → volume.real {u : I | y < a u} ≤ volume.real {u : I | y < b u})
    {y₀ : ℝ} (hy₀ : 0 < y₀)
    (hlt : ∀ y ∈ Ioo 0 y₀, volume.real {u : I | y < a u} < volume.real {u : I | y < b u}) :
    (∫ u, a u) < ∫ u, b u := by
  rw [integral_eq_integral_measureReal_gt ha0 ha1 ham,
    integral_eq_integral_measureReal_gt hb0 hb1 hbm, ← sub_pos,
    ← integral_sub (integrableOn_measureReal_gt b) (integrableOn_measureReal_gt a)]
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · apply lt_of_lt_of_le _ (measure_mono (t := Function.support
      (fun t : ℝ => volume.real {u : I | t < b u} - volume.real {u : I | t < a u}) ∩ Ioc 0 1)
      (s := Ioo 0 (min y₀ 1)) ?_)
    · rw [Real.volume_Ioo]
      simp only [sub_zero, ENNReal.ofReal_pos]
      exact lt_min hy₀ zero_lt_one
    · intro t ht
      refine ⟨?_, ht.1, (ht.2.le.trans (min_le_right _ _))⟩
      rw [Function.mem_support]
      exact (sub_pos.mpr (hlt t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩)).ne'
  · exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => sub_nonneg.mpr (hle t ht.1)
  · exact (integrableOn_measureReal_gt b).sub (integrableOn_measureReal_gt a)

end Layercake

/-! ## Application to `F` and `G` -/

section Main

variable {h : I → ℝ} {v : ℝ}

/-- Primitive comparison, `p = 1`: `∫ |F| ≤ ∫ G`. -/
theorem integral_abs_primDev_le (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1) (hm : Measurable h)
    (hv : (∫ u, h u) = v) : (∫ u, |primDev h v u|) ≤ ∫ u, rearrDev h v u := by
  have hv0 : 0 ≤ v := by rw [← hv]; exact integral_nonneg hf0
  exact integral_le_of_measure_gt_le (fun u => abs_nonneg _) (abs_primDev_le_one hf0 hf1 hm hv)
    (continuous_abs.measurable.comp (measurable_primDev hf0 hf1 hm))
    (rearrDev_nonneg hf0 hf1 hm hv) (rearrDev_le_one hf1 hv0) (measurable_rearrDev hf1)
    (fun y hy => measure_abs_primDev_gt_le hf0 hf1 hm hv hy.le)

theorem setOf_lt_sq_primDev {y : ℝ} (hy : 0 ≤ y) :
    {u : I | y < primDev h v u ^ 2} = {u : I | Real.sqrt y < |primDev h v u|} := by
  ext u
  simp only [mem_ofPred_eq]
  rw [← Real.sqrt_sq_eq_abs, Real.sqrt_lt_sqrt_iff hy]

theorem setOf_lt_sq_rearrDev (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1) (hm : Measurable h)
    (hv : (∫ u, h u) = v) {y : ℝ} (hy : 0 ≤ y) :
    {u : I | y < rearrDev h v u ^ 2} = {u : I | Real.sqrt y < rearrDev h v u} := by
  ext u
  simp only [mem_ofPred_eq]
  have h0 := rearrDev_nonneg hf0 hf1 hm hv u
  constructor
  · intro hlt
    have := (Real.sqrt_lt_sqrt_iff hy).mpr hlt
    rwa [Real.sqrt_sq h0] at this
  · intro hlt
    exact (Real.sqrt_lt_sqrt_iff hy).mp (by rwa [Real.sqrt_sq h0])

theorem sq_primDev_le_one (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1) (hm : Measurable h)
    (hv : (∫ u, h u) = v) (u : I) : primDev h v u ^ 2 ≤ 1 := by
  have := abs_primDev_le_one hf0 hf1 hm hv u
  rw [← sq_abs]
  nlinarith [abs_nonneg (primDev h v u)]

theorem sq_rearrDev_le_one (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1) (hm : Measurable h)
    (hv : (∫ u, h u) = v) (u : I) : rearrDev h v u ^ 2 ≤ 1 := by
  have hv0 : 0 ≤ v := by rw [← hv]; exact integral_nonneg hf0
  have h1 := rearrDev_le_one hf1 hv0 u
  have h0 := rearrDev_nonneg hf0 hf1 hm hv u
  nlinarith

/-- Primitive comparison, `p = 2`: `∫ F² ≤ ∫ G²`. -/
theorem integral_sq_primDev_le (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1) (hm : Measurable h)
    (hv : (∫ u, h u) = v) : (∫ u, primDev h v u ^ 2) ≤ ∫ u, rearrDev h v u ^ 2 := by
  refine integral_le_of_measure_gt_le (fun u => sq_nonneg _) (sq_primDev_le_one hf0 hf1 hm hv)
    ((measurable_primDev hf0 hf1 hm).pow_const 2) (fun u => sq_nonneg _)
    (sq_rearrDev_le_one hf0 hf1 hm hv) ((measurable_rearrDev hf1).pow_const 2) ?_
  intro y hy
  rw [setOf_lt_sq_primDev hy.le, setOf_lt_sq_rearrDev hf0 hf1 hm hv hy.le]
  exact measure_abs_primDev_gt_le hf0 hf1 hm hv (Real.sqrt_nonneg y)

/-- A nonempty open subset of the unit interval has positive measure; here for the set
`{-y < F < 0}` when `F` is continuous, vanishes at `0` and takes a value below `-y`. -/
theorem measure_pos_of_neg_value {F : I → ℝ} (hF : Continuous F) (hF0 : F 0 = 0) {y : ℝ}
    (hy : 0 < y) {t : I} (ht : F t < -y) :
    0 < volume.real {u : I | -y < F u ∧ F u < 0} := by
  -- a point where `F = -y/2`
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : I, F u₀ = -y / 2 := by
    have := intermediate_value_univ t 0 hF (show -y / 2 ∈ Icc (F t) (F 0) by
      rw [hF0]; exact ⟨by linarith, by linarith⟩)
    exact this
  have hopen : IsOpen {u : I | -y < F u ∧ F u < 0} :=
    (isOpen_lt continuous_const hF).inter (isOpen_lt hF continuous_const)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen u₀ ⟨by rw [hu₀]; linarith, by rw [hu₀]; linarith⟩
  have hp0 : 0 ≤ max 0 ((u₀ : ℝ) - ε) := le_max_left _ _
  have hp1 : max 0 ((u₀ : ℝ) - ε) ≤ 1 := max_le zero_le_one (by linarith [u₀.property.2])
  have hq0 : 0 ≤ min 1 ((u₀ : ℝ) + ε) := le_min zero_le_one (by linarith [u₀.property.1])
  have hq1 : min 1 ((u₀ : ℝ) + ε) ≤ 1 := min_le_left _ _
  let p : I := ⟨max 0 ((u₀ : ℝ) - ε), hp0, hp1⟩
  let q : I := ⟨min 1 ((u₀ : ℝ) + ε), hq0, hq1⟩
  have hpq : (p : ℝ) < q := by
    show max 0 ((u₀ : ℝ) - ε) < min 1 ((u₀ : ℝ) + ε)
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨zero_lt_one, by linarith [u₀.property.1]⟩, ⟨by linarith [u₀.property.2], by linarith⟩⟩
  have hsub : Ioo p q ⊆ {u : I | -y < F u ∧ F u < 0} := by
    intro u hu
    apply hball
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
    have h1 : (p : ℝ) < u := hu.1
    have h2 : (u : ℝ) < q := hu.2
    have h3 : (u₀ : ℝ) - ε ≤ p := le_max_right _ _
    have h4 : (q : ℝ) ≤ u₀ + ε := min_le_right _ _
    constructor <;> linarith
  calc (0 : ℝ) < volume.real (Ioo p q) := by
        rw [measureReal_Ioo_unit p q hpq.le]; linarith
    _ ≤ _ := measureReal_mono hsub

/-- Primitive comparison, strict `p = 1`: if `F` takes both signs, then `∫ |F| < ∫ G`. -/
theorem integral_abs_primDev_lt (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1) (hm : Measurable h)
    (hv : (∫ u, h u) = v) {t₁ t₂ : I} (h₁ : 0 < primDev h v t₁) (h₂ : primDev h v t₂ < 0) :
    (∫ u, |primDev h v u|) < ∫ u, rearrDev h v u := by
  have hv0 : 0 ≤ v := by rw [← hv]; exact integral_nonneg hf0
  refine integral_lt_of_measure_gt_lt (fun u => abs_nonneg _) (abs_primDev_le_one hf0 hf1 hm hv)
    (continuous_abs.measurable.comp (measurable_primDev hf0 hf1 hm))
    (rearrDev_nonneg hf0 hf1 hm hv) (rearrDev_le_one hf1 hv0) (measurable_rearrDev hf1)
    (fun y hy => measure_abs_primDev_gt_le hf0 hf1 hm hv hy.le)
    (y₀ := min (primDev h v t₁) (-primDev h v t₂)) (lt_min h₁ (by linarith)) ?_
  intro y hy
  have hyt : y < primDev h v t₁ := hy.2.trans_le (min_le_left _ _)
  have hyt' : primDev h v t₂ < -y := by linarith [hy.2.trans_le (min_le_right _ _)]
  have hJ := measure_pos_of_neg_value (continuous_primDev hf0 hf1 hm) primDev_zero hy.1 hyt'
  have := measure_abs_primDev_gt_add_le hf0 hf1 hm hv hy.1.le hyt
  linarith

/-- Primitive comparison, strict `p = 2`: if `F` takes both signs, then `∫ F² < ∫ G²`. -/
theorem integral_sq_primDev_lt (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1) (hm : Measurable h)
    (hv : (∫ u, h u) = v) {t₁ t₂ : I} (h₁ : 0 < primDev h v t₁) (h₂ : primDev h v t₂ < 0) :
    (∫ u, primDev h v u ^ 2) < ∫ u, rearrDev h v u ^ 2 := by
  set y₀ := min (primDev h v t₁) (-primDev h v t₂) with hy₀
  have hy₀pos : 0 < y₀ := lt_min h₁ (by linarith)
  refine integral_lt_of_measure_gt_lt (fun u => sq_nonneg _) (sq_primDev_le_one hf0 hf1 hm hv)
    ((measurable_primDev hf0 hf1 hm).pow_const 2) (fun u => sq_nonneg _)
    (sq_rearrDev_le_one hf0 hf1 hm hv) ((measurable_rearrDev hf1).pow_const 2)
    (fun y hy => by
      rw [setOf_lt_sq_primDev hy.le, setOf_lt_sq_rearrDev hf0 hf1 hm hv hy.le]
      exact measure_abs_primDev_gt_le hf0 hf1 hm hv (Real.sqrt_nonneg y))
    (y₀ := y₀ ^ 2) (by positivity) ?_
  intro y hy
  rw [setOf_lt_sq_primDev hy.1.le, setOf_lt_sq_rearrDev hf0 hf1 hm hv hy.1.le]
  have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy.1
  have hs1 : Real.sqrt y < y₀ := by
    rw [← Real.sqrt_sq hy₀pos.le]
    exact (Real.sqrt_lt_sqrt_iff hy.1.le).mpr hy.2
  have hyt : Real.sqrt y < primDev h v t₁ := hs1.trans_le (min_le_left _ _)
  have hyt' : primDev h v t₂ < -Real.sqrt y := by linarith [hs1.trans_le (min_le_right _ _)]
  have hJ := measure_pos_of_neg_value (continuous_primDev hf0 hf1 hm) primDev_zero hs0 hyt'
  have := measure_abs_primDev_gt_add_le hf0 hf1 hm hv hs0.le hyt
  linarith

end Main

end ProbabilityTheory.Copula
