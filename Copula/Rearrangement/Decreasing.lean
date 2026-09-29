/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-! # Decreasing rearrangements on the unit interval

For a measurable `f : I → ℝ` with values in `[0,1]`, the decreasing rearrangement is
`f↓(s) = inf {c ≥ 0 : λ(f > c) ≤ s}`. It is antitone, equimeasurable with `f`, monotone in `f`,
and satisfies the Hardy–Littlewood inequality `∫_A f ≤ ∫_0^{λ(A)} f↓` for measurable `A`
(the bathtub principle; see e.g. Lieb–Loss, *Analysis*, Section 3.3, or Bennett–Sharpley,
*Interpolation of Operators*, Chapter 2).

This is the general rearrangement infrastructure used for the SI rearrangement of a copula
(`Copula.Rearrangement.SI`) and for the primitive comparison lemma
(`Copula.Rearrangement.Primitive`).
-/

open MeasureTheory Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

/-- The distribution function `c ↦ λ{f > c}` on the unit interval. -/
noncomputable def distFun (f : I → ℝ) (c : ℝ) : ℝ := volume.real {u : I | c < f u}

theorem distFun_nonneg (f : I → ℝ) (c : ℝ) : 0 ≤ distFun f c := measureReal_nonneg

theorem distFun_le_one (f : I → ℝ) (c : ℝ) : distFun f c ≤ 1 := by
  unfold distFun
  calc volume.real {u : I | c < f u} ≤ volume.real (univ : Set I) :=
        measureReal_mono (subset_univ _)
    _ = 1 := by simp

theorem distFun_antitone (f : I → ℝ) : Antitone (distFun f) := by
  intro a b hab
  exact measureReal_mono (fun u hu => lt_of_le_of_lt hab hu)

theorem distFun_of_bound {f : I → ℝ} (hf : ∀ u, f u ≤ 1) {c : ℝ} (hc : 1 ≤ c) :
    distFun f c = 0 := by
  unfold distFun
  have : {u : I | c < f u} = ∅ := by
    ext u; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]; linarith [hf u]
  simp [this]

theorem distFun_of_neg {f : I → ℝ} (hf : ∀ u, 0 ≤ f u) {c : ℝ} (hc : c < 0) :
    distFun f c = 1 := by
  unfold distFun
  have : {u : I | c < f u} = univ := by
    ext u; simp only [mem_ofPred_eq, mem_univ, iff_true]; linarith [hf u]
  simp [this]

/-- Right continuity of the distribution function. -/
theorem distFun_rightContinuous (f : I → ℝ) (c : ℝ) :
    Tendsto (distFun f) (𝓝[>] c) (𝓝 (distFun f c)) := by
  have hU : {u : I | c < f u} = ⋃ n : ℕ, {u : I | c + 1 / ((n : ℝ) + 1) < f u} := by
    ext u
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hmono : Monotone (fun n : ℕ => {u : I | c + 1 / ((n : ℝ) + 1) < f u}) := by
    intro m n hmn u hu
    simp only [mem_ofPred_eq] at hu ⊢
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    linarith
  have hseq := tendsto_measure_iUnion_atTop (μ := (volume : Measure I)) hmono
  rw [← hU] at hseq
  have hreal : Tendsto (fun n : ℕ => distFun f (c + 1 / ((n : ℝ) + 1))) atTop
      (𝓝 (distFun f c)) := by
    unfold distFun
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hseq
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hreal) ε hε
  refine ⟨1 / ((N : ℝ) + 1), by positivity, ?_⟩
  intro x hx hdist
  have hxc : c < x := hx
  rw [Real.dist_eq, abs_lt] at hdist
  have h1 : distFun f x ≤ distFun f c := distFun_antitone f hxc.le
  have h2 : distFun f (c + 1 / ((N : ℝ) + 1)) ≤ distFun f x :=
    distFun_antitone f (by linarith [hdist.2])
  have h3 := hN N le_rfl
  rw [Real.dist_eq, abs_lt] at h3
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- The decreasing rearrangement `f↓(s) = inf {c ≥ 0 : λ{f > c} ≤ s}` of a `[0,1]`-valued
function. -/
noncomputable def decRearr (f : I → ℝ) (s : ℝ) : ℝ := sInf {c : ℝ | 0 ≤ c ∧ distFun f c ≤ s}

theorem decRearr_set_nonempty {f : I → ℝ} (hf : ∀ u, f u ≤ 1) {s : ℝ} (hs : 0 ≤ s) :
    ({c : ℝ | 0 ≤ c ∧ distFun f c ≤ s}).Nonempty :=
  ⟨1, zero_le_one, by rw [distFun_of_bound hf le_rfl]; exact hs⟩

theorem decRearr_set_bdd (f : I → ℝ) (s : ℝ) : BddBelow {c : ℝ | 0 ≤ c ∧ distFun f c ≤ s} :=
  ⟨0, fun _ hc => hc.1⟩

theorem decRearr_nonneg {f : I → ℝ} (hf : ∀ u, f u ≤ 1) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ decRearr f s :=
  le_csInf (decRearr_set_nonempty hf hs) (fun _ hc => hc.1)

theorem decRearr_le_one {f : I → ℝ} (hf : ∀ u, f u ≤ 1) {s : ℝ} (hs : 0 ≤ s) :
    decRearr f s ≤ 1 :=
  csInf_le (decRearr_set_bdd f s) ⟨zero_le_one, by rw [distFun_of_bound hf le_rfl]; exact hs⟩

theorem decRearr_antitoneOn {f : I → ℝ} (hf : ∀ u, f u ≤ 1) :
    AntitoneOn (decRearr f) (Ici 0) := by
  intro s hs t _ hst
  apply csInf_le_csInf (decRearr_set_bdd f t) (decRearr_set_nonempty hf hs)
  intro c hc
  exact ⟨hc.1, hc.2.trans hst⟩

/-- The defining property of the rearrangement. -/
theorem lt_decRearr_iff {f : I → ℝ} (hf : ∀ u, f u ≤ 1) {c s : ℝ}
    (hc : 0 ≤ c) (hs : 0 ≤ s) : c < decRearr f s ↔ s < distFun f c := by
  constructor
  · intro h
    by_contra hle
    push Not at hle
    have := csInf_le (decRearr_set_bdd f s) ⟨hc, hle⟩
    exact absurd h (not_lt.mpr this)
  · intro h
    have hev := (distFun_rightContinuous f c).eventually (lt_mem_nhds h)
    obtain ⟨δ, hδ, hδs⟩ : ∃ δ > 0, s < distFun f (c + δ) := by
      rcases (hev.and self_mem_nhdsWithin).exists with ⟨x, hx, hcx⟩
      exact ⟨x - c, sub_pos.mpr hcx, by simpa using hx⟩
    apply lt_of_lt_of_le (show c < c + δ by linarith)
    apply le_csInf (decRearr_set_nonempty hf hs)
    intro c' hc'
    by_contra hlt
    push Not at hlt
    have := distFun_antitone f hlt.le
    linarith [hc'.2]

theorem decRearr_measurable {f : I → ℝ} (hf : ∀ u, f u ≤ 1) :
    Measurable (fun s : I => decRearr f s) := by
  apply Antitone.measurable
  intro s t hst
  exact decRearr_antitoneOn hf s.property.1 t.property.1 hst

/-- Equimeasurability on upper level sets. -/
theorem volume_lt_decRearr {f : I → ℝ} (hf0 : ∀ u, 0 ≤ f u) (hf : ∀ u, f u ≤ 1)
    (c : ℝ) : volume {s : I | c < decRearr f s} = volume {u : I | c < f u} := by
  rcases lt_or_ge c 0 with hc | hc
  · have h1 : {s : I | c < decRearr f s} = univ := by
      ext s; simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact lt_of_lt_of_le hc (decRearr_nonneg hf s.property.1)
    have h2 : {u : I | c < f u} = univ := by
      ext u; simp only [mem_ofPred_eq, mem_univ, iff_true]; linarith [hf0 u]
    rw [h1, h2]
  · have hset : {s : I | c < decRearr f s} = {s : I | (s : ℝ) < distFun f c} := by
      ext s
      simp only [mem_ofPred_eq]
      exact lt_decRearr_iff hf hc s.property.1
    rw [hset]
    have hd0 := distFun_nonneg f c
    have hd1 := distFun_le_one f c
    have hvol : volume {s : I | (s : ℝ) < distFun f c} = ENNReal.ofReal (distFun f c) := by
      have := unitInterval.volume_Iio (⟨distFun f c, hd0, hd1⟩ : I)
      simpa [Iio, Subtype.mk_lt_mk, ← Subtype.coe_lt_coe] using this
    rw [hvol]
    unfold distFun
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The pushforward distributions of `f` and of its rearrangement coincide. -/
theorem map_decRearr {f : I → ℝ} (hf0 : ∀ u, 0 ≤ f u) (hf : ∀ u, f u ≤ 1) (hm : Measurable f) :
    (volume : Measure I).map (fun s : I => decRearr f s) = (volume : Measure I).map f := by
  apply (Measure.ext_of_Iic _ _ _).symm
  intro a
  rw [Measure.map_apply hm measurableSet_Iic,
    Measure.map_apply (decRearr_measurable hf) measurableSet_Iic]
  have h1 : f ⁻¹' Iic a = {u : I | a < f u}ᶜ := by ext u; simp
  have h2 : (fun s : I => decRearr f s) ⁻¹' Iic a = {s : I | a < decRearr f s}ᶜ := by
    ext u; simp
  rw [h1, h2, measure_compl (measurableSet_lt measurable_const hm) (measure_ne_top _ _),
    measure_compl (measurableSet_lt measurable_const (decRearr_measurable hf))
      (measure_ne_top _ _), volume_lt_decRearr hf0 hf a]

theorem integral_comp_decRearr {f : I → ℝ} (hf0 : ∀ u, 0 ≤ f u) (hf : ∀ u, f u ≤ 1)
    (hm : Measurable f) {φ : ℝ → ℝ} (hφ : Measurable φ) :
    (∫ s : I, φ (decRearr f s)) = ∫ u : I, φ (f u) := by
  have h1 := integral_map (μ := (volume : Measure I)) (decRearr_measurable hf).aemeasurable
    hφ.aestronglyMeasurable
  have h2 := integral_map (μ := (volume : Measure I)) hm.aemeasurable hφ.aestronglyMeasurable
  rw [← h1, ← h2, map_decRearr hf0 hf hm]

theorem decRearr_congr {f g : I → ℝ} (h : f =ᵐ[volume] g) : decRearr f = decRearr g := by
  have hd : distFun f = distFun g := by
    funext c
    unfold distFun
    apply measureReal_congr
    filter_upwards [h] with u hu
    simp only [eq_iff_iff]
    rw [hu]
  unfold decRearr
  rw [hd]

theorem decRearr_mono {f g : I → ℝ} (hg : ∀ u, g u ≤ 1) (h : ∀ᵐ u ∂volume, f u ≤ g u)
    {s : ℝ} (hs : 0 ≤ s) : decRearr f s ≤ decRearr g s := by
  apply csInf_le_csInf (decRearr_set_bdd f s) (decRearr_set_nonempty hg hs)
  intro c hc
  refine ⟨hc.1, le_trans ?_ hc.2⟩
  unfold distFun
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [h] with u hu
  exact fun hx => lt_of_lt_of_le hx hu

/-- A continuous function of a `[0,1]`-valued measurable function is integrable. -/
theorem integrable_comp_of_unit {f : I → ℝ} (hf0 : ∀ u, 0 ≤ f u) (hf : ∀ u, f u ≤ 1)
    (hm : Measurable f) {φ : ℝ → ℝ} (hφ : Continuous φ) : Integrable (fun u => φ (f u)) := by
  obtain ⟨b, hb⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hφ.continuousOn
  exact Integrable.of_bound (hφ.measurable.comp hm).aestronglyMeasurable b
    (Eventually.of_forall fun u => hb _ ⟨hf0 u, hf u⟩)

theorem integrable_decRearr {f : I → ℝ} (hf : ∀ u, f u ≤ 1) :
    Integrable (fun s : I => decRearr f s) :=
  integrable_comp_of_unit (fun s => decRearr_nonneg hf s.property.1)
    (fun s => decRearr_le_one hf s.property.1) (decRearr_measurable hf) continuous_id

/-! ## Layer-cake formulas on initial segments -/

theorem integral_Iic_eq_layercake {f : I → ℝ} (hf0 : ∀ u, 0 ≤ f u) (hf : ∀ u, f u ≤ 1)
    (hm : Measurable f) (A : Set I) :
    (∫ u in A, f u) = ∫ t in Ioc (0 : ℝ) 1, volume.real (A ∩ {u : I | t < f u}) := by
  have hi : Integrable f (volume.restrict A) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 u)]; exact hf u
  rw [hi.integral_eq_integral_meas_lt (Eventually.of_forall hf0),
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self]
  · apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    simp only
    rw [measureReal_restrict_apply (measurableSet_lt measurable_const hm), inter_comm]
  · intro t ht
    have ht1 : (1 : ℝ) < t := by
      rcases ht with ⟨h0, h1⟩
      simp only [mem_Ioi, mem_Ioc, not_and, not_le] at h0 h1
      exact h1 h0
    have : {a : I | t < f a} = ∅ := by
      ext a; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      linarith [hf a]
    simp [this]

theorem antitone_measureReal_inter (A : Set I) (f : I → ℝ) :
    Antitone (fun t : ℝ => volume.real (A ∩ {u : I | t < f u})) :=
  fun a b hab => measureReal_mono
    (inter_subset_inter_right _ (fun u (hu : b < f u) => (lt_of_le_of_lt hab hu : a < f u)))

theorem volume_Iic_inter_lt_decRearr {f : I → ℝ} (hf : ∀ u, f u ≤ 1) (x : I)
    {t : ℝ} (ht : 0 ≤ t) :
    volume.real (Iic x ∩ {s : I | t < decRearr f s}) = min (x : ℝ) (distFun f t) := by
  have hset : Iic x ∩ {s : I | t < decRearr f s} = Iic x ∩ {s : I | (s : ℝ) < distFun f t} := by
    ext s
    simp only [mem_inter_iff, mem_ofPred_eq]
    rw [lt_decRearr_iff hf ht s.property.1]
  rw [hset]
  have hd0 := distFun_nonneg f t
  have hd1 := distFun_le_one f t
  rcases le_total (x : ℝ) (distFun f t) with h | h
  · rw [min_eq_left h]
    have hsub : Iic x ∩ {s : I | (s : ℝ) < distFun f t} ⊆ Iic x := inter_subset_left
    have hsup : Iio x ⊆ Iic x ∩ {s : I | (s : ℝ) < distFun f t} := by
      intro s hs
      exact ⟨mem_Iic.mpr (mem_Iio.mp hs).le,
        lt_of_lt_of_le (Subtype.coe_lt_coe.mpr (mem_Iio.mp hs)) h⟩
    have h1 := measureReal_mono hsub (μ := (volume : Measure I))
    have h2 := measureReal_mono hsup (μ := (volume : Measure I))
    have hIic : volume.real (Iic x) = (x : ℝ) := by
      simp [measureReal_def, unitInterval.volume_Iic, ENNReal.toReal_ofReal x.property.1]
    have hIio : volume.real (Iio x) = (x : ℝ) := by
      simp [measureReal_def, unitInterval.volume_Iio, ENNReal.toReal_ofReal x.property.1]
    linarith
  · rw [min_eq_right h]
    have heq : Iic x ∩ {s : I | (s : ℝ) < distFun f t} = {s : I | (s : ℝ) < distFun f t} := by
      apply inter_eq_right.mpr
      intro s hs
      exact le_of_lt (lt_of_lt_of_le (hs : (s : ℝ) < distFun f t) h)
    rw [heq]
    have := unitInterval.volume_Iio (⟨distFun f t, hd0, hd1⟩ : I)
    have hv : volume {s : I | (s : ℝ) < distFun f t} = ENNReal.ofReal (distFun f t) := by
      simpa [Iio, ← Subtype.coe_lt_coe] using this
    rw [measureReal_def, hv, ENNReal.toReal_ofReal hd0]

/-- Layer-cake form of the partial integrals of the rearrangement. -/
theorem integral_Iic_decRearr {f : I → ℝ} (hf : ∀ u, f u ≤ 1) (x : I) :
    (∫ s in Iic x, decRearr f s) = ∫ t in Ioc (0 : ℝ) 1, min (x : ℝ) (distFun f t) := by
  rw [integral_Iic_eq_layercake (fun s => decRearr_nonneg hf s.property.1)
    (fun s => decRearr_le_one hf s.property.1) (decRearr_measurable hf) _]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  exact volume_Iic_inter_lt_decRearr hf x ht.1.le

/-- Hardy–Littlewood (bathtub principle) on arbitrary measurable sets: the integral of `f`
over a set of measure `x` is dominated by the integral of `f↓` over `[0, x]`. -/
theorem integral_set_le_decRearr {f : I → ℝ} (hf0 : ∀ u, 0 ≤ f u) (hf : ∀ u, f u ≤ 1)
    (hm : Measurable f) (A : Set I) (x : I) (hx : volume.real A = (x : ℝ)) :
    (∫ u in A, f u) ≤ ∫ s in Iic x, decRearr f s := by
  rw [integral_Iic_decRearr hf x, integral_Iic_eq_layercake hf0 hf hm A]
  have hb : ∀ t, volume.real (A ∩ {u : I | t < f u}) ≤ min (x : ℝ) (distFun f t) := by
    intro t
    apply le_min
    · rw [← hx]; exact measureReal_mono inter_subset_left
    · exact measureReal_mono inter_subset_right
  apply setIntegral_mono_on _ _ measurableSet_Ioc (fun t _ => hb t)
  · apply Measure.integrableOn_of_bounded (M := 1)
    · simp
    · exact (antitone_measureReal_inter A f).measurable.aestronglyMeasurable
    · exact Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        calc volume.real (A ∩ {u : I | t < f u}) ≤ volume.real (univ : Set I) :=
              measureReal_mono (subset_univ _)
          _ = 1 := by simp
  · apply Measure.integrableOn_of_bounded (M := 1)
    · simp
    · exact (Antitone.measurable
        (fun a b hab => min_le_min_left _ (distFun_antitone f hab))).aestronglyMeasurable
    · exact Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min x.property.1 (distFun_nonneg f t))]
        exact (min_le_right _ _).trans (distFun_le_one f t)

/-- Hardy–Littlewood on initial segments. -/
theorem integral_Iic_le_decRearr {f : I → ℝ} (hf0 : ∀ u, 0 ≤ f u) (hf : ∀ u, f u ≤ 1)
    (hm : Measurable f) (x : I) : (∫ u in Iic x, f u) ≤ ∫ s in Iic x, decRearr f s :=
  integral_set_le_decRearr hf0 hf hm (Iic x) x
    (by simp [measureReal_def, unitInterval.volume_Iic, ENNReal.toReal_ofReal x.property.1])

theorem decRearr_const_zero {s : ℝ} (hs : 0 ≤ s) : decRearr (fun _ : I => (0 : ℝ)) s = 0 := by
  apply le_antisymm _ (decRearr_nonneg (fun _ => zero_le_one) hs)
  apply csInf_le (decRearr_set_bdd _ s)
  refine ⟨le_rfl, ?_⟩
  unfold distFun
  simp [hs]

theorem decRearr_const_one {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    decRearr (fun _ : I => (1 : ℝ)) s = 1 := by
  apply le_antisymm (decRearr_le_one (fun _ => le_rfl) hs)
  apply le_csInf (decRearr_set_nonempty (fun _ => le_rfl) hs)
  intro c hc
  by_contra hlt
  push Not at hlt
  have : distFun (fun _ : I => (1 : ℝ)) c = 1 := by
    unfold distFun
    have : {u : I | c < (fun _ : I => (1 : ℝ)) u} = univ := by ext u; simp [hlt]
    simp [this]
  linarith [hc.2]

end ProbabilityTheory.Copula
