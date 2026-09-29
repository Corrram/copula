/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rearrangement.Decreasing
import Copula.Dependence.Conditional

/-! # Rearranging a derivative: the primitive of a mean-zero function

The primitive comparison lemma for decreasing rearrangements. For a measurable `h : I → [0,1]` with `∫ h = v`, put `f = h - v` (a bounded
mean-zero function) and

`F(u) = ∫_0^u f = ∫_0^u h - u v`,  `G(u) = ∫_0^u f↓ = ∫_0^u h↓ - u v`,

where `h↓ = decRearr h` is the decreasing rearrangement (`f↓ = h↓ - v`). This file proves the
structural statements: `G` is concave (chord inequality) and nonnegative, the
two-sided bound `-G(1 - λ(E)) ≤ ∫_E f ≤ G(λ(E))` for measurable `E`, hence
`-G(1-u) ≤ F(u) ≤ G(u)` and `|F| ≤ max G`, and the level-set inequality
`λ{|F| > y} ≤ λ{G > y}` for `y ≥ 0` (with a quantitative improvement when `F` takes both signs).
The integral consequences (`∫ |F|^p ≤ ∫ G^p` and the strict versions) are in
`Copula.Rearrangement.PrimitiveIntegral`.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The measure of a subset of the unit interval, as a point of the unit interval. -/
noncomputable def measureUnit (A : Set I) : I :=
  ⟨volume.real A, measureReal_nonneg, measureReal_le_one⟩

@[simp] theorem coe_measureUnit (A : Set I) : (measureUnit A : ℝ) = volume.real A := rfl

theorem measureUnit_Iic (u : I) : measureUnit (Iic u) = u := by
  apply Subtype.ext
  simp [measureUnit, measureReal_def, unitInterval.volume_Iic, ENNReal.toReal_ofReal u.property.1]

theorem measureReal_Ioo_unit (a b : I) (hab : a ≤ b) : volume.real (Ioo a b) = (b : ℝ) - a := by
  rw [measureReal_def, unitInterval.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

theorem measureReal_Icc_unit (a b : I) (hab : a ≤ b) : volume.real (Icc a b) = (b : ℝ) - a := by
  rw [measureReal_def, unitInterval.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

theorem measureReal_compl_unit (A : Set I) (hA : MeasurableSet A) :
    volume.real Aᶜ = 1 - volume.real A := by
  rw [measureReal_compl hA, probReal_univ]

/-! ## The primitive of a bounded function and its continuity -/

section Bounded

variable {h : I → ℝ}

/-- The primitive `u ↦ ∫_0^u h`, as a function on the unit interval. -/
noncomputable def primitive (h : I → ℝ) (u : I) : ℝ := ∫ t in Iic u, h t

theorem primitive_zero (h : I → ℝ) : primitive h 0 = 0 := by
  unfold primitive
  apply setIntegral_measure_zero
  rw [unitInterval.volume_Iic]
  simp

theorem primitive_one (h : I → ℝ) : primitive h 1 = ∫ t, h t := by
  unfold primitive
  rw [show Iic (1 : I) = univ from Iic_top, Measure.restrict_univ]

theorem integrable_of_unit_bounds (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1)
    (hm : Measurable h) : Integrable h :=
  integrable_comp_of_unit hf0 hf1 hm continuous_id

theorem primitive_sub_primitive (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1)
    (hm : Measurable h) {a b : I} (hab : a ≤ b) :
    primitive h b - primitive h a = ∫ t in Ioc a b, h t := by
  unfold primitive
  rw [← integral_Iic_add_Ioc_unit (integrable_of_unit_bounds hf0 hf1 hm) hab]
  ring

theorem primitive_sub_primitive_Ioo (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1)
    (hm : Measurable h) {a b : I} (hab : a ≤ b) :
    primitive h b - primitive h a = ∫ t in Ioo a b, h t := by
  rw [primitive_sub_primitive hf0 hf1 hm hab]
  exact integral_Ioc_eq_integral_Ioo

theorem primitive_mono (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1)
    (hm : Measurable h) {a b : I} (hab : a ≤ b) : primitive h a ≤ primitive h b := by
  have := primitive_sub_primitive hf0 hf1 hm hab
  have hn : 0 ≤ ∫ t in Ioc a b, h t := setIntegral_nonneg measurableSet_Ioc (fun t _ => hf0 t)
  linarith

theorem primitive_sub_le (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1)
    (hm : Measurable h) {a b : I} (hab : a ≤ b) :
    primitive h b - primitive h a ≤ (b : ℝ) - a := by
  rw [primitive_sub_primitive hf0 hf1 hm hab]
  have := setIntegral_mono_on (μ := volume) (s := Ioc a b)
    (integrable_of_unit_bounds hf0 hf1 hm).integrableOn
    (integrableOn_const (C := (1 : ℝ)) (by rw [unitInterval.volume_Ioc]; exact ENNReal.ofReal_ne_top))
    measurableSet_Ioc (fun t _ => hf1 t)
  rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, unitInterval.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] at this
  exact this

theorem continuous_primitive (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1)
    (hm : Measurable h) : Continuous (primitive h) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [Real.dist_eq, Subtype.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  rcases le_total a b with hab | hab
  · have h1 := primitive_sub_le hf0 hf1 hm hab
    have h2 := primitive_mono hf0 hf1 hm hab
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (sub_nonpos.mpr (show (a : ℝ) ≤ b from hab))]
    linarith
  · have h1 := primitive_sub_le hf0 hf1 hm hab
    have h2 := primitive_mono hf0 hf1 hm hab
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (sub_nonneg.mpr (show (b : ℝ) ≤ a from hab))]
    linarith

end Bounded

/-! ## The deviation functions `F` and `G` -/

/-- `F(u) = ∫_0^u h - u v`, the primitive of the mean-zero function `h - v`. -/
noncomputable def primDev (h : I → ℝ) (v : ℝ) (u : I) : ℝ := primitive h u - (u : ℝ) * v

/-- `G(u) = ∫_0^u h↓ - u v`, the primitive of the decreasing rearrangement `h↓ - v`. -/
noncomputable def rearrDev (h : I → ℝ) (v : ℝ) (u : I) : ℝ :=
  primitive (fun t => decRearr h t) u - (u : ℝ) * v

section Main

variable {h : I → ℝ} {v : ℝ}

theorem decRearr_nonneg' (hf1 : ∀ u, h u ≤ 1) (s : I) : 0 ≤ decRearr h s :=
  decRearr_nonneg hf1 s.property.1

theorem decRearr_le_one' (hf1 : ∀ u, h u ≤ 1) (s : I) : decRearr h s ≤ 1 :=
  decRearr_le_one hf1 s.property.1

theorem primDev_zero : primDev h v 0 = 0 := by simp [primDev, primitive_zero]

theorem rearrDev_zero : rearrDev h v 0 = 0 := by simp [rearrDev, primitive_zero]

theorem primDev_one (hv : (∫ u, h u) = v) : primDev h v 1 = 0 := by
  simp [primDev, primitive_one, hv]

theorem rearrDev_one (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1) (hm : Measurable h)
    (hv : (∫ u, h u) = v) : rearrDev h v 1 = 0 := by
  have h1 := integral_comp_decRearr hf0 hf1 hm (φ := id) measurable_id
  simp only [id] at h1
  simp [rearrDev, primitive_one, h1, hv]

theorem continuous_primDev (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1) (hm : Measurable h) :
    Continuous (primDev h v) :=
  (continuous_primitive hf0 hf1 hm).sub (by fun_prop)

theorem continuous_rearrDev (hf1 : ∀ u, h u ≤ 1) : Continuous (rearrDev h v) :=
  (continuous_primitive (decRearr_nonneg' hf1) (decRearr_le_one' hf1)
    (decRearr_measurable hf1)).sub (by fun_prop)

theorem measurable_primDev (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1) (hm : Measurable h) :
    Measurable (primDev h v) := (continuous_primDev hf0 hf1 hm).measurable

theorem measurable_rearrDev (hf1 : ∀ u, h u ≤ 1) : Measurable (rearrDev h v) :=
  (continuous_rearrDev hf1).measurable

/-- The chord inequality expressing concavity of `G`. -/
theorem rearrDev_chord (hf1 : ∀ u, h u ≤ 1) {a b c : I} (hab : a ≤ b) (hbc : b ≤ c) :
    ((b : ℝ) - a) * rearrDev h v c + ((c : ℝ) - b) * rearrDev h v a ≤
      ((c : ℝ) - a) * rearrDev h v b := by
  unfold rearrDev primitive
  set f := fun s : I => decRearr h s
  have hfi : Integrable f := integrable_decRearr hf1
  have hanti : ∀ s t : I, s ≤ t → f t ≤ f s := fun s t hst =>
    decRearr_antitoneOn hf1 s.property.1 t.property.1 hst
  have hdiff (x y : I) (hxy : x ≤ y) :
      (∫ s in Iic y, f s) - (∫ s in Iic x, f s) = ∫ s in Ioc x y, f s := by
    rw [← Iic_sdiff_Iic, setIntegral_sdiff measurableSet_Iic hfi.integrableOn
      (Iic_subset_Iic.mpr hxy)]
  have hlen (x y : I) (hxy : x ≤ y) : volume.real (Ioc x y) = (y : ℝ) - x := by
    rw [measureReal_def, unitInterval.volume_Ioc]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr hxy)
  have h1 : ((b : ℝ) - a) * f b ≤ ∫ s in Ioc a b, f s := by
    have := setIntegral_ge_of_const_le_real (μ := volume) (s := Ioc a b) (f := f)
      measurableSet_Ioc (by rw [unitInterval.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      (fun s hs => hanti s b hs.2) hfi.integrableOn
    rwa [hlen a b hab, mul_comm] at this
  have h2 : (∫ s in Ioc b c, f s) ≤ ((c : ℝ) - b) * f b := by
    have := setIntegral_mono_on (μ := volume) (s := Ioc b c) hfi.integrableOn
      (integrableOn_const (C := f b)
        (by rw [unitInterval.volume_Ioc]; exact ENNReal.ofReal_ne_top))
      measurableSet_Ioc (fun s hs => hanti b s (le_of_lt hs.1))
    rwa [setIntegral_const, smul_eq_mul, hlen b c hbc] at this
  have e1 := hdiff a b hab
  have e2 := hdiff b c hbc
  have hba : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr hab
  have hcb : 0 ≤ (c : ℝ) - b := sub_nonneg.mpr hbc
  nlinarith [mul_le_mul_of_nonneg_left h1 hcb, mul_le_mul_of_nonneg_left h2 hba]

/-- The rearranged primitive is nonnegative: `G ≥ 0`. -/
theorem rearrDev_nonneg (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1) (hm : Measurable h)
    (hv : (∫ u, h u) = v) (u : I) : 0 ≤ rearrDev h v u := by
  have hc := rearrDev_chord (v := v) hf1 (show (0 : I) ≤ u from u.property.1)
    (show u ≤ 1 from u.property.2)
  rw [rearrDev_zero, rearrDev_one hf0 hf1 hm hv] at hc
  simp only [Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, add_zero, sub_zero, one_mul] at hc
  exact hc

/-- Concavity keeps `G ≥ y` on the interval between two points where `G ≥ y`. -/
theorem rearrDev_ge_of_ge (hf1 : ∀ u, h u ≤ 1) {y : ℝ} {a b c : I} (hab : a ≤ b) (hbc : b ≤ c)
    (ha : y ≤ rearrDev h v a) (hc : y ≤ rearrDev h v c) : y ≤ rearrDev h v b := by
  have hch := rearrDev_chord (v := v) hf1 hab hbc
  rcases eq_or_lt_of_le (hab.trans hbc) with hac | hac
  · have : b = a := le_antisymm (hbc.trans hac.symm.le) hab
    rw [this]; exact ha
  · have hpos : 0 < (c : ℝ) - a := sub_pos.mpr hac
    have hba : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr hab
    have hcb : 0 ≤ (c : ℝ) - b := sub_nonneg.mpr hbc
    have : ((c : ℝ) - a) * y ≤ ((c : ℝ) - a) * rearrDev h v b := by
      nlinarith [mul_le_mul_of_nonneg_left hc hba, mul_le_mul_of_nonneg_left ha hcb]
    exact le_of_mul_le_mul_left this hpos

theorem rearrDev_le_one (hf1 : ∀ u, h u ≤ 1) (hv0 : 0 ≤ v) (u : I) : rearrDev h v u ≤ 1 := by
  unfold rearrDev
  have h1 := primitive_sub_le (decRearr_nonneg' hf1) (decRearr_le_one' hf1)
    (decRearr_measurable hf1) (show (0 : I) ≤ u from u.property.1)
  rw [primitive_zero] at h1
  simp only [Set.Icc.coe_zero, sub_zero] at h1
  nlinarith [u.property.1, u.property.2, mul_nonneg u.property.1 hv0]

/-- Two-sided bound, upper half: `∫_E f ≤ G(λ(E))` for every measurable `E` (bathtub principle). -/
theorem integral_set_sub_le_rearrDev (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1)
    (hm : Measurable h) (E : Set I) :
    (∫ u in E, h u) - volume.real E * v ≤ rearrDev h v (measureUnit E) := by
  unfold rearrDev primitive
  have := integral_set_le_decRearr hf0 hf1 hm E (measureUnit E) rfl
  simp only [coe_measureUnit]
  linarith

/-- Two-sided bound, lower half: `-G(1 - λ(E)) ≤ ∫_E f` for every measurable `E`. -/
theorem neg_rearrDev_le_integral_set_sub (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1)
    (hm : Measurable h) (hv : (∫ u, h u) = v) (E : Set I) (hE : MeasurableSet E) :
    -rearrDev h v (unitInterval.symm (measureUnit E)) ≤ (∫ u in E, h u) - volume.real E * v := by
  have hc := integral_set_sub_le_rearrDev (v := v) hf0 hf1 hm Eᶜ
  have hsplit : (∫ u in E, h u) + (∫ u in Eᶜ, h u) = v := by
    rw [← hv]; exact integral_add_compl hE (integrable_of_unit_bounds hf0 hf1 hm)
  have hmeas : measureUnit Eᶜ = unitInterval.symm (measureUnit E) := by
    apply Subtype.ext
    simp [measureUnit, measureReal_compl_unit E hE, unitInterval.coe_symm_eq]
  rw [hmeas, measureReal_compl_unit E hE] at hc
  linarith

/-- `F ≤ G` pointwise. -/
theorem primDev_le_rearrDev (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1) (hm : Measurable h)
    (u : I) : primDev h v u ≤ rearrDev h v u := by
  have := integral_set_sub_le_rearrDev (v := v) hf0 hf1 hm (Iic u)
  rw [measureUnit_Iic] at this
  unfold primDev primitive
  have hu : volume.real (Iic u) = (u : ℝ) := by
    simp [measureReal_def, unitInterval.volume_Iic, ENNReal.toReal_ofReal u.property.1]
  rw [hu] at this
  exact this

/-- `-G(1-u) ≤ F(u)`. -/
theorem neg_rearrDev_symm_le_primDev (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1)
    (hm : Measurable h) (hv : (∫ u, h u) = v) (u : I) :
    -rearrDev h v (unitInterval.symm u) ≤ primDev h v u := by
  have := neg_rearrDev_le_integral_set_sub hf0 hf1 hm hv (Iic u) measurableSet_Iic
  rw [measureUnit_Iic] at this
  unfold primDev primitive
  have hu : volume.real (Iic u) = (u : ℝ) := by
    simp [measureReal_def, unitInterval.volume_Iic, ENNReal.toReal_ofReal u.property.1]
  rw [hu] at this
  exact this

/-- `|F| ≤ max G`, in pointwise form. -/
theorem abs_primDev_le_max (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1) (hm : Measurable h)
    (hv : (∫ u, h u) = v) (u : I) :
    |primDev h v u| ≤ max (rearrDev h v u) (rearrDev h v (unitInterval.symm u)) := by
  apply abs_le.mpr
  constructor
  · have := neg_rearrDev_symm_le_primDev hf0 hf1 hm hv u
    linarith [le_max_right (rearrDev h v u) (rearrDev h v (unitInterval.symm u))]
  · exact (primDev_le_rearrDev hf0 hf1 hm u).trans (le_max_left _ _)

theorem abs_primDev_le_one (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1) (hm : Measurable h)
    (hv : (∫ u, h u) = v) (u : I) : |primDev h v u| ≤ 1 := by
  have hv0 : 0 ≤ v := by rw [← hv]; exact integral_nonneg hf0
  exact (abs_primDev_le_max hf0 hf1 hm hv u).trans
    (max_le (rearrDev_le_one hf1 hv0 u) (rearrDev_le_one hf1 hv0 _))

end Main

end ProbabilityTheory.Copula
