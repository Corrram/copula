/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.ConditionalMixture
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Squared distance between conditional CDFs

The integrated squared difference separates copulas even though conditional
distributions are only defined almost everywhere. In particular, Chatterjee's
xi is zero exactly at independence. No density is assumed.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem eq_of_ae_eq_unit {f g : I → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[volume] g) : f = g := by
  let p := projIcc (0 : ℝ) 1 zero_le_one
  have hfc : Continuous (f ∘ p) := hf.comp continuous_projIcc
  have hgc : Continuous (g ∘ p) := hg.comp continuous_projIcc
  have he : (f ∘ p) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] (g ∘ p) := by
    rw [← unitInterval.measurePreserving_coe.map_eq]
    apply (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_eq_fun hfc.measurable hgc.measurable)).2
    filter_upwards [h] with t ht
    simpa [p] using ht
  have he' := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1) he
    hfc.continuousOn hgc.continuousOn
  funext t
  simpa [p] using he' t.property

/-- Nested almost-everywhere equality of conditional CDFs determines the copula. -/
theorem ext_conditionalCDF_ae {C D : Copula 2}
    (h : ∀ᵐ v : I, (fun u => C.conditionalCDF u v) =ᵐ[volume] fun u => D.conditionalCDF u v) :
    C = D := by
  have hcdf (u v : I) : C.cdf ![u, v] = D.cdf ![u, v] := by
    have he : (fun t : I => C.cdf ![u, t]) =ᵐ[volume] fun t => D.cdf ![u, t] := by
      filter_upwards [h] with t ht
      rw [C.cdf_eq_integral_conditionalCDF, D.cdf_eq_integral_conditionalCDF]
      exact integral_congr_ae (ae_restrict_of_ae ht)
    exact congrFun (eq_of_ae_eq_unit (C.continuous_cdf.comp (by fun_prop))
      (D.continuous_cdf.comp (by fun_prop)) he) v
  apply ext_cdf
  intro u
  have he : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
  rw [← he]
  exact hcdf _ _

theorem integrable_conditionalCDF_sub_sq (C D : Copula 2) (v : I) :
    Integrable (fun u => (C.conditionalCDF u v - D.conditionalCDF u v) ^ 2) := by
  refine (integrable_const (1 : ℝ)).mono'
    (((C.measurable_conditionalCDF_left v).sub
      (D.measurable_conditionalCDF_left v)).pow_const 2).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hC := C.conditionalCDF_nonneg u v
    have hD := D.conditionalCDF_nonneg u v
    have hC' := C.conditionalCDF_le_one u v
    have hD' := D.conditionalCDF_le_one u v
    apply (sq_le_one_iff_abs_le_one _).2
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem integrable_integral_conditionalCDF_sub_sq (C D : Copula 2) :
    Integrable (fun v : I => ∫ u : I, (C.conditionalCDF u v - D.conditionalCDF u v) ^ 2) := by
  refine (integrable_const (1 : ℝ)).mono'
    ((C.measurable_conditionalCDF.sub D.measurable_conditionalCDF).pow_const 2).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun v => by
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun u => sq_nonneg _)]
    have hm := integral_mono (C.integrable_conditionalCDF_sub_sq D v) (integrable_const (1 : ℝ))
      (fun u => by
        have hC := C.conditionalCDF_nonneg u v
        have hD := D.conditionalCDF_nonneg u v
        have hC' := C.conditionalCDF_le_one u v
        have hD' := D.conditionalCDF_le_one u v
        apply (sq_le_one_iff_abs_le_one _).2
        exact abs_le.mpr ⟨by linarith, by linarith⟩)
    simpa using hm

/-- Squared `L²` distance between the two conditional CDFs on the unit square. -/
noncomputable def conditionalCDFDistanceSq (C D : Copula 2) : ℝ :=
  ∫ v : I, ∫ u : I, (C.conditionalCDF u v - D.conditionalCDF u v) ^ 2

theorem conditionalCDFDistanceSq_nonneg (C D : Copula 2) : 0 ≤ C.conditionalCDFDistanceSq D :=
  integral_nonneg fun v => integral_nonneg fun u =>
    sq_nonneg (C.conditionalCDF u v - D.conditionalCDF u v)

theorem conditionalCDFDistanceSq_comm (C D : Copula 2) :
    C.conditionalCDFDistanceSq D = D.conditionalCDFDistanceSq C := by
  simp only [conditionalCDFDistanceSq, sub_sq_comm]

@[simp] theorem conditionalCDFDistanceSq_self (C : Copula 2) : C.conditionalCDFDistanceSq C = 0 := by
  simp [conditionalCDFDistanceSq]

theorem conditionalCDFDistanceSq_eq_zero_iff (C D : Copula 2) :
    C.conditionalCDFDistanceSq D = 0 ↔ C = D := by
  refine ⟨fun hz => ?_, fun h => h ▸ conditionalCDFDistanceSq_self D⟩
  have ht := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun v : I => integral_nonneg fun u : I =>
      sq_nonneg (C.conditionalCDF u v - D.conditionalCDF u v))
    (C.integrable_integral_conditionalCDF_sub_sq D)).1 hz
  apply ext_conditionalCDF_ae
  filter_upwards [ht] with v hv
  have hu := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun u : I => sq_nonneg (C.conditionalCDF u v - D.conditionalCDF u v))
    (C.integrable_conditionalCDF_sub_sq D v)).1 hv
  filter_upwards [hu] with u hu
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hu)

theorem conditionalCDFDistanceSq_pos_iff (C D : Copula 2) :
    0 < C.conditionalCDFDistanceSq D ↔ C ≠ D := by
  rw [lt_iff_le_and_ne, and_iff_right (C.conditionalCDFDistanceSq_nonneg D), ne_comm]
  exact not_congr (C.conditionalCDFDistanceSq_eq_zero_iff D)

theorem chatterjeeXi_eq_distance_independence (C : Copula 2) :
    C.chatterjeeXi = 6 * C.conditionalCDFDistanceSq (independence 2) := by
  rw [C.chatterjeeXi_eq_integral_centered_sq, conditionalCDFDistanceSq]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => integral_congr_ae (by
    filter_upwards [conditionalCDF_independence v] with u hu
    rw [hu])

/-- Chatterjee's xi detects every departure from independence, including singular laws. -/
theorem chatterjeeXi_eq_zero_iff (C : Copula 2) : C.chatterjeeXi = 0 ↔ C = independence 2 := by
  rw [C.chatterjeeXi_eq_distance_independence]
  simp [conditionalCDFDistanceSq_eq_zero_iff]

theorem chatterjeeXi_pos_iff (C : Copula 2) : 0 < C.chatterjeeXi ↔ C ≠ independence 2 := by
  rw [lt_iff_le_and_ne, and_iff_right C.chatterjeeXi_nonneg, ne_comm]
  exact not_congr C.chatterjeeXi_eq_zero_iff

end ProbabilityTheory.Copula
