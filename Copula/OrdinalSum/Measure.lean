/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.Basic
import Copula.Rank.Integration

/-! # Probability measures and integration for binary ordinal sums

The ordinal-sum measure is the weighted sum of the two component measures
pushed into their respective squares. This representation also covers
singular copulas and zero-length blocks.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace OrdinalSum

@[fun_prop] theorem continuous_lowerEmbed (a : I) : Continuous (lowerEmbed a) := by
  apply Continuous.subtype_mk
  exact continuous_const.mul continuous_subtype_val

@[fun_prop] theorem continuous_upperEmbed (a : I) : Continuous (upperEmbed a) := by
  apply Continuous.subtype_mk
  exact continuous_const.add (continuous_const.mul continuous_subtype_val)

@[fun_prop] theorem measurable_lowerEmbed (a : I) : Measurable (lowerEmbed a) :=
  (continuous_lowerEmbed a).measurable

@[fun_prop] theorem measurable_upperEmbed (a : I) : Measurable (upperEmbed a) :=
  (continuous_upperEmbed a).measurable

theorem lowerEmbed_le_iff (a x u : I) (ha : 0 < a) :
    lowerEmbed a x ≤ u ↔ x ≤ lowerCoord a u := by
  rcases le_total a u with hu | hu
  · rw [lowerCoord_of_ge a u ha hu]
    exact iff_of_true ((lowerEmbed_le a x).trans hu) x.property.2
  · change (a : ℝ) * x ≤ u ↔ (x : ℝ) ≤ lowerCoord a u
    rw [coe_lowerCoord_of_le a u ha hu, le_div_iff₀ (show (0 : ℝ) < a from ha), mul_comm]

theorem upperEmbed_le_iff (a x u : I) (ha : a < 1) (hu : a ≤ u) :
    upperEmbed a x ≤ u ↔ x ≤ upperCoord a u := by
  change (a : ℝ) + (1 - (a : ℝ)) * x ≤ u ↔ (x : ℝ) ≤ upperCoord a u
  rw [coe_upperCoord_of_ge a u ha hu, le_div_iff₀ (sub_pos.mpr (show (a : ℝ) < 1 from ha))]
  constructor <;> intro h <;> nlinarith only [h]

theorem measureReal_map_lowerEmbed_Iic (C : Copula 2) (a : I) (ha : 0 < a)
    (u : Fin 2 → I) :
    (C.toMeasure.map (fun x i => lowerEmbed a (x i))).real (Iic u) =
      C.cdf (fun i => lowerCoord a (u i)) := by
  rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
  have he : (fun x i => lowerEmbed a (x i)) ⁻¹' Iic u = Iic (fun i => lowerCoord a (u i)) := by
    ext x
    simp only [mem_preimage, mem_Iic, Pi.le_def, lowerEmbed_le_iff a _ _ ha]
  rw [he]
  rfl

theorem measureReal_map_upperEmbed_Iic (C : Copula 2) (a : I) (ha : a < 1)
    (u : Fin 2 → I) :
    (C.toMeasure.map (fun x i => upperEmbed a (x i))).real (Iic u) =
      C.cdf (fun i => upperCoord a (u i)) := by
  rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
  by_cases hu : ∀ i, a ≤ u i
  · have he : (fun x i => upperEmbed a (x i)) ⁻¹' Iic u = Iic (fun i => upperCoord a (u i)) := by
      ext x
      simp only [mem_preimage, mem_Iic, Pi.le_def]
      exact forall_congr' fun i => upperEmbed_le_iff a (x i) (u i) ha (hu i)
    rw [he]
    rfl
  · obtain ⟨i, hi⟩ := not_forall.mp hu
    have he : (fun (x : Fin 2 → I) i => upperEmbed a (x i)) ⁻¹' Iic u = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hi ((le_upperEmbed a (x i)).trans (hx i))
    rw [he, measureReal_empty, C.cdf_eq_zero_of_coord_eq_zero _ i
      (upperCoord_of_le a (u i) (le_of_lt (lt_of_not_ge hi)))]

end OrdinalSum

open OrdinalSum

/-- Identify a candidate probability law by its lower-orthant probabilities. -/
theorem toMeasure_eq_of_measureReal_Iic {d : ℕ} (C : Copula d)
    (μ : Measure (Fin d → I)) [hprob : IsProbabilityMeasure μ]
    (hμ : ∀ u, μ.real (Iic u) = C.cdf u) : C.toMeasure = μ := by
  let D := C.isClassical_cdf.ofMeasure ⟨μ, hprob⟩ hμ
  have he : D = C := cdf_injective (C.isClassical_cdf.cdf_ofMeasure ⟨μ, hprob⟩ hμ)
  rw [← he]
  rfl

theorem toMeasure_ordinalSum (C D : Copula 2) (a : I) :
    (C.ordinalSum D a).toMeasure =
      ENNReal.ofReal (a : ℝ) • C.toMeasure.map (fun x i => lowerEmbed a (x i)) +
      ENNReal.ofReal (1 - (a : ℝ)) • D.toMeasure.map (fun x i => upperEmbed a (x i)) := by
  by_cases ha0 : a = 0
  · subst a
    have he : (fun x : Fin 2 → I => fun i => upperEmbed 0 (x i)) = id := by
      funext x i
      apply Subtype.ext
      simp [upperEmbed]
    simp [he]
  by_cases ha1 : a = 1
  · subst a
    have he : (fun x : Fin 2 → I => fun i => lowerEmbed 1 (x i)) = id := by
      funext x i
      apply Subtype.ext
      simp [lowerEmbed]
    simp [he]
  have hp : 0 < a := lt_of_le_of_ne a.property.1 (Ne.symm ha0)
  have hl : a < 1 := lt_of_le_of_ne a.property.2 ha1
  have hmL : Measurable (fun (x : Fin 2 → I) i => lowerEmbed a (x i)) := by fun_prop
  have hmU : Measurable (fun (x : Fin 2 → I) i => upperEmbed a (x i)) := by fun_prop
  let μ := ENNReal.ofReal (a : ℝ) • C.toMeasure.map (fun x i => lowerEmbed a (x i)) +
    ENNReal.ofReal (1 - (a : ℝ)) • D.toMeasure.map (fun x i => upperEmbed a (x i))
  have hprob : IsProbabilityMeasure μ := ⟨by
    simp only [μ, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply hmL MeasurableSet.univ, Measure.map_apply hmU MeasurableSet.univ,
      preimage_univ, measure_univ, mul_one]
    rw [← ENNReal.ofReal_add a.property.1 (sub_nonneg.mpr a.property.2)]
    simp⟩
  let := hprob
  apply (C.ordinalSum D a).toMeasure_eq_of_measureReal_Iic μ
  intro u
  change (ENNReal.ofReal (a : ℝ) • C.toMeasure.map (fun x i => lowerEmbed a (x i)) +
    ENNReal.ofReal (1 - (a : ℝ)) • D.toMeasure.map (fun x i => upperEmbed a (x i))).real (Iic u) = _
  rw [measureReal_add_apply (by simp [Measure.smul_apply, ENNReal.mul_ne_top])
    (by simp [Measure.smul_apply, ENNReal.mul_ne_top]),
    measureReal_ennreal_smul_apply, measureReal_ennreal_smul_apply,
    measureReal_map_lowerEmbed_Iic C a hp, measureReal_map_upperEmbed_Iic D a hl,
    ENNReal.toReal_ofReal a.property.1, ENNReal.toReal_ofReal (sub_nonneg.mpr a.property.2)]
  have he (f : I → I) : (fun i => f (u i)) = ![f (u 0), f (u 1)] := by
    funext i; fin_cases i <;> rfl
  rw [he, he, cdf_ordinalSum, ordinalSumCDF]

/-- Integrate a continuous observable by integrating over each component square. -/
theorem integral_ordinalSum (C D : Copula 2) (a : I)
    {f : (Fin 2 → I) → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂(C.ordinalSum D a).toMeasure) =
      (a : ℝ) * (∫ x, f (fun i => lowerEmbed a (x i)) ∂C.toMeasure) +
      (1 - (a : ℝ)) * ∫ x, f (fun i => upperEmbed a (x i)) ∂D.toMeasure := by
  have hmL : Measurable (fun (x : Fin 2 → I) i => lowerEmbed a (x i)) := by fun_prop
  have hmU : Measurable (fun (x : Fin 2 → I) i => upperEmbed a (x i)) := by fun_prop
  rw [toMeasure_ordinalSum, integral_add_measure
    ((integrable_continuous_cube _ hf).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_continuous_cube _ hf).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure,
    integral_map hmL.aemeasurable hf.aestronglyMeasurable,
    integral_map hmU.aemeasurable hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal a.property.1, ENNReal.toReal_ofReal (sub_nonneg.mpr a.property.2)]
  rfl

end ProbabilityTheory.Copula
