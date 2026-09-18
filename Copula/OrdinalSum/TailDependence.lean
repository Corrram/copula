/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.Properties
import Copula.TailDependence.Basic

/-! # Tail dependence of ordinal sums

A positive lower block determines lower-tail dependence, and a positive
upper block determines upper-tail dependence. The equivalences include
existence of the limits; no differentiability or density is assumed.
-/

open Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

open OrdinalSum

private theorem tendsto_lowerCoord_zero (a : I) (ha : 0 < a) :
    Tendsto (lowerCoord a) (𝓝[>] (0 : I)) (𝓝[>] (0 : I)) := by
  apply tendsto_nhdsWithin_iff.2
  constructor
  · simpa using ((continuous_lowerCoord a).tendsto (0 : I)).mono_left nhdsWithin_le_nhds
  · filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < t)] with t ht
    rcases le_total t a with hta | hta
    · change (0 : ℝ) < lowerCoord a t
      rw [coe_lowerCoord_of_le a t ha hta]
      exact div_pos ht ha
    · rw [lowerCoord_of_ge a t ha hta]
      norm_num

private theorem tendsto_lowerEmbed_zero (a : I) (ha : 0 < a) :
    Tendsto (lowerEmbed a) (𝓝[>] (0 : I)) (𝓝[>] (0 : I)) := by
  have hc : Continuous (lowerEmbed a) := by unfold lowerEmbed; fun_prop
  apply tendsto_nhdsWithin_iff.2
  constructor
  · simpa [lowerEmbed] using (hc.tendsto (0 : I)).mono_left nhdsWithin_le_nhds
  · filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < t)] with t ht
    exact mul_pos ha ht

theorem lowerTailRatio_ordinalSum (C D : Copula 2) (a t : I)
    (ha : 0 < a) (ht : 0 < t) (hta : t ≤ a) :
    (C.ordinalSum D a).lowerTailRatio t = C.lowerTailRatio (lowerCoord a t) := by
  rw [lowerTailRatio, diagonal_ordinalSum_lower C D a t hta,
    lowerTailRatio, coe_lowerCoord_of_le a t ha hta]
  have ha' : (0 : ℝ) < a := ha
  have ht' : (0 : ℝ) < t := ht
  field_simp [ha'.ne', ht'.ne']

private theorem upperCoord_symm (a t : I) (ha : a < 1) (ht : t ≤ unitInterval.symm a) :
    upperCoord a (unitInterval.symm t) = unitInterval.symm (lowerCoord (unitInterval.symm a) t) := by
  have hq : 0 < unitInterval.symm a := by
    change (0 : ℝ) < 1 - a
    exact sub_pos.mpr ha
  have hat : a ≤ unitInterval.symm t := by
    change (a : ℝ) ≤ 1 - t
    change (t : ℝ) ≤ 1 - a at ht
    linarith
  apply Subtype.ext
  rw [coe_upperCoord_of_ge a _ ha hat]
  simp only [unitInterval.coe_symm_eq]
  rw [coe_lowerCoord_of_le _ t hq ht]
  simp only [unitInterval.coe_symm_eq]
  have hp : (0 : ℝ) < 1 - a := sub_pos.mpr ha
  field_simp [hp.ne']
  ring

theorem upperTailRatio_ordinalSum (C D : Copula 2) (a t : I)
    (ha : a < 1) (ht : 0 < t) (hta : t ≤ unitInterval.symm a) :
    (C.ordinalSum D a).upperTailRatio t = D.upperTailRatio (lowerCoord (unitInterval.symm a) t) := by
  have hq : 0 < unitInterval.symm a := by
    change (0 : ℝ) < 1 - a
    exact sub_pos.mpr ha
  have hat : a ≤ unitInterval.symm t := by
    change (a : ℝ) ≤ 1 - t
    change (t : ℝ) ≤ 1 - a at hta
    linarith
  rw [upperTailRatio_eq, diagonal_ordinalSum_upper C D a _ hat, upperCoord_symm a t ha hta,
    D.upperTailRatio_eq, coe_lowerCoord_of_le _ t hq hta]
  simp only [unitInterval.coe_symm_eq]
  have hp : (0 : ℝ) < 1 - a := sub_pos.mpr ha
  have ht' : (0 : ℝ) < t := ht
  field_simp [hp.ne', ht'.ne']
  ring

theorem HasLowerTailDependence.ordinalSum {C : Copula 2} {l : ℝ}
    (h : C.HasLowerTailDependence l) (D : Copula 2) (a : I) (ha : 0 < a) :
    (C.ordinalSum D a).HasLowerTailDependence l := by
  apply (h.comp (tendsto_lowerCoord_zero a ha)).congr'
  filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < t),
    (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with t ht hta
  exact (lowerTailRatio_ordinalSum C D a t ha ht hta.le).symm

theorem HasUpperTailDependence.ordinalSum {D : Copula 2} {l : ℝ}
    (h : D.HasUpperTailDependence l) (C : Copula 2) (a : I) (ha : a < 1) :
    (C.ordinalSum D a).HasUpperTailDependence l := by
  have hq : 0 < unitInterval.symm a := by
    change (0 : ℝ) < 1 - a
    exact sub_pos.mpr ha
  apply (h.comp (tendsto_lowerCoord_zero _ hq)).congr'
  filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < t),
    (eventually_lt_nhds hq).filter_mono nhdsWithin_le_nhds] with t ht hta
  exact (upperTailRatio_ordinalSum C D a t ha ht hta.le).symm

theorem hasLowerTailDependence_ordinalSum_iff (C D : Copula 2) (a : I) (ha : 0 < a) (l : ℝ) :
    (C.ordinalSum D a).HasLowerTailDependence l ↔ C.HasLowerTailDependence l := by
  refine ⟨fun h => ?_, fun h => h.ordinalSum D a ha⟩
  apply (h.comp (tendsto_lowerEmbed_zero a ha)).congr'
  filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < t)] with t ht
  change (C.ordinalSum D a).lowerTailRatio (lowerEmbed a t) = C.lowerTailRatio t
  rw [lowerTailRatio_ordinalSum C D a (lowerEmbed a t) ha (mul_pos ha ht) (lowerEmbed_le a t),
    lowerCoord_lowerEmbed a t ha]

theorem hasUpperTailDependence_ordinalSum_iff (C D : Copula 2) (a : I) (ha : a < 1) (l : ℝ) :
    (C.ordinalSum D a).HasUpperTailDependence l ↔ D.HasUpperTailDependence l := by
  refine ⟨fun h => ?_, fun h => h.ordinalSum C a ha⟩
  have hq : 0 < unitInterval.symm a := by
    change (0 : ℝ) < 1 - a
    exact sub_pos.mpr ha
  apply (h.comp (tendsto_lowerEmbed_zero _ hq)).congr'
  filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < t)] with t ht
  change (C.ordinalSum D a).upperTailRatio (lowerEmbed (unitInterval.symm a) t) = D.upperTailRatio t
  rw [upperTailRatio_ordinalSum C D a (lowerEmbed (unitInterval.symm a) t) ha
      (mul_pos hq ht) (lowerEmbed_le _ t),
    lowerCoord_lowerEmbed _ t hq]

end ProbabilityTheory.Copula
