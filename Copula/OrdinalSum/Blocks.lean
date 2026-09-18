/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.Measure
import Copula.Order.Survival

/-! # Block probabilities and support of ordinal sums

The two coordinates belong to the same block almost surely. The lower
block has probability `a` and the upper block has probability `1-a`.
The statements include both degenerate splits.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

open OrdinalSum

theorem ae_ordinalSum_mem_blocks (C D : Copula 2) (a : I) :
    ∀ᵐ x ∂(C.ordinalSum D a).toMeasure, (∀ i, x i ≤ a) ∨ (∀ i, a ≤ x i) := by
  have hs : MeasurableSet {x : Fin 2 → I | (∀ i, x i ≤ a) ∨ (∀ i, a ≤ x i)} :=
    (measurableSet_le measurable_id (measurable_const (a := fun _ : Fin 2 => a))).union
      (measurableSet_le (measurable_const (a := fun _ : Fin 2 => a)) measurable_id)
  have hmL : Measurable (fun (x : Fin 2 → I) i => lowerEmbed a (x i)) := by fun_prop
  have hmU : Measurable (fun (x : Fin 2 → I) i => upperEmbed a (x i)) := by fun_prop
  rw [toMeasure_ordinalSum, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    apply (ae_map_iff hmL.aemeasurable hs).2
    exact Filter.Eventually.of_forall fun x => Or.inl fun i => lowerEmbed_le a (x i)
  · apply Measure.ae_smul_measure
    apply (ae_map_iff hmU.aemeasurable hs).2
    exact Filter.Eventually.of_forall fun x => Or.inr fun i => le_upperEmbed a (x i)

theorem measureReal_ordinalSum_lower_block (C D : Copula 2) (a : I) :
    (C.ordinalSum D a).toMeasure.real {x | ∀ i, x i ≤ a} = a := by
  change (C.ordinalSum D a).cdf (fun _ => a) = _
  have he : (fun _ : Fin 2 => a) = ![a, a] := by ext i; fin_cases i <;> rfl
  rw [he, cdf_ordinalSum_split]

theorem measureReal_ordinalSum_upper_block (C D : Copula 2) (a : I) :
    (C.ordinalSum D a).toMeasure.real {x | ∀ i, a ≤ x i} = 1 - (a : ℝ) := by
  change (C.ordinalSum D a).survival (fun _ => a) = _
  have he : (fun _ : Fin 2 => a) = ![a, a] := by ext i; fin_cases i <;> rfl
  rw [he, survival_two, cdf_ordinalSum_split]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem measure_ordinalSum_cross_blocks (C D : Copula 2) (a : I) :
    (C.ordinalSum D a).toMeasure
      {x | (x 0 < a ∧ a < x 1) ∨ (x 1 < a ∧ a < x 0)} = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ae_ordinalSum_mem_blocks C D a] with x hx
  rintro (⟨h0, h1⟩ | ⟨h1, h0⟩)
  · rcases hx with hl | hu
    · exact (not_lt_of_ge (hl 1)) h1
    · exact (not_lt_of_ge (hu 0)) h0
  · rcases hx with hl | hu
    · exact (not_lt_of_ge (hl 0)) h0
    · exact (not_lt_of_ge (hu 1)) h1

theorem ae_ordinalSum_same_side (C D : Copula 2) (a : I) :
    ∀ᵐ x ∂(C.ordinalSum D a).toMeasure, x 0 ≤ a ↔ x 1 ≤ a := by
  filter_upwards [ae_ordinalSum_mem_blocks C D a,
    (C.ordinalSum D a).ae_eval_ne 0 a, (C.ordinalSum D a).ae_eval_ne 1 a] with x hx h0 h1
  rcases hx with hl | hu
  · exact iff_of_true (hl 0) (hl 1)
  · exact iff_of_false (fun h => h0 (le_antisymm h (hu 0)))
      (fun h => h1 (le_antisymm h (hu 1)))

end ProbabilityTheory.Copula
