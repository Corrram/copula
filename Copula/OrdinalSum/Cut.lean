/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.Properties

/-! # Diagonal fixed points as copula cuts

If `C(a,a)=a`, each section through the cut agrees with the upper Fréchet
bound. The two off-diagonal rectangles are consequently determined.
The threshold indicators agree almost surely exactly at such a cut.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem cdf_right_cut_of_le (C : Copula 2) (a u : I)
    (ha : C.diagonal a = a) (hu : u ≤ a) : C.cdf ![u, a] = u := by
  have hi := C.rectangleIncrement_cdf_nonneg ![u, a] ![a, 1] (by
    intro i; fin_cases i
    · exact hu
    · exact a.property.2)
  simp only [rectangleIncrement_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    cdf_two_one_right] at hi
  change C.cdf ![a, a] = (a : ℝ) at ha
  have hb : C.cdf ![u, a] ≤ (u : ℝ) := C.cdf_le_coord ![u, a] 0
  linarith

theorem cdf_left_cut_of_le (C : Copula 2) (a v : I)
    (ha : C.diagonal a = a) (hv : v ≤ a) : C.cdf ![a, v] = v := by
  have hi := C.rectangleIncrement_cdf_nonneg ![a, v] ![1, a] (by
    intro i; fin_cases i
    · exact a.property.2
    · exact hv)
  simp only [rectangleIncrement_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    cdf_two_one_left] at hi
  change C.cdf ![a, a] = (a : ℝ) at ha
  have hb : C.cdf ![a, v] ≤ (v : ℝ) := C.cdf_le_coord ![a, v] 1
  linarith

theorem cdf_right_cut_of_ge (C : Copula 2) (a u : I)
    (ha : C.diagonal a = a) (hu : a ≤ u) : C.cdf ![u, a] = a := by
  have hm : C.cdf ![a, a] ≤ C.cdf ![u, a] := C.monotone_cdf (by
    intro i; fin_cases i
    · exact hu
    · exact le_rfl)
  change C.cdf ![a, a] = (a : ℝ) at ha
  have hb : C.cdf ![u, a] ≤ (a : ℝ) := C.cdf_le_coord ![u, a] 1
  linarith

theorem cdf_left_cut_of_ge (C : Copula 2) (a v : I)
    (ha : C.diagonal a = a) (hv : a ≤ v) : C.cdf ![a, v] = a := by
  have hm : C.cdf ![a, a] ≤ C.cdf ![a, v] := C.monotone_cdf (by
    intro i; fin_cases i
    · exact le_rfl
    · exact hv)
  change C.cdf ![a, a] = (a : ℝ) at ha
  have hb : C.cdf ![a, v] ≤ (a : ℝ) := C.cdf_le_coord ![a, v] 0
  linarith

theorem cdf_right_cut (C : Copula 2) (a u : I) (ha : C.diagonal a = a) :
    C.cdf ![u, a] = min (u : ℝ) a := by
  rcases le_total u a with hu | hu
  · rw [C.cdf_right_cut_of_le a u ha hu, min_eq_left (show (u : ℝ) ≤ a from hu)]
  · rw [C.cdf_right_cut_of_ge a u ha hu, min_eq_right (show (a : ℝ) ≤ u from hu)]

theorem cdf_left_cut (C : Copula 2) (a v : I) (ha : C.diagonal a = a) :
    C.cdf ![a, v] = min (a : ℝ) v := by
  rcases le_total v a with hv | hv
  · rw [C.cdf_left_cut_of_le a v ha hv, min_eq_right (show (v : ℝ) ≤ a from hv)]
  · rw [C.cdf_left_cut_of_ge a v ha hv, min_eq_left (show (a : ℝ) ≤ v from hv)]

theorem cdf_cross_cut_lower_upper (C : Copula 2) (a u v : I)
    (ha : C.diagonal a = a) (hu : u ≤ a) (hv : a ≤ v) : C.cdf ![u, v] = u := by
  have hm : C.cdf ![u, a] ≤ C.cdf ![u, v] := C.monotone_cdf (by
    intro i; fin_cases i
    · exact le_rfl
    · exact hv)
  rw [C.cdf_right_cut_of_le a u ha hu] at hm
  exact le_antisymm (C.cdf_le_coord ![u, v] 0) hm

theorem cdf_cross_cut_upper_lower (C : Copula 2) (a u v : I)
    (ha : C.diagonal a = a) (hu : a ≤ u) (hv : v ≤ a) : C.cdf ![u, v] = v := by
  have hm : C.cdf ![a, v] ≤ C.cdf ![u, v] := C.monotone_cdf (by
    intro i; fin_cases i
    · exact hu
    · exact le_rfl)
  rw [C.cdf_left_cut_of_le a v ha hv] at hm
  exact le_antisymm (C.cdf_le_coord ![u, v] 1) hm

/-- Disagreement of the two threshold indicators measures the diagonal's deficit. -/
theorem measureReal_threshold_disagreement (C : Copula 2) (a : I) :
    C.toMeasure.real {x | ¬ (x 0 ≤ a ↔ x 1 ≤ a)} = 2 * ((a : ℝ) - C.diagonal a) := by
  have he : {x : Fin 2 → I | ¬ (x 0 ≤ a ↔ x 1 ≤ a)} =
      {x | min (x 0) (x 1) ≤ a} \ {x | max (x 0) (x 1) ≤ a} := by
    ext x
    simp only [mem_ofPred_eq, mem_sdiff, min_le_iff, max_le_iff]
    tauto
  have hs : {x : Fin 2 → I | max (x 0) (x 1) ≤ a} ⊆ {x | min (x 0) (x 1) ≤ a} := by
    intro x hx
    exact (min_le_max : min (x 0) (x 1) ≤ max (x 0) (x 1)).trans hx
  rw [he, measureReal_sdiff hs (measurableSet_le (by fun_prop) measurable_const),
    C.measureReal_min_le, C.measureReal_max_le]
  ring

theorem diagonal_eq_iff_ae_same_side (C : Copula 2) (a : I) :
    C.diagonal a = a ↔ ∀ᵐ x ∂C.toMeasure, x 0 ≤ a ↔ x 1 ≤ a := by
  rw [ae_iff, ← measureReal_eq_zero_iff, C.measureReal_threshold_disagreement]
  constructor <;> intro h <;> linarith

theorem diagonal_eq_iff_measureReal_max_eq_min (C : Copula 2) (a : I) :
    C.diagonal a = a ↔
      C.toMeasure.real {x | max (x 0) (x 1) ≤ a} = C.toMeasure.real {x | min (x 0) (x 1) ≤ a} := by
  rw [C.measureReal_min_le, C.measureReal_max_le]
  constructor <;> intro h <;> linarith

theorem isClosed_diagonal_fixedPoints (C : Copula 2) :
    IsClosed {a : I | C.diagonal a = (a : ℝ)} :=
  isClosed_eq C.continuous_diagonal continuous_subtype_val

theorem IsNQD.diagonal_lt {C : Copula 2} (h : C.IsNQD) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    C.diagonal a < (a : ℝ) := by
  have hb := h a a
  change C.diagonal a ≤ (a : ℝ) * a at hb
  have hp : (0 : ℝ) < a := ha0
  have hl : (a : ℝ) < 1 := ha1
  nlinarith [mul_pos hp (sub_pos.mpr hl)]

end ProbabilityTheory.Copula
