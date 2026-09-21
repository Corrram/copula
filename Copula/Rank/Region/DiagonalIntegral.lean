/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Diagonal
import Copula.Rank.Concordance

/-! # The diagonal evaluated at a coordinate maximum

The integral identity in Kokol Bukovšek–Stopar (2023), Proposition 1,
holds directly for every copula measure: the maximum has no atoms and
two independent copies are equally likely to occur in either order.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem ae_max_ne (C : Copula 2) (t : I) :
    ∀ᵐ x ∂C.toMeasure, max (x 0) (x 1) ≠ t := by
  filter_upwards [C.ae_eval_ne 0 t, C.ae_eval_ne 1 t] with x h0 h1
  rcases le_total (x 0) (x 1) with h | h
  · simpa only [max_eq_right h] using h1
  · simpa only [max_eq_left h] using h0

/-- The expected CDF of the atomless coordinate maximum is one half. -/
theorem integral_diagonal_max (C : Copula 2) :
    (∫ x, C.diagonal (max (x 0) (x 1)) ∂C.toMeasure) = 1 / 2 := by
  classical
  let m : (Fin 2 → I) → I := fun x => max (x 0) (x 1)
  let s : Set ((Fin 2 → I) × (Fin 2 → I)) := {p | m p.1 ≤ m p.2}
  have hs : MeasurableSet s := measurableSet_le (by fun_prop) (by fun_prop)
  let f := s.indicator (fun _ => (1 : ℝ))
  have hf : Integrable f (C.toMeasure.prod C.toMeasure) :=
    (integrable_const (1 : ℝ)).indicator hs
  have hinner (y : Fin 2 → I) : (∫ x, f (x, y) ∂C.toMeasure) = C.diagonal (m y) := by
    have h := integral_indicator_one (μ := C.toMeasure)
      (s := {x | m x ≤ m y}) (measurableSet_le (by fun_prop) (by fun_prop))
    simpa only [f, s, Set.indicator, mem_ofPred_eq, Pi.one_apply, m, C.measureReal_max_le] using h
  have hsym : (∫ x, ∫ y, f (x, y) ∂C.toMeasure ∂C.toMeasure) =
      ∫ y, ∫ x, f (x, y) ∂C.toMeasure ∂C.toMeasure := integral_integral_swap hf
  have hsum (x : Fin 2 → I) :
      (∫ y, f (x, y) ∂C.toMeasure) + (∫ y, f (y, x) ∂C.toMeasure) = 1 := by
    have hxy : Integrable (fun y => f (x, y)) C.toMeasure :=
      (integrable_const (1 : ℝ)).indicator
        (measurableSet_le (by fun_prop) (by fun_prop))
    have hyx : Integrable (fun y => f (y, x)) C.toMeasure :=
      (integrable_const (1 : ℝ)).indicator
        (measurableSet_le (by fun_prop) (by fun_prop))
    rw [← integral_add hxy hyx]
    calc
      _ = ∫ _ : Fin 2 → I, (1 : ℝ) ∂C.toMeasure := by
        apply integral_congr_ae
        filter_upwards [C.ae_max_ne (m x)] with y hy
        change m y ≠ m x at hy
        simp only [f, s, Set.indicator, mem_ofPred_eq]
        by_cases h : m x ≤ m y
        · have h' : ¬m y ≤ m x := not_le.mpr (lt_of_le_of_ne h hy.symm)
          simp [h, h']
        · simp [h, le_of_not_ge h]
      _ = 1 := by simp
  have hfun : (fun x => ∫ y, f (x, y) ∂C.toMeasure) =
      fun x => 1 - C.diagonal (m x) := by
    funext x
    have hh := hsum x
    rw [hinner] at hh
    linarith
  rw [hfun] at hsym
  simp_rw [hinner] at hsym
  rw [integral_sub (integrable_const _) (integrable_continuous_cube _ (by fun_prop))] at hsym
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hsym
  linarith

end ProbabilityTheory.Copula
