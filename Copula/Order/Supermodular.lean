/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Order.Orthant

/-! # Supermodular order and orthant comparisons -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory

/-- Supermodularity on a lattice. -/
def IsSupermodular {α : Type*} [Lattice α] (f : α → ℝ) : Prop :=
  ∀ x y, f x + f y ≤ f (x ⊓ y) + f (x ⊔ y)

theorem isSupermodular_lowerIndicator {α : Type*} [Lattice α] [DecidableLE α] (u : α) :
    IsSupermodular (fun x => if x ≤ u then (1 : ℝ) else 0) := by
  classical
  intro x y
  by_cases hx : x ≤ u
  · have hi : x ⊓ y ≤ u := inf_le_left.trans hx
    simp [hx, hi, sup_le_iff]
  · by_cases hy : y ≤ u
    · have hi : x ⊓ y ≤ u := inf_le_right.trans hy
      simp [hx, hy, hi, sup_le_iff]
    · simp only [hx, hy, ite_false, sup_le_iff, false_and, add_zero]
      split_ifs <;> norm_num

theorem isSupermodular_upperIndicator {α : Type*} [Lattice α] [DecidableLE α] (u : α) :
    IsSupermodular (fun x => if u ≤ x then (1 : ℝ) else 0) := by
  classical
  intro x y
  by_cases hx : u ≤ x
  · have hs : u ≤ x ⊔ y := hx.trans le_sup_left
    simp [hx, hs, le_inf_iff, add_comm]
  · by_cases hy : u ≤ y
    · have hs : u ≤ x ⊔ y := hy.trans le_sup_right
      simp [hx, hy, hs, le_inf_iff]
    · simp only [hx, hy, ite_false, le_inf_iff, false_and, zero_add]
      split_ifs <;> norm_num

namespace Copula

variable {d : ℕ}

/-- Comparison of expectations of all bounded measurable supermodular functions. -/
def SupermodularLE (C D : Copula d) : Prop :=
  ∀ f : (Fin d → I) → ℝ, IsSupermodular f → Measurable f →
    (∃ b : ℝ, ∀ x, ‖f x‖ ≤ b) → (∫ x, f x ∂C.toMeasure) ≤ ∫ x, f x ∂D.toMeasure

@[refl] theorem SupermodularLE.refl (C : Copula d) : C.SupermodularLE C :=
  fun _ _ _ _ => le_rfl

@[trans] theorem SupermodularLE.trans {C D E : Copula d}
    (h : C.SupermodularLE D) (k : D.SupermodularLE E) : C.SupermodularLE E :=
  fun f hf hm hb => (h f hf hm hb).trans (k f hf hm hb)

theorem SupermodularLE.lowerOrthantLE {C D : Copula d} (h : C.SupermodularLE D) :
    C.LowerOrthantLE D := by
  classical
  intro u
  have he (E : Copula d) : (∫ x, if x ≤ u then (1 : ℝ) else 0 ∂E.toMeasure) = E.cdf u := by
    simpa [Set.indicator, cdf] using integral_indicator_one (μ := E.toMeasure)
      (s := Iic u) measurableSet_Iic
  have hm : Measurable (fun x : Fin d → I => if x ≤ u then (1 : ℝ) else 0) :=
    measurable_const.ite (measurableSet_le measurable_id measurable_const) measurable_const
  have hb : ∃ b : ℝ, ∀ x : Fin d → I, ‖if x ≤ u then (1 : ℝ) else 0‖ ≤ b := by
    refine ⟨1, fun x => ?_⟩
    split_ifs <;> norm_num
  simpa only [he] using h _ (isSupermodular_lowerIndicator u) hm hb

theorem SupermodularLE.upperOrthantLE {C D : Copula d} (h : C.SupermodularLE D) :
    C.UpperOrthantLE D := by
  classical
  intro u
  have he (E : Copula d) : (∫ x, if u ≤ x then (1 : ℝ) else 0 ∂E.toMeasure) = E.survival u := by
    simpa [Set.indicator, survival] using integral_indicator_one (μ := E.toMeasure)
      (s := Ici u) measurableSet_Ici
  have hm : Measurable (fun x : Fin d → I => if u ≤ x then (1 : ℝ) else 0) :=
    measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const
  have hb : ∃ b : ℝ, ∀ x : Fin d → I, ‖if u ≤ x then (1 : ℝ) else 0‖ ≤ b := by
    refine ⟨1, fun x => ?_⟩
    split_ifs <;> norm_num
  simpa only [he] using h _ (isSupermodular_upperIndicator u) hm hb

theorem SupermodularLE.concordanceLE {C D : Copula d} (h : C.SupermodularLE D) :
    C.ConcordanceLE D := ⟨h.lowerOrthantLE, h.upperOrthantLE⟩

theorem SupermodularLE.antisymm {C D : Copula d} (h : C.SupermodularLE D)
    (k : D.SupermodularLE C) : C = D := h.lowerOrthantLE.antisymm k.lowerOrthantLE

end Copula
end ProbabilityTheory
