/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.CDF
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-! # Rectangle probabilities and increasing distribution functions

Rectangle increments use lower endpoints on the selected coordinates, hence
the sign is `(-1)^s.card`. The probability identity requires ordered endpoints.
The empty-dimensional rectangle has probability one.
-/

open MeasureTheory Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- A corner of a rectangle, choosing the lower endpoint on `s`. -/
def corner (a b : Fin d → I) (s : Finset (Fin d)) (i : Fin d) : I :=
  if i ∈ s then a i else b i

/-- Apply finite differences in the coordinates of `s`. -/
def partialIncrement (F : (Fin d → I) → ℝ) (a b : Fin d → I)
    (s : Finset (Fin d)) : ℝ :=
  ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card * F (corner a b t)

/-- The alternating sum of a function over all corners of a rectangle. -/
def rectangleIncrement (F : (Fin d → I) → ℝ) (a b : Fin d → I) : ℝ :=
  partialIncrement F a b Finset.univ

theorem partialIncrement_insert (F : (Fin d → I) → ℝ) (a b : Fin d → I)
    (s : Finset (Fin d)) (i : Fin d) (hi : i ∉ s) :
    partialIncrement F a b (insert i s) =
      partialIncrement F a b s - partialIncrement F a (Function.update b i (a i)) s := by
  unfold partialIncrement
  rw [Finset.sum_powerset_insert hi, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have hit : i ∉ t := fun h => hi (Finset.mem_powerset.mp ht h)
  have hc : corner a b (insert i t) = corner a (Function.update b i (a i)) t := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [corner]
    · simp [corner, hji, Function.update_of_ne hji]
  rw [Finset.card_insert_of_notMem hit, pow_succ, hc]
  ring

private def partialRectangle (a b : Fin d → I) (s : Finset (Fin d)) : Set (Fin d → I) :=
  {x | x ≤ b ∧ ∀ i ∈ s, a i < x i}

private theorem measurableSet_partialRectangle (a b : Fin d → I) (s : Finset (Fin d)) :
    MeasurableSet (partialRectangle a b s) :=
  measurableSet_Iic.inter (by
    change MeasurableSet (⋂ i ∈ s, {x : Fin d → I | a i < x i})
    exact s.measurableSet_biInter fun i _ => measurableSet_lt measurable_const (measurable_pi_apply i))

private theorem partialIncrement_cdf (C : Copula d) (a b : Fin d → I)
    (s : Finset (Fin d)) (hab : a ≤ b) :
    partialIncrement C.cdf a b s = C.toMeasure.real (partialRectangle a b s) := by
  induction s using Finset.induction_on generalizing b with
  | empty => simp [partialIncrement, partialRectangle, corner, cdf, Iic]
  | @insert i s hi ih =>
    have hab' : a ≤ Function.update b i (a i) := by
      intro j
      by_cases hji : j = i
      · subst j; simp
      · simpa [Function.update_of_ne hji] using hab j
    have hinter : partialRectangle a b s ∩ {x | x i ≤ a i} =
        partialRectangle a (Function.update b i (a i)) s := by
      ext x
      constructor
      · rintro ⟨⟨hxb, hx⟩, hxi⟩
        refine ⟨?_, hx⟩
        intro j
        by_cases hji : j = i
        · subst j; simpa using hxi
        · simpa [Function.update_of_ne hji] using hxb j
      · rintro ⟨hxb, hx⟩
        refine ⟨⟨?_, hx⟩, ?_⟩
        · intro j
          by_cases hji : j = i
          · subst j
            exact (by simpa using hxb i : x i ≤ a i).trans (hab i)
          · simpa [Function.update_of_ne hji] using hxb j
        · simpa using hxb i
    have hdiff : partialRectangle a b s \ {x | x i ≤ a i} =
        partialRectangle a b (insert i s) := by
      ext x
      simp only [partialRectangle, mem_setOf_eq, mem_sdiff, Finset.mem_insert,
        forall_eq_or_imp, not_le]
      tauto
    rw [partialIncrement_insert _ _ _ _ _ hi, ih b hab, ih _ hab']
    have h := measureReal_inter_add_sdiff (μ := C.toMeasure)
      (s := partialRectangle a b s)
      (measurableSet_le (measurable_pi_apply i) measurable_const)
    rw [hinter, hdiff] at h
    linarith

/-- The alternating CDF sum equals the probability of the half-open rectangle. -/
theorem rectangleIncrement_cdf (C : Copula d) (a b : Fin d → I) (hab : a ≤ b) :
    rectangleIncrement C.cdf a b = C.toMeasure.real (Set.pi univ (fun i => Ioc (a i) (b i))) := by
  rw [rectangleIncrement, partialIncrement_cdf C a b _ hab]
  congr 1
  ext x
  simp only [partialRectangle, mem_setOf_eq, Finset.mem_univ, forall_const,
    mem_univ_pi, mem_Ioc, Pi.le_def]
  exact ⟨fun h i => ⟨h.2 i, h.1 i⟩, fun h => ⟨fun i => (h i).2, fun i => (h i).1⟩⟩

/-- Nonnegative rectangle increments: the classical `d`-increasing property. -/
theorem rectangleIncrement_cdf_nonneg (C : Copula d) (a b : Fin d → I) (hab : a ≤ b) :
    0 ≤ rectangleIncrement C.cdf a b := by
  rw [C.rectangleIncrement_cdf a b hab]
  exact measureReal_nonneg

end ProbabilityTheory.Copula
