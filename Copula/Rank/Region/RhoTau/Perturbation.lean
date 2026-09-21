/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.Combinatorics
import Mathlib.Data.Finset.Max

/-! # Moving a constrained quadratic to the boundary of the simplex

This is the boundary reduction in Schreyer–Paulin–Trutschnig, Lemma 4.7.
The interval endpoint is constructed from a minimum over the negative
coordinates of a nonzero direction.
-/

open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

variable {ι : Type*} [Fintype ι]

theorem exists_positive_boundary_step (u δ : ι → ℝ) (hu : ∀ i, 0 < u i)
    (hδ : ∑ i, δ i = 0) (hne : ∃ i, δ i ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, 0 ≤ u i + t * δ i) ∧ ∃ i, u i + t * δ i = 0 := by
  classical
  have hneg : ∃ i, δ i < 0 := by
    by_contra h
    push Not at h
    obtain ⟨i, hi⟩ := hne
    have hle := Finset.single_le_sum (s := Finset.univ) (f := δ)
      (fun j _ => h j) (Finset.mem_univ i)
    rw [hδ] at hle
    exact hi (le_antisymm hle (h i))
  let S := Finset.univ.filter (fun i => δ i < 0)
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hneg
    exact ⟨i, by simp [S, hi]⟩
  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image S (fun i => u i / (-δ i)) hS
  have hkδ : δ k < 0 := (Finset.mem_filter.mp hk).2
  refine ⟨u k / (-δ k), div_pos (hu k) (neg_pos.mpr hkδ), ?_, k, ?_⟩
  · intro i
    by_cases hi : δ i < 0
    · have hh := hmin i (by simp [S, hi])
      have hm := (le_div_iff₀ (neg_pos.mpr hi)).mp hh
      linarith
    · exact add_nonneg (hu i).le
        (mul_nonneg (div_nonneg (hu k).le (neg_nonneg.mpr hkδ.le)) (le_of_not_gt hi))
  · field_simp [ne_of_lt hkδ]
    ring

/-- The sign of the linear term selects one of the two endpoints. -/
theorem exists_quadratic_boundary_step (u δ : ι → ℝ) (hu : ∀ i, 0 < u i)
    (hδ : ∑ i, δ i = 0) (hne : ∃ i, δ i ≠ 0) (b₁ b₂ : ℝ) (hb₂ : b₂ ≤ 0) :
    ∃ t : ℝ, t ≠ 0 ∧ (∀ i, 0 ≤ u i + t * δ i) ∧
      (∃ i, u i + t * δ i = 0) ∧ b₁ * t + b₂ * t ^ 2 ≤ 0 := by
  by_cases hb₁ : b₁ ≤ 0
  · obtain ⟨t, ht, hpos, hz⟩ := exists_positive_boundary_step u δ hu hδ hne
    exact ⟨t, ne_of_gt ht, hpos, hz,
      add_nonpos (mul_nonpos_of_nonpos_of_nonneg hb₁ ht.le)
        (mul_nonpos_of_nonpos_of_nonneg hb₂ (sq_nonneg t))⟩
  · obtain ⟨t, ht, hpos, hz⟩ := exists_positive_boundary_step u (fun i => -δ i) hu
      (by simp [hδ]) (by obtain ⟨i, hi⟩ := hne; exact ⟨i, neg_ne_zero.mpr hi⟩)
    refine ⟨-t, neg_ne_zero.mpr (ne_of_gt ht), ?_, ?_, ?_⟩
    · intro i
      simpa only [mul_neg, neg_mul] using hpos i
    · simpa only [mul_neg, neg_mul] using hz
    · exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (le_of_not_ge hb₁) (by linarith))
        (mul_nonpos_of_nonpos_of_nonneg hb₂ (sq_nonneg (-t)))

/-- Two linear constraints on three coordinates always admit a nonzero direction. -/
theorem exists_three_direction (a b c : ℝ) :
    ∃ x y z : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ x + y + z = 0 ∧ a * x + b * y + c * z = 0 := by
  by_cases hab : a = b
  · exact ⟨1, -1, 0, Or.inl one_ne_zero, by ring, by rw [hab]; ring⟩
  · exact ⟨b - c, c - a, a - b, Or.inr (Or.inr (sub_ne_zero.mpr hab)), by ring, by ring⟩

/-- Three linear constraints on the four coordinates of a 3412 pattern. -/
theorem exists_four_direction (a b c d : ℝ) :
    ∃ x y : ℝ, (x ≠ 0 ∨ y ≠ 0) ∧ (a - b) * x + (c - d) * y = 0 := by
  by_cases hab : a = b
  · exact ⟨1, 0, Or.inl one_ne_zero, by rw [hab]; ring⟩
  · exact ⟨c - d, b - a, Or.inr (sub_ne_zero.mpr (Ne.symm hab)), by ring⟩

end ProbabilityTheory.Copula.RankRegion.RhoTau
