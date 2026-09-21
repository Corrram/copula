/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion

/-- Adjacent paths add to a constant density, including the two endpoints. -/
theorem weighted_chain_sum (N : ℕ) (B : ℕ → ℝ) :
    (∑ k ∈ Finset.range N, ((N - (k : ℝ)) * B k + ((k : ℝ) + 1) * B (k + 1))) =
      N * ∑ k ∈ Finset.range (N + 1), B k := by
  have ht : (∑ k ∈ Finset.range N, (((k : ℝ) + 1) * B (k + 1) - k * B k)) = N * B N := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  calc
    _ = (N : ℝ) * (∑ k ∈ Finset.range N, B k) +
        ∑ k ∈ Finset.range N, (((k : ℝ) + 1) * B (k + 1) - k * B k) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [ht, Finset.sum_range_succ]; ring

end ProbabilityTheory.Copula.RankRegion
