/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.PowerSums
import Copula.Rank.Region.RhoTau.Boundary

/-! # The decreasing-permutation case of the sharp inequality

Schreyer–Paulin–Trutschnig, Lemmas 4.1–4.2. A minimizing vector has
equal large coordinates and at most one smaller coordinate. Its first
two rank coordinates therefore lie on one of the explicit prototype arcs.
-/

open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

theorem two_level_is_arc {k : ℕ} {r b : ℝ} (hk : 0 < k) (hb : 0 ≤ b)
    (hbr : b ≤ r) (hs : (k : ℝ) * r + b = 1) :
    ∃ n : ℕ, ∃ s : I, arcTau n s = -1 + 2 * (k * r ^ 2 + b ^ 2) ∧
      arcRho n s = -1 + 2 * (k * r ^ 3 + b ^ 3) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hk)
  simp only [Nat.cast_succ] at hs ⊢
  let s : ℝ := ((n : ℝ) + 1) * (((n : ℝ) + 2) * r - 1)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hs0 : 0 ≤ s := by
    have hh : 0 ≤ ((n : ℝ) + 2) * r - 1 := by nlinarith
    exact mul_nonneg (by positivity) hh
  have hs1 : s ≤ 1 := by
    have hh := mul_nonneg (show 0 ≤ (n : ℝ) + 2 by positivity) hb
    dsimp [s]
    nlinarith [congrArg (fun z : ℝ => z * ((n : ℝ) + 2)) hs]
  refine ⟨n, ⟨s, hs0, hs1⟩, ?_, ?_⟩
  all_goals
    have hbform : b = 1 - ((n : ℝ) + 1) * r := by linarith
    rw [hbform]
    dsimp [arcTau, arcRho, s]
    field_simp
    ring

theorem decreasing_permutation_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hs : ∑ i, u i = 1) :
    ∃ n : ℕ, ∃ s : I, arcTau n s = -1 + 2 * ∑ i, (u i) ^ 2 ∧
      arcRho n s ≤ -1 + 2 * ∑ i, (u i) ^ 3 := by
  obtain ⟨k, r, b, hk, _, hb, hbr, hsum, hsq, hcube⟩ := powerSum_prototype u hu hs
  obtain ⟨n, s, ht, hr⟩ := two_level_is_arc hk hb hbr hsum
  exact ⟨n, s, by rwa [hsq] at ht, by rw [hr]; linarith⟩

end ProbabilityTheory.Copula.RankRegion.RhoTau
