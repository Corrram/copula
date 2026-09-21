/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.FrechetChatterjee
import Copula.Rank.FrechetKendall

/-! # Exact xi plus footrule optimization over the full Frechet simplex -/

namespace ProbabilityTheory.Copula

variable (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)

theorem frechet_xi_add_footrule_identity :
    (frechet a b ha hb hab).chatterjeeXi + (frechet a b ha hb hab).spearmanFootrule =
      (b - 1 / 4) ^ 2 + a * (a + 1 - b) - 1 / 16 := by
  rw [chatterjeeXi_frechet, spearmanFootrule_frechet]
  ring

/-- The exact minimum is attained by three quarters independence plus one quarter W. -/
theorem frechet_xi_add_footrule_lower :
    -(1 / 16 : ℝ) ≤
      (frechet a b ha hb hab).chatterjeeXi + (frechet a b ha hb hab).spearmanFootrule := by
  rw [frechet_xi_add_footrule_identity]
  have hn : 0 ≤ a + 1 - b := by linarith
  nlinarith [sq_nonneg (b - 1 / 4), mul_nonneg ha hn]

theorem frechet_xi_add_footrule_eq_iff :
    (frechet a b ha hb hab).chatterjeeXi + (frechet a b ha hb hab).spearmanFootrule =
      -(1 / 16 : ℝ) ↔ a = 0 ∧ b = 1 / 4 := by
  rw [frechet_xi_add_footrule_identity]
  constructor
  · intro he
    have hn : 0 ≤ a + 1 - b := by linarith
    have hbq : (b - 1 / 4) ^ 2 = 0 := by
      nlinarith [sq_nonneg (b - 1 / 4), mul_nonneg ha hn]
    have hbv : b = 1 / 4 := by
      have h := eq_zero_of_pow_eq_zero hbq
      linarith
    refine ⟨?_, hbv⟩
    rw [hbv] at he
    nlinarith [sq_nonneg a]
  · rintro ⟨rfl, rfl⟩
    norm_num

end ProbabilityTheory.Copula
