/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.Rank
import Copula.Rank.Benchmarks

/-! # Sharp bounds and explicit ordinal-sum rank formulas

Two independent components yield positive rank dependence at every interior
split, maximized uniquely by equal block lengths. Two countermonotonic
components attain the sharp lower bounds at each fixed split.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem kendallTau_ordinalSum_independence (a : I) :
    ((independence 2).ordinalSum (independence 2) a).kendallTau =
      2 * (a : ℝ) * (1 - (a : ℝ)) := by
  rw [kendallTau_ordinalSum, kendallTau_independence]
  ring

theorem spearmanRho_ordinalSum_independence (a : I) :
    ((independence 2).ordinalSum (independence 2) a).spearmanRho =
      3 * (a : ℝ) * (1 - (a : ℝ)) := by
  rw [spearmanRho_ordinalSum, spearmanRho_independence]
  ring

theorem spearmanFootrule_ordinalSum_independence (a : I) :
    ((independence 2).ordinalSum (independence 2) a).spearmanFootrule =
      2 * (a : ℝ) * (1 - (a : ℝ)) := by
  rw [spearmanFootrule_ordinalSum, spearmanFootrule_independence]
  ring

theorem kendallTau_ordinalSum_countermonotonic (a : I) :
    (countermonotonic.ordinalSum countermonotonic a).kendallTau =
      4 * (a : ℝ) * (1 - (a : ℝ)) - 1 := by
  rw [kendallTau_ordinalSum, kendallTau_countermonotonic]
  ring

theorem spearmanRho_ordinalSum_countermonotonic (a : I) :
    (countermonotonic.ordinalSum countermonotonic a).spearmanRho =
      6 * (a : ℝ) * (1 - (a : ℝ)) - 1 := by
  rw [spearmanRho_ordinalSum, spearmanRho_countermonotonic]
  ring

theorem spearmanFootrule_ordinalSum_countermonotonic (a : I) :
    (countermonotonic.ordinalSum countermonotonic a).spearmanFootrule =
      3 * (a : ℝ) * (1 - (a : ℝ)) - 1 / 2 := by
  rw [spearmanFootrule_ordinalSum, spearmanFootrule_countermonotonic]
  ring

/-- The sharp lower bound for tau at a fixed split. -/
theorem kendallTau_ordinalSum_lower_bound (C D : Copula 2) (a : I) :
    4 * (a : ℝ) * (1 - (a : ℝ)) - 1 ≤ (C.ordinalSum D a).kendallTau := by
  rw [kendallTau_ordinalSum]
  nlinarith only [mul_nonneg (sq_nonneg (a : ℝ)) (show 0 ≤ 1 + C.kendallTau by
      linarith [C.kendallTau_mem_Icc.1]),
    mul_nonneg (sq_nonneg (1 - (a : ℝ))) (show 0 ≤ 1 + D.kendallTau by
      linarith [D.kendallTau_mem_Icc.1])]

/-- The sharp lower bound for rho at a fixed split. -/
theorem spearmanRho_ordinalSum_lower_bound (C D : Copula 2) (a : I) :
    6 * (a : ℝ) * (1 - (a : ℝ)) - 1 ≤ (C.ordinalSum D a).spearmanRho := by
  rw [spearmanRho_ordinalSum]
  nlinarith only [mul_nonneg (pow_nonneg a.property.1 3) (show 0 ≤ 1 + C.spearmanRho by
      linarith [C.spearmanRho_mem_Icc.1]),
    mul_nonneg (pow_nonneg (sub_nonneg.mpr a.property.2) 3) (show 0 ≤ 1 + D.spearmanRho by
      linarith [D.spearmanRho_mem_Icc.1])]

/-- The sharp lower bound for footrule at a fixed split. -/
theorem spearmanFootrule_ordinalSum_lower_bound (C D : Copula 2) (a : I) :
    3 * (a : ℝ) * (1 - (a : ℝ)) - 1 / 2 ≤ (C.ordinalSum D a).spearmanFootrule := by
  rw [spearmanFootrule_ordinalSum]
  nlinarith only [mul_nonneg (sq_nonneg (a : ℝ)) (show 0 ≤ 1 / 2 + C.spearmanFootrule by
      linarith [C.spearmanFootrule_mem_Icc.1]),
    mul_nonneg (sq_nonneg (1 - (a : ℝ))) (show 0 ≤ 1 / 2 + D.spearmanFootrule by
      linarith [D.spearmanFootrule_mem_Icc.1])]

theorem kendallTau_ordinalSum_independence_le_half (a : I) :
    ((independence 2).ordinalSum (independence 2) a).kendallTau ≤ 1 / 2 := by
  rw [kendallTau_ordinalSum_independence]
  nlinarith [sq_nonneg ((a : ℝ) - 1 / 2)]

theorem spearmanRho_ordinalSum_independence_le_three_quarters (a : I) :
    ((independence 2).ordinalSum (independence 2) a).spearmanRho ≤ 3 / 4 := by
  rw [spearmanRho_ordinalSum_independence]
  nlinarith [sq_nonneg ((a : ℝ) - 1 / 2)]

theorem spearmanFootrule_ordinalSum_independence_le_half (a : I) :
    ((independence 2).ordinalSum (independence 2) a).spearmanFootrule ≤ 1 / 2 := by
  rw [spearmanFootrule_ordinalSum_independence]
  nlinarith [sq_nonneg ((a : ℝ) - 1 / 2)]

theorem kendallTau_ordinalSum_independence_eq_half_iff (a : I) :
    ((independence 2).ordinalSum (independence 2) a).kendallTau = 1 / 2 ↔ a = unitHalf := by
  rw [kendallTau_ordinalSum_independence]
  constructor
  · intro h
    apply Subtype.ext
    change (a : ℝ) = 1 / 2
    have hz : ((a : ℝ) - 1 / 2) ^ 2 = 0 := by nlinarith only [h]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · rintro rfl
    norm_num [unitHalf]

theorem spearmanRho_ordinalSum_independence_eq_three_quarters_iff (a : I) :
    ((independence 2).ordinalSum (independence 2) a).spearmanRho = 3 / 4 ↔ a = unitHalf := by
  rw [← kendallTau_ordinalSum_independence_eq_half_iff,
    spearmanRho_ordinalSum_independence, kendallTau_ordinalSum_independence]
  constructor <;> intro h <;> linarith

theorem spearmanFootrule_ordinalSum_independence_eq_half_iff (a : I) :
    ((independence 2).ordinalSum (independence 2) a).spearmanFootrule = 1 / 2 ↔ a = unitHalf := by
  rw [← kendallTau_ordinalSum_independence_eq_half_iff,
    spearmanFootrule_ordinalSum_independence, kendallTau_ordinalSum_independence]

end ProbabilityTheory.Copula
