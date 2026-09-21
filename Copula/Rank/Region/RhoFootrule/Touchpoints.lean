/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel

Adapted from Corrram/lean-verifications, commit
9e144da5e0d8e2b59dadf9cef090947cb2220313.
Source module: Papers.AnsariRockel2026RhoFootrule.Touchpoints
Imports and namespaces adapted to the copula package; unused helpers omitted.
-/
import Copula.Rank.Region.RhoFootrule.Moments
import Copula.Rank.Region.EqualBlocks
import Copula.Rank.MedianExtrema

/-! # The Cauchy-Schwarz equality case and every discrete contact point

The exact variance defect gives equation (22). Equal blocks of a half-turn
shuffle attain all the contact points x_N=1-3/(2N), N>=1.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoFootrule

theorem quadratic_defect (C : Copula 2) :
    1 - 2 / 3 * (1 - C.spearmanFootrule) ^ 2 - C.spearmanRho =
      6 * (∫ x, (|(x 0 : ℝ) - x 1| - (1 - C.spearmanFootrule) / 3) ^ 2 ∂C.toMeasure) := by
  let m : ℝ := ∫ x, |(x 0 : ℝ) - x 1| ∂C.toMeasure
  have hm : (1 - C.spearmanFootrule) / 3 = m := by
    rw [ProbabilityTheory.Copula.RankRegion.footrule_eq_abs_moment]
    dsimp [m]
    ring
  have he : (fun x : Fin 2 → I => (|(x 0 : ℝ) - x 1| - m) ^ 2) =
      fun x => ((x 0 : ℝ) - x 1) ^ 2 - (2 * m) * |(x 0 : ℝ) - x 1| + m ^ 2 := by
    funext x
    nlinarith only [sq_abs ((x 0 : ℝ) - x 1)]
  rw [hm, he, integral_add, integral_sub, integral_const_mul, integral_const]
  · simp only [probReal_univ, smul_eq_mul, one_mul]
    rw [C.spearmanRho_eq_one_sub, ProbabilityTheory.Copula.RankRegion.footrule_eq_abs_moment]
    dsimp [m]
    ring
  all_goals exact Copula.integrable_continuous_cube C.toMeasure (by fun_prop)

/-- Equation (22): equality is exactly constant absolute displacement. -/
theorem quadratic_equality_iff (C : Copula 2) :
    C.spearmanRho = 1 - 2 / 3 * (1 - C.spearmanFootrule) ^ 2 ↔
      ∀ᵐ x ∂C.toMeasure, |(x 0 : ℝ) - x 1| = (1 - C.spearmanFootrule) / 3 := by
  have hd := quadratic_defect C
  have hi : Integrable
      (fun x : Fin 2 → I => (|(x 0 : ℝ) - x 1| - (1 - C.spearmanFootrule) / 3) ^ 2)
      C.toMeasure := Copula.integrable_continuous_cube C.toMeasure (by fun_prop)
  have hz := integral_eq_zero_iff_of_nonneg
    (fun x : Fin 2 → I => sq_nonneg (|(x 0 : ℝ) - x 1| - (1 - C.spearmanFootrule) / 3)) hi
  constructor
  · intro h
    have hI : (∫ x, (|(x 0 : ℝ) - x 1| - (1 - C.spearmanFootrule) / 3) ^ 2 ∂C.toMeasure) = 0 :=
      by linarith
    filter_upwards [hz.mp hI] with x hx
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)
  · intro h
    have hI := hz.mpr (by filter_upwards [h] with x hx; simp [hx])
    linarith

noncomputable def halfTurn : Copula 2 :=
  (Copula.countermonotonic.ordinalSum Copula.countermonotonic Copula.unitHalf).reflect {1}

theorem halfTurn_rho : halfTurn.spearmanRho = -1 / 2 := by
  rw [halfTurn, Copula.spearmanRho_reflect_second, Copula.spearmanRho_ordinalSum]
  norm_num [Copula.unitHalf]

theorem halfTurn_footrule : halfTurn.spearmanFootrule = -1 / 2 :=
  Copula.spearmanFootrule_reflect_ordinalSum_half _ _

/-- Index n means N=n+1, covering every positive integer contact index. -/
noncomputable def contactCopula (n : ℕ) : Copula 2 := ProbabilityTheory.Copula.RankRegion.equalBlocks n halfTurn

theorem contactCopula_coefficients (n : ℕ) :
    (contactCopula n).spearmanFootrule = 1 - 3 / (2 * ((n : ℝ) + 1)) ∧
    (contactCopula n).spearmanRho = 1 - 3 / (2 * ((n : ℝ) + 1) ^ 2) := by
  simp only [contactCopula, ProbabilityTheory.Copula.RankRegion.equalBlocks_footrule, ProbabilityTheory.Copula.RankRegion.equalBlocks_rho,
    halfTurn_footrule, halfTurn_rho]
  constructor <;> field_simp <;> ring

/-- These are genuine global maxima at fixed footrule, not just benchmark values. -/
theorem contactCopula_maximizes_rho (n : ℕ) (C : Copula 2)
    (hC : C.spearmanFootrule = 1 - 3 / (2 * ((n : ℝ) + 1))) :
    C.spearmanRho ≤ (contactCopula n).spearmanRho := by
  have h := quadratic_upper_bound C
  rw [hC] at h
  rw [(contactCopula_coefficients n).2]
  convert h using 1
  field_simp
  ring

theorem contactCopula_constant_displacement (n : ℕ) :
    ∀ᵐ x ∂(contactCopula n).toMeasure,
      |(x 0 : ℝ) - x 1| = 1 / (2 * ((n : ℝ) + 1)) := by
  have he : (contactCopula n).spearmanRho =
      1 - 2 / 3 * (1 - (contactCopula n).spearmanFootrule) ^ 2 := by
    rw [(contactCopula_coefficients n).1, (contactCopula_coefficients n).2]
    field_simp
    ring
  have h := (quadratic_equality_iff _).mp he
  have hm : (1 - (contactCopula n).spearmanFootrule) / 3 = 1 / (2 * ((n : ℝ) + 1)) := by
    rw [(contactCopula_coefficients n).1]
    field_simp
    ring
  simpa only [hm] using h

end ProbabilityTheory.Copula.RankRegion.RhoFootrule
