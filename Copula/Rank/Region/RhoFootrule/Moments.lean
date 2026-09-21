/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel

Adapted from Corrram/lean-verifications, commit
9e144da5e0d8e2b59dadf9cef090947cb2220313.
Source module: Papers.AnsariRockel2026RhoFootrule.Moments
Imports and namespaces adapted to the copula package; unused helpers omitted.
-/
import Copula.Rank.Region.Moments
import Copula.Rank.Region.Mixture

/-! # Moment representation and interpolation at fixed footrule

Lemma 3.2 and the interpolation step of Corollary 1.2 use no regularity
assumption beyond being a copula. Optimal boundary constructions are pending.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoFootrule

theorem moment_representation (C : Copula 2) :
    C.spearmanRho = 1 - 6 * (∫ x, ((x 0 : ℝ) - x 1) ^ 2 ∂C.toMeasure) ∧
    C.spearmanFootrule = 1 - 3 * (∫ x, |(x 0 : ℝ) - x 1| ∂C.toMeasure) :=
  ⟨C.spearmanRho_eq_one_sub, ProbabilityTheory.Copula.RankRegion.footrule_eq_abs_moment C⟩

/-- The classical quadratic upper envelope (equations (16)-(17)), before the
article's strictly sharper transport correction is imposed. -/
theorem quadratic_upper_bound (C : Copula 2) :
    C.spearmanRho ≤ 1 - 2 / 3 * (1 - C.spearmanFootrule) ^ 2 := by
  let m : ℝ := ∫ x, |(x 0 : ℝ) - x 1| ∂C.toMeasure
  have hv : 0 ≤ ∫ x : Fin 2 → I, (|(x 0 : ℝ) - x 1| - m) ^ 2 ∂C.toMeasure :=
    integral_nonneg (fun x => sq_nonneg (|(x 0 : ℝ) - x 1| - m))
  have he : (fun x : Fin 2 → I => (|(x 0 : ℝ) - x 1| - m) ^ 2) =
      fun x => ((x 0 : ℝ) - x 1) ^ 2 -
        (2 * m) * |(x 0 : ℝ) - x 1| + m ^ 2 := by
    funext x
    nlinarith only [sq_abs ((x 0 : ℝ) - x 1)]
  rw [he, integral_add, integral_sub, integral_const_mul, integral_const] at hv
  · simp only [probReal_univ, smul_eq_mul, one_mul] at hv
    have hm : C.spearmanFootrule = 1 - 3 * m := ProbabilityTheory.Copula.RankRegion.footrule_eq_abs_moment C
    rw [C.spearmanRho_eq_one_sub, hm]
    dsimp only [m] at hv ⊢
    nlinarith only [hv]
  all_goals exact Copula.integrable_continuous_cube C.toMeasure (by fun_prop)

theorem fixed_footrule_intermediate (C D : Copula 2) {p r : ℝ}
    (hC : C.spearmanFootrule = p) (hD : D.spearmanFootrule = p)
    (hrC : C.spearmanRho ≤ r) (hrD : r ≤ D.spearmanRho) :
    ∃ E : Copula 2, E.spearmanFootrule = p ∧ E.spearmanRho = r := by
  have hc : Continuous (fun a : I => (D.mix C a).spearmanRho) := by
    simp_rw [Copula.spearmanRho_mix]
    fun_prop
  obtain ⟨a, ha⟩ := ProbabilityTheory.Copula.RankRegion.exists_unitInterval_eq hc
    (by simpa using hrC) (by simpa using hrD)
  refine ⟨D.mix C a, ?_, ha⟩
  rw [Copula.spearmanFootrule_mix, hD, hC]
  ring

end ProbabilityTheory.Copula.RankRegion.RhoFootrule
