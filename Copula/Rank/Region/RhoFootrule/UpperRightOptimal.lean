/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoFootrule.UpperRightMoments
import Copula.Rank.Region.RhoFootrule.UpperContact

open MeasureTheory
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoFootrule.RightData

open UpperSpline

variable (S : RightData)

noncomputable def dual (x : ℝ) : ℝ := potential S.N S.v S.w S.period_pos x

@[fun_prop] theorem continuous_dual : Continuous S.dual :=
  continuous_potential (by exact_mod_cast S.N_pos) S.v_nonneg S.w_nonneg S.period_pos

theorem dual_phase (k : ℕ) (i : Fin 4) (s : I) :
    S.dual (S.phase k i s) = pieceValue S.N S.v S.w i s :=
  potential_translated_piecePoint (by exact_mod_cast S.N_pos) S.v_nonneg S.w_nonneg S.period_pos k i s

theorem path_contact (i : S.Index) (s : I) :
    S.dual (S.path i s 0) + S.dual (S.path i s 1) =
      S.distance i s ^ 2 - period S.N S.v S.w * S.distance i s := by
  rcases i with k | k | k
  · change S.dual (S.phase k 0 s) + S.dual (S.phase k 2 s) = _
    rw [S.dual_phase, S.dual_phase]
    dsimp [pieceValue, offset, distance, period]
    ring
  · change S.dual (S.phase k 1 s) + S.dual (S.phase k 3 s) = _
    rw [S.dual_phase, S.dual_phase]
    dsimp [pieceValue, offset, distance, period]
    ring
  · change S.dual (S.phase k 3 s) + S.dual (S.phase (k + 1) 1 s) = _
    rw [S.dual_phase, S.dual_phase]
    dsimp [pieceValue, offset, distance, period]
    ring

theorem symmetric_contact (i : S.Index × Bool) (s : I) :
    S.dual (S.symmetricPath i s 0) + S.dual (S.symmetricPath i s 1) =
      |(S.symmetricPath i s 0 : ℝ) - S.symmetricPath i s 1| ^ 2 -
        period S.N S.v S.w * |(S.symmetricPath i s 0 : ℝ) - S.symmetricPath i s 1| := by
  rw [S.symmetric_abs_distance]
  rcases i with ⟨i, b⟩
  cases b
  · exact S.path_contact i s
  · change S.dual (S.path i s 1) + S.dual (S.path i s 0) = _
    rw [add_comm]
    exact S.path_contact i s

theorem integral_dual (C : Copula 2) :
    (∫ x, S.dual (x 0) + S.dual (x 1) ∂C.toMeasure) = 2 * ∫ u : I, S.dual u := by
  rw [integral_add (integrable_continuous_cube _ (by fun_prop))
    (integrable_continuous_cube _ (by fun_prop)),
    C.integral_eval 0 (fun u : I => S.dual u) (by fun_prop), C.integral_eval 1 (fun u : I => S.dual u) (by fun_prop)]
  ring

theorem cost_lower_bound (C : Copula 2) :
    2 * (∫ u : I, S.dual u) ≤
      (∫ x, ((x 0 : ℝ) - x 1) ^ 2 ∂C.toMeasure) -
        period S.N S.v S.w * ∫ x, |(x 0 : ℝ) - x 1| ∂C.toMeasure := by
  rw [← S.integral_dual C, ← integral_const_mul, ← integral_sub
    (integrable_continuous_cube _ (by fun_prop)) (integrable_continuous_cube _ (by fun_prop))]
  apply integral_mono (integrable_continuous_cube _ (by fun_prop))
    (integrable_continuous_cube _ (by fun_prop))
  intro x
  have h := potential_feasible (by exact_mod_cast S.N_pos) S.v_nonneg S.w_nonneg S.period_pos
    (x 1 : ℝ) (x 0 : ℝ)
  simpa only [dual, add_comm] using h

theorem cost_attained :
    (∫ x, ((x 0 : ℝ) - x 1) ^ 2 ∂S.copula.toMeasure) -
      period S.N S.v S.w * (∫ x, |(x 0 : ℝ) - x 1| ∂S.copula.toMeasure) =
      2 * ∫ u : I, S.dual u := by
  rw [← S.integral_dual S.copula, ← integral_const_mul, ← integral_sub
    (integrable_continuous_cube _ (by fun_prop)) (integrable_continuous_cube _ (by fun_prop))]
  rw [S.integral_copula (by fun_prop), S.integral_copula (by fun_prop)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply integral_congr_ae
  filter_upwards [] with s
  simpa only [sq_abs] using (S.symmetric_contact i s).symm

/-- The supporting line is valid for every copula and is attained by this family. -/
theorem supporting_bound (C : Copula 2) :
    C.spearmanRho - 2 * period S.N S.v S.w * C.spearmanFootrule ≤
      S.copula.spearmanRho - 2 * period S.N S.v S.w * S.copula.spearmanFootrule := by
  have h := S.cost_lower_bound C
  rw [← S.cost_attained] at h
  rw [Copula.spearmanRho_eq_one_sub, Copula.spearmanRho_eq_one_sub,
    footrule_eq_abs_moment, footrule_eq_abs_moment]
  linarith

theorem maximizes_rho (C : Copula 2) (h : C.spearmanFootrule = S.copula.spearmanFootrule) :
    C.spearmanRho ≤ S.copula.spearmanRho := by
  have hh := S.supporting_bound C
  rw [h] at hh
  linarith

end ProbabilityTheory.Copula.RankRegion.RhoFootrule.RightData
