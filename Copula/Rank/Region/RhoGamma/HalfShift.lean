/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel

Adapted from Corrram/lean-verifications, commit
9e144da5e0d8e2b59dadf9cef090947cb2220313.
Source module: Papers.AnsariRockelSteinmassl2026RhoGamma.HalfShift
Imports and namespaces adapted to the copula package; unused helpers omitted.
-/
import Copula.Rank.Region.RhoFootrule.Touchpoints
import Copula.Rank.Benchmarks

/-! # The half-shift dual certificate for s >= 1

This covers the theta <= 1 branch of Lemma 3.5, with s = 1/theta,
and the sufficient direction of Lemma 3.6. It includes the junction s=1.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoGamma

private noncomputable def medianWedge (u : I) : ℝ := min (u : ℝ) (1 - u)

@[fun_prop] private theorem continuous_medianWedge : Continuous medianWedge := by
  unfold medianWedge
  fun_prop

noncomputable def halfShiftPotential (s : ℝ) (u : I) : ℝ :=
  3 / 8 - s / 2 + (s - 1) * medianWedge u

@[fun_prop] theorem continuous_halfShiftPotential (s : ℝ) :
    Continuous (halfShiftPotential s) := by
  unfold halfShiftPotential
  fun_prop

/-- The same potential on the real line, used for its derivative bound. -/
noncomputable def halfShiftPotentialReal (s u : ℝ) : ℝ :=
  3 / 8 - s / 2 + (s - 1) * min u (1 - u)

theorem halfShiftPotentialReal_lipschitz {s : ℝ} (hs : 1 ≤ s) :
    LipschitzWith ⟨s - 1, sub_nonneg.mpr hs⟩ (halfShiftPotentialReal s) := by
  have hw : LipschitzWith 1 (fun u : ℝ => min u (1 - u)) := by
    apply LipschitzWith.mk_one
    intro u v
    simp only [Real.dist_eq, abs_eq_max_neg, min_def, max_def]
    split_ifs <;> linarith
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have h := hw.dist_le_mul u v
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
  change |halfShiftPotentialReal s u - halfShiftPotentialReal s v| ≤ (s - 1) * |u - v|
  rw [show halfShiftPotentialReal s u - halfShiftPotentialReal s v =
    (s - 1) * (min u (1 - u) - min v (1 - v)) by unfold halfShiftPotentialReal; ring,
    abs_mul, abs_of_nonneg (sub_nonneg.mpr hs)]
  exact mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hs)

theorem halfShiftPotential_lipschitz {s : ℝ} (hs : 1 ≤ s) :
    LipschitzWith ⟨s - 1, sub_nonneg.mpr hs⟩ (halfShiftPotential s) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  exact (halfShiftPotentialReal_lipschitz hs).dist_le_mul (u : ℝ) (v : ℝ)

theorem halfShiftPotential_deriv_bound {s : ℝ} (hs : 1 ≤ s) (u : ℝ) :
    |deriv (halfShiftPotentialReal s) u| ≤ s - 1 :=
  norm_deriv_le_of_lipschitz (halfShiftPotentialReal_lipschitz hs)

theorem halfShiftPotential_zero (s : ℝ) : halfShiftPotential s 0 = 3 / 8 - s / 2 := by
  norm_num [halfShiftPotential, medianWedge]

theorem halfShiftPotential_integral (s : ℝ) :
    (2 * ∫ u : I, halfShiftPotential s u) = 1 / 4 - s / 2 := by
  unfold halfShiftPotential medianWedge
  rw [integral_add, integral_const_mul, Copula.integral_unit_min_symm]
  · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  all_goals exact Copula.integrable_continuous_unit volume (by fun_prop)

theorem halfShiftPotential_feasible {s : ℝ} (hs : 1 ≤ s) (u v : I) :
    halfShiftPotential s u + halfShiftPotential s v ≤
      ((u : ℝ) - v) ^ 2 - s * |(u : ℝ) - v| := by
  have hw : medianWedge u + medianWedge v ≤ 1 - |(u : ℝ) - v| := by
    unfold medianWedge
    rcases le_total (u : ℝ) (v : ℝ) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      linarith [min_le_left (u : ℝ) (1 - u), min_le_right (v : ℝ) (1 - v)]
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      linarith [min_le_right (u : ℝ) (1 - u), min_le_left (v : ℝ) (1 - v)]
  have hm := mul_le_mul_of_nonneg_left hw (sub_nonneg.mpr hs)
  unfold halfShiftPotential
  nlinarith [sq_nonneg (|(u : ℝ) - v| - 1 / 2), sq_abs ((u : ℝ) - v)]

theorem halfShift_cost (s : ℝ) :
    (∫ x, ((x 0 : ℝ) - x 1) ^ 2 - s * |(x 0 : ℝ) - x 1|
      ∂RhoFootrule.halfTurn.toMeasure) = 1 / 4 - s / 2 := by
  have hr := RhoFootrule.halfTurn.spearmanRho_eq_one_sub
  rw [RhoFootrule.halfTurn_rho] at hr
  have hp := ProbabilityTheory.Copula.RankRegion.footrule_eq_abs_moment RhoFootrule.halfTurn
  rw [RhoFootrule.halfTurn_footrule] at hp
  have hq : (∫ x, ((x 0 : ℝ) - x 1) ^ 2
      ∂RhoFootrule.halfTurn.toMeasure) = 1 / 4 := by linarith
  have hm : (∫ x, |(x 0 : ℝ) - x 1|
      ∂RhoFootrule.halfTurn.toMeasure) = 1 / 2 := by linarith
  rw [integral_sub, integral_const_mul, hq, hm]
  · ring
  all_goals exact Copula.integrable_continuous_cube _ (by fun_prop)

theorem halfShift_optimal {s : ℝ} (hs : 1 ≤ s) (C : Copula 2) :
    (∫ x, ((x 0 : ℝ) - x 1) ^ 2 - s * |(x 0 : ℝ) - x 1|
      ∂RhoFootrule.halfTurn.toMeasure) ≤
    (∫ x, ((x 0 : ℝ) - x 1) ^ 2 - s * |(x 0 : ℝ) - x 1| ∂C.toMeasure) := by
  have hi := integral_mono
    (Copula.integrable_continuous_cube C.toMeasure (by fun_prop))
    (Copula.integrable_continuous_cube C.toMeasure (by fun_prop))
    (fun x : Fin 2 → I => halfShiftPotential_feasible hs (x 0) (x 1))
  rw [integral_add,
    C.integral_eval 0 (halfShiftPotential s) (continuous_halfShiftPotential s).measurable,
    C.integral_eval 1 (halfShiftPotential s) (continuous_halfShiftPotential s).measurable] at hi
  · rw [halfShift_cost]
    linarith [halfShiftPotential_integral s]
  all_goals exact Copula.integrable_continuous_cube C.toMeasure (by fun_prop)

theorem halfShiftPotential_contact (s : ℝ) :
    ∀ᵐ x ∂RhoFootrule.halfTurn.toMeasure,
      halfShiftPotential s (x 0) + halfShiftPotential s (x 1) =
        ((x 0 : ℝ) - x 1) ^ 2 - s * |(x 0 : ℝ) - x 1| := by
  have he := (RhoFootrule.quadratic_equality_iff
    RhoFootrule.halfTurn).mp (by
      rw [RhoFootrule.halfTurn_rho, RhoFootrule.halfTurn_footrule]
      norm_num)
  rw [RhoFootrule.halfTurn_footrule] at he
  filter_upwards [he] with x hx
  have hd : |(x 0 : ℝ) - x 1| = 1 / 2 := by linarith
  have hw : medianWedge (x 0) + medianWedge (x 1) = 1 / 2 := by
    unfold medianWedge
    rcases le_total (x 0 : ℝ) (x 1 : ℝ) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hd
      rw [min_eq_left (by linarith [(x 1).property.2]),
        min_eq_right (by linarith [(x 0).property.1])]
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hd
      rw [min_eq_right (by linarith [(x 1).property.1]),
        min_eq_left (by linarith [(x 0).property.2])]
      linarith
  have hq : ((x 0 : ℝ) - x 1) ^ 2 = 1 / 4 := by nlinarith [sq_abs ((x 0 : ℝ) - x 1)]
  rw [hd, hq]
  unfold halfShiftPotential
  linear_combination (s - 1) * hw

end ProbabilityTheory.Copula.RankRegion.RhoGamma
