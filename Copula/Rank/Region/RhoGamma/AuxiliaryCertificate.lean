/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoGamma.AuxiliaryEndpoints

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoGamma

/-- The analytic data used in gluing, with concrete instances for every auxiliary branch. -/
structure AuxiliaryCertificate where
  s : ℝ
  s_pos : 0 < s
  w : ℝ
  w_nonneg : 0 ≤ w
  c : ℝ
  c_neg : c < 0
  discriminant : w ^ 2 ≤ s ^ 2 + 2 * c
  h : ℝ → ℝ
  lipschitz : LipschitzWith ⟨w, w_nonneg⟩ h
  at_zero : h 0 = c
  D : Copula 2
  feasible : ∀ u v : I, h u + h v ≤ ((u : ℝ) - v) ^ 2 - s * |(u : ℝ) - v|
  contact : ∀ᵐ x ∂D.toMeasure,
    h (x 0) + h (x 1) = ((x 0 : ℝ) - x 1) ^ 2 - s * |(x 0 : ℝ) - x 1|

theorem auxiliary_contact_of_integral (D : Copula 2) (s : ℝ) {h : ℝ → ℝ}
    (hh : Continuous h)
    (hf : ∀ u v : I, h u + h v ≤ ((u : ℝ) - v) ^ 2 - s * |(u : ℝ) - v|)
    (hi : (∫ x, ((x 0 : ℝ) - x 1) ^ 2 ∂D.toMeasure) -
      s * (∫ x, |(x 0 : ℝ) - x 1| ∂D.toMeasure) = 2 * ∫ u : I, h u) :
    ∀ᵐ x ∂D.toMeasure,
      h (x 0) + h (x 1) = ((x 0 : ℝ) - x 1) ^ 2 - s * |(x 0 : ℝ) - x 1| := by
  apply (integral_eq_iff_of_ae_le (integrable_continuous_cube _ (by fun_prop))
    (integrable_continuous_cube _ (by fun_prop)) (Filter.Eventually.of_forall fun x => hf (x 0) (x 1))).mp
  rw [integral_add (integrable_continuous_cube _ (by fun_prop)) (integrable_continuous_cube _ (by fun_prop)),
    D.integral_eval 0 (fun u : I => h u) (by fun_prop),
    D.integral_eval 1 (fun u : I => h u) (by fun_prop),
    integral_sub (integrable_continuous_cube _ (by fun_prop)) (integrable_continuous_cube _ (by fun_prop)),
    integral_const_mul, hi]
  ring

namespace AuxiliaryCertificate

open RhoFootrule.UpperSpline

noncomputable def ofRight (S : RhoFootrule.RightData) : AuxiliaryCertificate where
  s := period S.N S.v S.w
  s_pos := S.period_pos
  w := S.v
  w_nonneg := S.v_nonneg
  c := offset S.N S.v S.w
  c_neg := right_offset_neg (by exact_mod_cast S.N_pos) S.v_nonneg S.w_nonneg S.period_pos
  discriminant := right_discriminant_bound (Nat.cast_nonneg _) S.v_nonneg S.w_nonneg
  h := S.dual
  lipschitz := right_dual_lipschitz S
  at_zero := right_dual_zero S
  D := S.copula
  feasible := by
    intro u v
    have hh := potential_feasible (by exact_mod_cast S.N_pos) S.v_nonneg S.w_nonneg S.period_pos (v : ℝ) (u : ℝ)
    simpa only [RhoFootrule.RightData.dual, add_comm] using hh
  contact := auxiliary_contact_of_integral S.copula _ S.continuous_dual (by
    intro u v
    have hh := potential_feasible (by exact_mod_cast S.N_pos) S.v_nonneg S.w_nonneg S.period_pos (v : ℝ) (u : ℝ)
    simpa only [RhoFootrule.RightData.dual, add_comm] using hh) S.cost_attained

noncomputable def ofLeft (S : RhoFootrule.LeftData) : AuxiliaryCertificate where
  s := period S.N S.v S.w
  s_pos := S.period_pos
  w := S.v
  w_nonneg := S.v_nonneg
  c := offset S.N S.v S.w + S.v * S.w
  c_neg := left_offset_neg (by exact_mod_cast S.N_pos) S.v_nonneg S.w_nonneg S.period_pos
  discriminant := left_discriminant_bound (Nat.cast_nonneg _) S.v_nonneg S.w_nonneg
  h := S.dual
  lipschitz := left_dual_lipschitz S
  at_zero := left_dual_zero S
  D := S.copula
  feasible := by
    intro u v
    have hh := potential_feasible (by exact_mod_cast S.N_pos) S.v_nonneg S.w_nonneg S.period_pos
      ((v : ℝ) + S.w) ((u : ℝ) + S.w)
    rw [add_sub_add_right_eq_sub] at hh
    simpa only [RhoFootrule.LeftData.dual, add_comm] using hh
  contact := auxiliary_contact_of_integral S.copula _ S.continuous_dual (by
    intro u v
    have hh := potential_feasible (by exact_mod_cast S.N_pos) S.v_nonneg S.w_nonneg S.period_pos
      ((v : ℝ) + S.w) ((u : ℝ) + S.w)
    rw [add_sub_add_right_eq_sub] at hh
    simpa only [RhoFootrule.LeftData.dual, add_comm] using hh) S.cost_attained

noncomputable def halfShift (s : ℝ) (hs : 1 ≤ s) : AuxiliaryCertificate where
  s := s
  s_pos := by linarith
  w := s - 1
  w_nonneg := sub_nonneg.mpr hs
  c := 3 / 8 - s / 2
  c_neg := (halfShift_endpoint_properties hs).1
  discriminant := (halfShift_endpoint_properties hs).2
  h := halfShiftPotentialReal s
  lipschitz := halfShiftPotentialReal_lipschitz hs
  at_zero := by norm_num [halfShiftPotentialReal]
  D := RhoFootrule.halfTurn
  feasible := halfShiftPotential_feasible hs
  contact := halfShiftPotential_contact s

end AuxiliaryCertificate
end ProbabilityTheory.Copula.RankRegion.RhoGamma
