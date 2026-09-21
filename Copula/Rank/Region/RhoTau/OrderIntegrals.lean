/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.OrderSigns
import Copula.Rank.ConcordanceProbability
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter Set
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

theorem norm_orderSign_le_one {α : Type*} [LinearOrder α] (x y : α) :
    ‖orderSign x y‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  exact orderSign_mem x y

theorem measurable_orderSign : Measurable (fun p : I × I => orderSign p.1 p.2) := by
  exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd) measurable_const
    (Measurable.ite (measurableSet_lt measurable_snd measurable_fst) measurable_const measurable_const)

theorem integral_orderSign (C : Copula 2) (i : Fin 2) (t : I) :
    (∫ x, orderSign t (x i) ∂C.toMeasure) = 1 - 2 * (t : ℝ) := by
  let s : Set (Fin 2 → I) := {x | x i ≤ t}
  have hs : MeasurableSet s := measurableSet_le (measurable_pi_apply i) measurable_const
  have he : (fun x => orderSign t (x i)) =ᵐ[C.toMeasure]
      fun x => 1 - 2 * s.indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [C.ae_eval_ne i t] with x hx
    rcases lt_or_gt_of_ne hx with h | h
    · norm_num [orderSign, s, h, not_lt_of_ge h.le, h.le]
    · simp [orderSign, s, h, not_le_of_gt h]
  erw [integral_congr_ae he, integral_sub (integrable_const 1)
    (((integrable_const (1 : ℝ)).indicator hs).const_mul 2), integral_const_mul,
    integral_indicator_one hs]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [show C.toMeasure.real s = (t : ℝ) from C.measureReal_eval_le i t]

theorem integral_rank_product (C : Copula 2) :
    3 * (∫ x, (1 - 2 * (x 0 : ℝ)) * (1 - 2 * (x 1 : ℝ)) ∂C.toMeasure) =
      C.spearmanRho := by
  have he : (fun x : Fin 2 → I => (1 - 2 * (x 0 : ℝ)) * (1 - 2 * (x 1 : ℝ))) =
      fun x => 1 - 2 * (x 0 : ℝ) - 2 * (x 1 : ℝ) + 4 * ((x 0 : ℝ) * (x 1 : ℝ)) := by
    funext x; ring
  rw [he, integral_add, integral_sub, integral_sub, integral_const_mul,
    integral_const_mul, integral_const_mul, C.integral_coe_eval, C.integral_coe_eval]
  · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, spearmanRho]
    ring
  all_goals exact integrable_continuous_cube C.toMeasure (by fun_prop)

theorem integral_orderSign_product (C : Copula 2) :
    (∫ p, orderSign (p.1 0) (p.2 0) * orderSign (p.1 1) (p.2 1)
      ∂C.toMeasure.prod C.toMeasure) = C.kendallTau := by
  have he : (fun p : (Fin 2 → I) × (Fin 2 → I) =>
      orderSign (p.1 0) (p.2 0) * orderSign (p.1 1) (p.2 1)) =ᵐ[C.toMeasure.prod C.toMeasure]
      fun p => concordantPairs.indicator (fun _ => (1 : ℝ)) p -
        discordantPairs.indicator (fun _ => (1 : ℝ)) p := by
    filter_upwards [C.ae_prod_eval_ne C 0, C.ae_prod_eval_ne C 1] with p h0 h1
    rcases lt_or_gt_of_ne h0 with h0 | h0 <;> rcases lt_or_gt_of_ne h1 with h1 | h1
    · have hp := mul_pos_of_neg_of_neg (sub_neg.mpr (show (p.1 0 : ℝ) < p.2 0 from h0))
        (sub_neg.mpr (show (p.1 1 : ℝ) < p.2 1 from h1))
      simp [orderSign, h0, h1, concordantPairs, discordantPairs, hp, not_lt_of_ge hp.le]
    · have hp := mul_neg_of_neg_of_pos (sub_neg.mpr (show (p.1 0 : ℝ) < p.2 0 from h0))
        (sub_pos.mpr (show (p.2 1 : ℝ) < p.1 1 from h1))
      simp [orderSign, h0, h1, not_lt_of_ge h1.le, concordantPairs, discordantPairs,
        hp, not_lt_of_ge hp.le]
    · have hp := mul_neg_of_pos_of_neg (sub_pos.mpr (show (p.2 0 : ℝ) < p.1 0 from h0))
        (sub_neg.mpr (show (p.1 1 : ℝ) < p.2 1 from h1))
      simp [orderSign, h0, h1, not_lt_of_ge h0.le, concordantPairs, discordantPairs,
        hp, not_lt_of_ge hp.le]
    · have hp := mul_pos (sub_pos.mpr (show (p.2 0 : ℝ) < p.1 0 from h0))
        (sub_pos.mpr (show (p.2 1 : ℝ) < p.1 1 from h1))
      simp [orderSign, h0, h1, not_lt_of_ge h0.le, not_lt_of_ge h1.le,
        concordantPairs, discordantPairs, hp, not_lt_of_ge hp.le]
  erw [integral_congr_ae he, integral_sub
    ((integrable_const (1 : ℝ)).indicator measurableSet_concordantPairs)
    ((integrable_const (1 : ℝ)).indicator measurableSet_discordantPairs),
    integral_indicator_one measurableSet_concordantPairs,
    integral_indicator_one measurableSet_discordantPairs]
  exact C.kendallTau_eq_concordant_sub_discordant.symm

end ProbabilityTheory.Copula.RankRegion.RhoTau
