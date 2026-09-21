/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.Centered
import Copula.Rank.Region.TauGamma

/-! # Gini gamma and reflected footrule of a centered ordinal sum -/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion

theorem centered_abs_sum (C : Copula 2) (r : I) :
    (∫ x, |(x 0 : ℝ) + x 1 - 1| ∂(centered C r).toMeasure) =
      (1 - (r : ℝ) ^ 2) / 2 + (r : ℝ) ^ 2 *
        ∫ x, |(x 0 : ℝ) + x 1 - 1| ∂C.toMeasure := by
  let a := centeredEdge r
  let b := centeredSplit r
  have ha : (a : ℝ) = (1 - (r : ℝ)) / 2 := rfl
  have hb : (1 - (a : ℝ)) * (b : ℝ) = (r : ℝ) := by
    dsimp [a, b, centeredEdge, centeredSplit]
    have hd : 1 + (r : ℝ) ≠ 0 := by linarith [r.property.1]
    field_simp; ring
  have he : (1 - (a : ℝ)) * (1 - (b : ℝ)) = (a : ℝ) := by nlinarith [ha, hb]
  have hmid (x : Fin 2 → I) :
      |((OrdinalSum.upperEmbed a (OrdinalSum.lowerEmbed b (x 0))) : ℝ) +
        OrdinalSum.upperEmbed a (OrdinalSum.lowerEmbed b (x 1)) - 1| =
      (r : ℝ) * |(x 0 : ℝ) + x 1 - 1| := by
    change |(a : ℝ) + (1 - (a : ℝ)) * ((b : ℝ) * x 0) +
      ((a : ℝ) + (1 - (a : ℝ)) * ((b : ℝ) * x 1)) - 1| = _
    have hh : (a : ℝ) + (1 - (a : ℝ)) * ((b : ℝ) * x 0) +
        ((a : ℝ) + (1 - (a : ℝ)) * ((b : ℝ) * x 1)) - 1 =
        (r : ℝ) * ((x 0 : ℝ) + x 1 - 1) := by
      nlinarith [congrArg (fun z : ℝ => z * (x 0 : ℝ)) hb,
        congrArg (fun z : ℝ => z * (x 1 : ℝ)) hb]
    rw [hh, abs_mul, abs_of_nonneg r.property.1]
  have hlo (u : I) :
      |(OrdinalSum.lowerEmbed a u : ℝ) + OrdinalSum.lowerEmbed a u - 1| =
        1 - (1 - (r : ℝ)) * u := by
    change |(a : ℝ) * u + (a : ℝ) * u - 1| = _
    rw [abs_of_nonpos (by nlinarith [r.property.1, mul_nonneg a.property.1 (sub_nonneg.mpr u.property.2)])]
    nlinarith [congrArg (fun z : ℝ => z * (u : ℝ)) ha]
  have hhi (u : I) :
      |(OrdinalSum.upperEmbed a (OrdinalSum.upperEmbed b u) : ℝ) +
        OrdinalSum.upperEmbed a (OrdinalSum.upperEmbed b u) - 1| =
        (r : ℝ) + (1 - (r : ℝ)) * u := by
    have hh : (OrdinalSum.upperEmbed a (OrdinalSum.upperEmbed b u) : ℝ) =
        (a : ℝ) + (r : ℝ) + (a : ℝ) * u := by
      change (a : ℝ) + (1 - (a : ℝ)) * ((b : ℝ) + (1 - (b : ℝ)) * u) = _
      nlinarith [congrArg (fun z : ℝ => z * (u : ℝ)) he]
    rw [hh, abs_of_nonneg (by nlinarith [r.property.1, mul_nonneg a.property.1 u.property.1])]
    nlinarith [congrArg (fun z : ℝ => z * (u : ℝ)) ha]
  change (∫ x, |(x 0 : ℝ) + x 1 - 1| ∂
    ((comonotonic 2).ordinalSum (C.ordinalSum (comonotonic 2) b) a).toMeasure) = _
  rw [integral_ordinalSum _ _ _ (by fun_prop),
    integral_ordinalSum _ _ _ (by fun_prop),
    integral_comonotonic _ (by fun_prop), integral_comonotonic _ (by fun_prop)]
  simp_rw [hlo, hhi, hmid]
  rw [integral_sub, integral_add, integral_const_mul, integral_const_mul,
    integral_const, integral_const, integral_unit_id]
  · simp only [probReal_univ, smul_eq_mul, one_mul]
    rw [mul_add (1 - (a : ℝ))]
    simp only [← mul_assoc, hb, he]
    rw [ha]
    ring
  all_goals exact integrable_continuous_unit volume (by fun_prop)

theorem centered_gamma (C : Copula 2) (r : I) :
    (centered C r).giniGamma = 1 - (r : ℝ) ^ 2 * (1 - C.giniGamma) := by
  have hd : (∫ x, |(x 0 : ℝ) - x 1| ∂(centered C r).toMeasure) =
      (r : ℝ) ^ 2 * ∫ x, |(x 0 : ℝ) - x 1| ∂C.toMeasure := by
    have h := centered_footrule C r
    rw [footrule_eq_abs_moment, footrule_eq_abs_moment] at h
    nlinarith only [h]
  rw [gamma_eq_abs_moments, gamma_eq_abs_moments, integral_sub, integral_sub,
    centered_abs_sum, hd]
  · ring
  all_goals exact integrable_continuous_cube _ (by fun_prop)

theorem centered_reflect_footrule (C : Copula 2) (r : I) :
    ((centered C r).reflect {1}).spearmanFootrule =
      -1 / 2 + (r : ℝ) ^ 2 * (1 / 2 + (C.reflect {1}).spearmanFootrule) := by
  have h := (centered C r).giniGamma_eq_footrule_sub_reflect
  rw [centered_gamma, centered_footrule, C.giniGamma_eq_footrule_sub_reflect] at h
  nlinarith only [h]

end ProbabilityTheory.Copula.RankRegion
