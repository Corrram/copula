/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoFootrule.Moments
import Copula.Rank.Region.RhoGamma.SignMagnitude
import Copula.Rank.Region.CenteredGamma

/-! # The sharp lower rho–footrule boundary

The lower boundary of Kokol Bukovšek–Stopar is certified by a truncated
quadratic potential. Its parameter is the width of the central diagonal
block of a Bertino copula.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoFootrule

noncomputable def lowerPotential (r u : ℝ) : ℝ :=
  max 0 (|2 * u - 1| ^ 2 - r * |2 * u - 1|) / 2

@[fun_prop] theorem continuous_lowerPotential (r : ℝ) : Continuous (lowerPotential r) := by
  unfold lowerPotential
  fun_prop

theorem lowerPotential_feasible {r : ℝ} (hr : 0 ≤ r) (u v : ℝ) :
    (u - v) ^ 2 - r * |u - v| ≤ lowerPotential r u + lowerPotential r v := by
  have ha := abs_nonneg (2 * u - 1)
  have hb := abs_nonneg (2 * v - 1)
  have hd := abs_nonneg (u - v)
  have hab : 2 * |u - v| ≤ |2 * u - 1| + |2 * v - 1| := by
    have h := abs_sub (2 * u - 1) (2 * v - 1)
    rw [show 2 * u - 1 - (2 * v - 1) = 2 * (u - v) by ring, abs_mul] at h
    norm_num at h
    exact h
  have hu0 := le_max_left 0 (|2 * u - 1| ^ 2 - r * |2 * u - 1|)
  have hv0 := le_max_left 0 (|2 * v - 1| ^ 2 - r * |2 * v - 1|)
  have hu := le_max_right 0 (|2 * u - 1| ^ 2 - r * |2 * u - 1|)
  have hv := le_max_right 0 (|2 * v - 1| ^ 2 - r * |2 * v - 1|)
  unfold lowerPotential
  by_cases h : |u - v| ≤ r
  · nlinarith [mul_nonneg hd (sub_nonneg.mpr h), sq_abs (u - v)]
  · have hm := mul_nonneg (sub_nonneg.mpr hab)
      (show 0 ≤ |2 * u - 1| + |2 * v - 1| + 2 * |u - v| - 2 * r by linarith)
    nlinarith [sq_nonneg (|2 * u - 1| - |2 * v - 1|), sq_abs (u - v)]

theorem integral_truncated_quadratic (r : I) :
    (∫ u : I, max 0 ((u : ℝ) ^ 2 - (r : ℝ) * u)) =
      1 / 3 - (r : ℝ) / 2 + (r : ℝ) ^ 3 / 6 := by
  rw [integral_unitInterval (fun u : ℝ => max 0 (u ^ 2 - (r : ℝ) * u))]
  have hc : Continuous (fun u : ℝ => max 0 (u ^ 2 - (r : ℝ) * u)) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (a := 0) (b := r)) (hc.intervalIntegrable (a := r) (b := 1))]
  have hl : (∫ u in (0 : ℝ)..r, max 0 (u ^ 2 - (r : ℝ) * u)) = 0 := by
    calc
      _ = ∫ _ in (0 : ℝ)..r, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le r.property.1] at hu
        exact max_eq_left (by nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)])
      _ = 0 := by simp
  have hh : (∫ u in (r : ℝ)..1, max 0 (u ^ 2 - (r : ℝ) * u)) =
      ∫ u in (r : ℝ)..1, (u ^ 2 - (r : ℝ) * u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le r.property.2] at hu
    exact max_eq_right (by nlinarith [mul_nonneg (le_trans r.property.1 hu.1) (sub_nonneg.mpr hu.1)])
  rw [hl, hh, zero_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, integral_pow, integral_id]
  · norm_num; ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

theorem lowerPotential_integral (r : I) :
    (∫ u : I, lowerPotential r u) = 1 / 6 - (r : ℝ) / 4 + (r : ℝ) ^ 3 / 12 := by
  have hm := integral_map RhoGamma.continuous_rankMagnitude.measurable.aemeasurable
    (f := fun u : I => max 0 ((u : ℝ) ^ 2 - (r : ℝ) * u))
    (by fun_prop : AEStronglyMeasurable _ ((volume : Measure I).map RhoGamma.rankMagnitude))
  rw [RhoGamma.rankMagnitude_uniform, integral_truncated_quadratic] at hm
  unfold lowerPotential
  rw [integral_div]
  change (∫ u : I, max 0 (((RhoGamma.rankMagnitude u : I) : ℝ) ^ 2 -
    (r : ℝ) * RhoGamma.rankMagnitude u)) / 2 = _
  rw [← hm]
  ring

/-- Every parameter supplies a global supporting lower bound. -/
theorem lower_support (C : Copula 2) (r : I) :
    -1 + (r : ℝ) * (1 + 2 * C.spearmanFootrule) - (r : ℝ) ^ 3 ≤ C.spearmanRho := by
  have hi := integral_mono
    (integrable_continuous_cube C.toMeasure (by fun_prop))
    (integrable_continuous_cube C.toMeasure (by fun_prop))
    (fun x : Fin 2 → I => lowerPotential_feasible r.property.1 (x 0) (x 1))
  rw [integral_sub, integral_const_mul, integral_add,
    C.integral_eval 0 (fun u : I => lowerPotential r u) (by fun_prop),
    C.integral_eval 1 (fun u : I => lowerPotential r u) (by fun_prop),
    lowerPotential_integral] at hi
  · rw [C.spearmanRho_eq_one_sub, footrule_eq_abs_moment]
    nlinarith only [hi]
  all_goals exact integrable_continuous_cube C.toMeasure (by fun_prop)


/-- The sharp lower boundary, using a square-root parameter rather than real powers. -/
noncomputable def lowerBoundary (p : ℝ) : ℝ :=
  -1 + 2 * (Real.sqrt ((1 + 2 * p) / 3)) ^ 3

noncomputable def lowerParameter (p : ℝ) (hp : p ∈ Set.Icc (-1 / 2) 1) : I :=
  ⟨Real.sqrt ((1 + 2 * p) / 3), Real.sqrt_nonneg _, by
    have hs := Real.sq_sqrt (show 0 ≤ (1 + 2 * p) / 3 by linarith [hp.1])
    nlinarith [Real.sqrt_nonneg ((1 + 2 * p) / 3), hp.2]⟩

theorem lower_bound (C : Copula 2) : lowerBoundary C.spearmanFootrule ≤ C.spearmanRho := by
  have h := lower_support C (lowerParameter C.spearmanFootrule C.spearmanFootrule_mem_Icc)
  have hs := Real.sq_sqrt
    (show 0 ≤ (1 + 2 * C.spearmanFootrule) / 3 by linarith [C.spearmanFootrule_mem_Icc.1])
  dsimp [lowerParameter, lowerBoundary] at h ⊢
  nlinarith [congrArg (fun z : ℝ => z * Real.sqrt ((1 + 2 * C.spearmanFootrule) / 3)) hs]

/-- A central comonotonic block with countermonotonic outer pieces. -/
noncomputable def lowerCopula (r : I) : Copula 2 :=
  (centered countermonotonic r).reflect {1}

theorem lowerCopula_coefficients (r : I) :
    (lowerCopula r).spearmanFootrule = -1 / 2 + 3 / 2 * (r : ℝ) ^ 2 ∧
    (lowerCopula r).spearmanRho = -1 + 2 * (r : ℝ) ^ 3 := by
  have hW : countermonotonic.reflect {1} = comonotonic 2 := by
    rw [← reflect_comonotonic_eq_countermonotonic, reflect_reflect]
  simp only [lowerCopula, centered_reflect_footrule, hW, spearmanFootrule_comonotonic,
    spearmanRho_reflect_second, centered_rho, spearmanRho_countermonotonic]
  constructor <;> ring

/-- The sharp lower boundary is attained at every admissible footrule value. -/
theorem lowerBoundary_attained {p : ℝ} (hp : p ∈ Set.Icc (-1 / 2) 1) :
    ∃ C : Copula 2, C.spearmanFootrule = p ∧ C.spearmanRho = lowerBoundary p := by
  refine ⟨lowerCopula (lowerParameter p hp), ?_, ?_⟩
  · rw [(lowerCopula_coefficients _).1]
    dsimp [lowerParameter]
    rw [Real.sq_sqrt (by linarith [hp.1])]
    ring
  · exact (lowerCopula_coefficients _).2

/-- Global minimality of each constructed lower-boundary copula. -/
theorem lowerCopula_minimizes_rho (r : I) (C : Copula 2)
    (hp : C.spearmanFootrule = (lowerCopula r).spearmanFootrule) :
    (lowerCopula r).spearmanRho ≤ C.spearmanRho := by
  have h := lower_support C r
  rw [hp, (lowerCopula_coefficients r).1] at h
  rw [(lowerCopula_coefficients r).2]
  nlinarith only [h]

end ProbabilityTheory.Copula.RankRegion.RhoFootrule
