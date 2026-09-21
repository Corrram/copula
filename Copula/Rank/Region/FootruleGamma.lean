/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.TauGamma

/-! # The exact Spearman footrule–Gini gamma region

Kokol Bukovšek–Mojškerc, *On the exact region determined
by Spearman's footrule and Gini's gamma* (2022). The quadrilateral is
also stated as Proposition 2.1 in Kokol Bukovšek–Mojškerc (2026).
The bounds below use absolute moments; mixtures fill its edges and fibres.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem integral_unit_abs_sub (a : I) :
    (∫ u : I, |(u : ℝ) - a|) = (a : ℝ) ^ 2 - a + 1 / 2 := by
  rw [integral_unitInterval (fun u : ℝ => |u - a|)]
  have hc : Continuous (fun u : ℝ => |u - a|) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (a := 0) (b := a)) (hc.intervalIntegrable (a := a) (b := 1))]
  have hl : (∫ u in (0 : ℝ)..a, |u - a|) = ∫ u in (0 : ℝ)..a, ((a : ℝ) - u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le a.property.1] at hu
    change |u - (a : ℝ)| = (a : ℝ) - u
    rw [abs_of_nonpos (sub_nonpos.mpr hu.2)]
    ring
  have hr : (∫ u in (a : ℝ)..1, |u - a|) = ∫ u in (a : ℝ)..1, (u - a) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le a.property.2] at hu
    exact abs_of_nonneg (sub_nonneg.mpr hu.1)
  rw [hl, hr, intervalIntegral.integral_sub, intervalIntegral.integral_sub,
    intervalIntegral.integral_const, intervalIntegral.integral_const, integral_id, integral_id]
  · simp only [smul_eq_mul]; ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

private noncomputable def quarterCost (u : ℝ) : ℝ := |u - 1 / 4| + |u - 3 / 4|

@[fun_prop] private theorem continuous_quarterCost : Continuous quarterCost := by
  unfold quarterCost
  fun_prop

private theorem quarterCost_lower (u : ℝ) : 1 / 2 ≤ quarterCost u := by
  have h := abs_sub (u - 1 / 4) (u - 3 / 4)
  norm_num [show u - 1 / 4 - (u - 3 / 4) = 1 / 2 by ring] at h
  exact h

private theorem quarterCost_abs (u : ℝ) : |2 * u - 1| ≤ quarterCost u := by
  simpa only [quarterCost, show u - 1 / 4 + (u - 3 / 4) = 2 * u - 1 by ring] using
    abs_add_le (u - 1 / 4) (u - 3 / 4)

private theorem displacement_sum_upper (u v : ℝ) :
    |u - v| + |u + v - 1| ≤ quarterCost u + quarterCost v - 1 / 2 := by
  have hu := quarterCost_abs u
  have hv := quarterCost_abs v
  have hlu := quarterCost_lower u
  have hlv := quarterCost_lower v
  have hu1 := (abs_le.mp hu).1
  have hu2 := (abs_le.mp hu).2
  have hv1 := (abs_le.mp hv).1
  have hv2 := (abs_le.mp hv).2
  simp only [abs_eq_max_neg]
  simp only [max_def]
  split_ifs <;> linarith

private theorem integral_quarterCost : (∫ u : I, quarterCost u) = 5 / 8 := by
  unfold quarterCost
  rw [integral_add (integrable_continuous_unit volume (by fun_prop))
    (integrable_continuous_unit volume (by fun_prop))]
  have h1 := integral_unit_abs_sub (⟨1 / 4, by norm_num, by norm_num⟩ : I)
  have h3 := integral_unit_abs_sub (⟨3 / 4, by norm_num, by norm_num⟩ : I)
  norm_num at h1 h3
  linarith

theorem footrule_le_giniGamma (C : Copula 2) :
    4 / 3 * C.spearmanFootrule - 1 / 3 ≤ C.giniGamma := by
  have h (x : Fin 2 → I) : |2 * (x 0 : ℝ) - 1| ≤
      |(x 0 : ℝ) - x 1| + |(x 0 : ℝ) + x 1 - 1| := by
    simpa only [show (x 0 : ℝ) - x 1 + ((x 0 : ℝ) + x 1 - 1) = 2 * (x 0 : ℝ) - 1 by ring]
      using abs_add_le ((x 0 : ℝ) - x 1) ((x 0 : ℝ) + x 1 - 1)
  have hi := integral_mono (integrable_continuous_cube C.toMeasure (by fun_prop))
    (integrable_continuous_cube C.toMeasure (by fun_prop)) h
  have he : (fun u : I => |2 * (u : ℝ) - 1|) = fun u : I => 2 * |(u : ℝ) - 1 / 2| := by
    funext u
    rw [show 2 * (u : ℝ) - 1 = 2 * ((u : ℝ) - 1 / 2) by ring, abs_mul]
    norm_num
  have hh := integral_unit_abs_sub unitHalf
  norm_num [unitHalf] at hh
  rw [C.integral_eval 0 (fun u : I => |2 * (u : ℝ) - 1|) (by fun_prop), he, integral_const_mul,
    hh, integral_add] at hi
  · have hp := RankRegion.footrule_eq_abs_moment C
    rw [RankRegion.gamma_eq_abs_moments, integral_sub]
    · norm_num [unitHalf] at hi
      linarith
    all_goals exact integrable_continuous_cube C.toMeasure (by fun_prop)
  all_goals exact integrable_continuous_cube C.toMeasure (by fun_prop)

theorem giniGamma_le_footrule (C : Copula 2) :
    C.giniGamma ≤ min (4 / 3 * C.spearmanFootrule + 1 / 6)
      (2 / 3 * C.spearmanFootrule + 1 / 3) := by
  apply le_min
  · have hi := integral_mono (integrable_continuous_cube C.toMeasure (by fun_prop))
      (integrable_continuous_cube C.toMeasure (by fun_prop))
      (fun x : Fin 2 → I => displacement_sum_upper (x 0) (x 1))
    rw [integral_add, integral_sub, integral_add,
      C.integral_eval 0 (fun u : I => quarterCost u) (by fun_prop),
      C.integral_eval 1 (fun u : I => quarterCost u) (by fun_prop), integral_quarterCost] at hi
    · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
      have hp := RankRegion.footrule_eq_abs_moment C
      rw [RankRegion.gamma_eq_abs_moments, integral_sub]
      · linarith
      all_goals exact integrable_continuous_cube C.toMeasure (by fun_prop)
    all_goals exact integrable_continuous_cube C.toMeasure (by fun_prop)
  · have h := (C.reflect {1}).spearmanFootrule_mem_Icc.1
    rw [giniGamma_eq_footrule_sub_reflect]
    linarith

namespace RankRegion.FootruleGamma

theorem exists_lower {p : ℝ} (hp : p ∈ Icc (-1 / 2) 1) :
    ∃ C : Copula 2, C.spearmanFootrule = p ∧ C.giniGamma = 4 / 3 * p - 1 / 3 := by
  let a : I := ⟨(2 * p + 1) / 3, by constructor <;> linarith [hp.1, hp.2]⟩
  refine ⟨(comonotonic 2).mix countermonotonic a, ?_, ?_⟩
  · simp only [spearmanFootrule_mix, spearmanFootrule_comonotonic, spearmanFootrule_countermonotonic]
    dsimp [a]; ring
  · simp only [giniGamma_mix, giniGamma_comonotonic, giniGamma_countermonotonic]
    dsimp [a]; ring

theorem exists_upper {p : ℝ} (hp : p ∈ Icc (-1 / 2) 1) :
    ∃ C : Copula 2, C.spearmanFootrule = p ∧
      C.giniGamma = min (4 / 3 * p + 1 / 6) (2 / 3 * p + 1 / 3) := by
  have hc := TauGamma.corner_coefficients
  have hr : (TauGamma.corner.reflect {1}).spearmanFootrule = -1 / 2 :=
    spearmanFootrule_reflect_ordinalSum_half _ _
  by_cases h : p ≤ 1 / 4
  · let a : I := ⟨(4 * p + 2) / 3, by constructor <;> linarith [hp.1]⟩
    refine ⟨TauGamma.corner.mix (TauGamma.corner.reflect {1}) a, ?_, ?_⟩
    · rw [spearmanFootrule_mix, hc.2.2, hr]
      dsimp [a]; ring
    · rw [giniGamma_mix, giniGamma_reflect_second, hc.1, min_eq_left (by linarith)]
      dsimp [a]; ring
  · let a : I := ⟨(4 * p - 1) / 3, by constructor <;> linarith [hp.2]⟩
    refine ⟨(comonotonic 2).mix TauGamma.corner a, ?_, ?_⟩
    · rw [spearmanFootrule_mix, spearmanFootrule_comonotonic, hc.2.2]
      dsimp [a]; ring
    · rw [giniGamma_mix, giniGamma_comonotonic, hc.1, min_eq_right (by linarith)]
      dsimp [a]; ring

theorem exists_copula_iff (p g : ℝ) :
    (∃ C : Copula 2, C.spearmanFootrule = p ∧ C.giniGamma = g) ↔
      p ∈ Icc (-1 / 2) 1 ∧ 4 / 3 * p - 1 / 3 ≤ g ∧
      g ≤ min (4 / 3 * p + 1 / 6) (2 / 3 * p + 1 / 3) := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    exact ⟨C.spearmanFootrule_mem_Icc, C.footrule_le_giniGamma, C.giniGamma_le_footrule⟩
  · rintro ⟨hp, hl, hu⟩
    obtain ⟨C, hC, hgC⟩ := exists_lower hp
    obtain ⟨D, hD, hgD⟩ := exists_upper hp
    have hcont : Continuous (fun a : I => (D.mix C a).giniGamma) := by
      simp_rw [giniGamma_mix]; fun_prop
    obtain ⟨a, ha⟩ := exists_unitInterval_eq (z := g) hcont
      (by simpa only [mix_zero, hgC] using hl) (by simpa only [mix_one, hgD] using hu)
    refine ⟨D.mix C a, ?_, ha⟩
    rw [spearmanFootrule_mix, hD, hC]
    ring

end RankRegion.FootruleGamma
end ProbabilityTheory.Copula
