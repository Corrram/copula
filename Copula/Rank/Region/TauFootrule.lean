/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.DiagonalIntegral
import Copula.Rank.Region.Mixture
import Copula.Rank.MedianExtrema
import Copula.OrdinalSum.Rank

/-! # The exact Kendall tau–Spearman footrule region

Kokol Bukovšek–Stopar, *On the exact regions determined by Kendall's tau
and other concordance measures* (2023), Theorem 4.
The lower-bound argument is applied directly to a copula measure.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem kendallTau_le_footrule (C : Copula 2) :
    C.kendallTau ≤ 2 / 3 * C.spearmanFootrule + 1 / 3 := by
  have h := (show C.LowerOrthantLE (comonotonic 2) from C.cdf_le_comonotonic).concordanceQ_le_right C
  rw [concordanceQ_self, concordanceQ_comonotonic] at h
  linarith

theorem footrule_le_kendallTau (C : Copula 2) :
    4 / 3 * C.spearmanFootrule - 1 / 3 ≤ C.kendallTau := by
  have hp (x : Fin 2 → I) :
      C.diagonal (x 0) + C.diagonal (x 1) - C.diagonal (max (x 0) (x 1)) ≤ C.cdf x := by
    rcases le_total (x 0) (x 1) with h | h
    · rw [max_eq_right h, add_sub_cancel_right]
      apply C.monotone_cdf
      intro i; fin_cases i <;> simp [h]
    · rw [max_eq_left h, add_sub_cancel_left]
      apply C.monotone_cdf
      intro i; fin_cases i <;> simp [h]
  have hi := integral_mono (integrable_continuous_cube C.toMeasure (by fun_prop))
    (C.integrable_cdf C.toMeasure) hp
  rw [integral_sub, integral_add,
    C.integral_eval 0 C.diagonal C.continuous_diagonal.measurable,
    C.integral_eval 1 C.diagonal C.continuous_diagonal.measurable,
    C.integral_diagonal_max] at hi
  · unfold kendallTau spearmanFootrule
    change _ ≤ 4 * (∫ x, C.cdf x ∂C.toMeasure) - 1
    change (∫ t : I, C.cdf ![t, t]) + (∫ t : I, C.cdf ![t, t]) - 1 / 2 ≤ _ at hi
    linarith
  all_goals exact integrable_continuous_cube C.toMeasure (by fun_prop)

namespace RankRegion.TauFootrule

/-- Lower boundary family (Example 2 of the source). -/
noncomputable def lowerCopula (a : I) : Copula 2 :=
  (comonotonic 2).ordinalSum countermonotonic a

/-- A rescaled half-turn supplies the upper boundary. -/
noncomputable def upperCopula (a : I) : Copula 2 :=
  (comonotonic 2).ordinalSum
    ((countermonotonic.ordinalSum countermonotonic unitHalf).reflect {1}) a

theorem lowerCopula_coefficients (a : I) :
    (lowerCopula a).spearmanFootrule = 1 - 3 / 2 * (1 - (a : ℝ)) ^ 2 ∧
    (lowerCopula a).kendallTau = 1 - 2 * (1 - (a : ℝ)) ^ 2 := by
  simp only [lowerCopula, spearmanFootrule_ordinalSum, kendallTau_ordinalSum,
    spearmanFootrule_comonotonic, spearmanFootrule_countermonotonic,
    kendallTau_comonotonic, kendallTau_countermonotonic]
  constructor <;> ring

theorem upperCopula_coefficients (a : I) :
    (upperCopula a).spearmanFootrule = 1 - 3 / 2 * (1 - (a : ℝ)) ^ 2 ∧
    (upperCopula a).kendallTau = 1 - (1 - (a : ℝ)) ^ 2 := by
  simp only [upperCopula, spearmanFootrule_ordinalSum, kendallTau_ordinalSum,
    spearmanFootrule_comonotonic, spearmanFootrule_reflect_ordinalSum_half,
    kendallTau_reflect_second, kendallTau_countermonotonic, kendallTau_comonotonic]
  norm_num [unitHalf]
  ring

/-- Every value between the two sharp bounds is attained. -/
theorem exists_copula {p t : ℝ} (hp : p ∈ Set.Icc (-1 / 2) 1)
    (hl : 4 / 3 * p - 1 / 3 ≤ t) (hu : t ≤ 2 / 3 * p + 1 / 3) :
    ∃ C : Copula 2, C.spearmanFootrule = p ∧ C.kendallTau = t := by
  obtain ⟨a, ha⟩ := exists_unitInterval_eq (z := p)
    (f := fun a : I => 1 - 3 / 2 * (1 - (a : ℝ)) ^ 2) (by fun_prop)
    (by norm_num; linarith [hp.1]) (by norm_num; exact hp.2)
  obtain ⟨b, hb⟩ := exists_unitInterval_eq (z := t)
    (continuous_tau_mix (upperCopula a) (lowerCopula a))
    (by simp only [mix_zero]; rw [(lowerCopula_coefficients a).2]; nlinarith [hl, ha])
    (by simp only [mix_one]; rw [(upperCopula_coefficients a).2]; nlinarith [hu, ha])
  refine ⟨(upperCopula a).mix (lowerCopula a) b, ?_, hb⟩
  rw [spearmanFootrule_mix, (upperCopula_coefficients a).1,
    (lowerCopula_coefficients a).1, ha]
  ring

/-- Exact membership, including the three vertices and every boundary point. -/
theorem exists_copula_iff (p t : ℝ) :
    (∃ C : Copula 2, C.spearmanFootrule = p ∧ C.kendallTau = t) ↔
      p ∈ Set.Icc (-1 / 2) 1 ∧ 4 / 3 * p - 1 / 3 ≤ t ∧ t ≤ 2 / 3 * p + 1 / 3 := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    exact ⟨C.spearmanFootrule_mem_Icc, C.footrule_le_kendallTau, C.kendallTau_le_footrule⟩
  · rintro ⟨hp, hl, hu⟩
    exact exists_copula hp hl hu

end RankRegion.TauFootrule
end ProbabilityTheory.Copula
