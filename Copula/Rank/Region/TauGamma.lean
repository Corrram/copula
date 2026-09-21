/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.TauFootrule
import Copula.Rank.Region.Moments
import Copula.OrdinalSum.RankExamples

/-! # Kendall tau and Gini gamma

The inequalities and boundary families of Kokol Bukovšek–Stopar (2023),
Theorem 6. The proof uses their reflection reduction to tau–footrule.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem giniGamma_eq_footrule_sub_reflect (C : Copula 2) :
    C.giniGamma = 2 / 3 * (C.spearmanFootrule - (C.reflect {1}).spearmanFootrule) := by
  unfold giniGamma spearmanFootrule
  simp only [cdf_reflect_second]
  rw [integral_sub (integrable_continuous_unit volume (by fun_prop))
    C.integrable_antidiagonal_cdf, integral_unit_id]
  ring

theorem kendallTau_le_gamma (C : Copula 2) :
    C.kendallTau ≤ min (2 / 3 * C.giniGamma + 1 / 3) (2 * C.giniGamma + 1) := by
  have hu := C.kendallTau_le_footrule
  have hl := (C.reflect {1}).footrule_le_kendallTau
  rw [kendallTau_reflect_second] at hl
  have hg := C.giniGamma_eq_footrule_sub_reflect
  have hp := C.spearmanFootrule_mem_Icc.1
  exact le_min (by linarith) (by linarith)

theorem gamma_le_kendallTau (C : Copula 2) :
    max (2 / 3 * C.giniGamma - 1 / 3) (2 * C.giniGamma - 1) ≤ C.kendallTau := by
  have h := (C.reflect {1}).kendallTau_le_gamma
  rw [kendallTau_reflect_second, giniGamma_reflect_second] at h
  have h1 := h.trans (min_le_left _ _)
  have h2 := h.trans (min_le_right _ _)
  exact max_le (by linarith) (by linarith)

/-- The two-countermonotonic-block family in Example 5 of the source. -/
theorem giniGamma_ordinalSum_countermonotonic (a : I) :
    (countermonotonic.ordinalSum countermonotonic a).giniGamma =
      6 * (a : ℝ) * (1 - (a : ℝ)) - 1 := by
  let C := countermonotonic.ordinalSum countermonotonic a
  have habs : (∫ x, |(x 0 : ℝ) + x 1 - 1| ∂C.toMeasure) =
      2 * (a : ℝ) * (1 - (a : ℝ)) := by
    rw [integral_ordinalSum _ _ _ (by fun_prop)]
    rw [integral_countermonotonic _ (by fun_prop), integral_countermonotonic _ (by fun_prop)]
    simp only [OrdinalSum.lowerEmbed, OrdinalSum.upperEmbed, Matrix.cons_val_zero,
      Matrix.cons_val_one, unitInterval.coe_symm_eq]
    have hl (t : I) : (a : ℝ) * t + (a : ℝ) * (1 - (t : ℝ)) - 1 = (a : ℝ) - 1 := by ring
    have hu (t : I) : (a : ℝ) + (1 - (a : ℝ)) * t +
        ((a : ℝ) + (1 - (a : ℝ)) * (1 - (t : ℝ))) - 1 = (a : ℝ) := by ring
    simp_rw [hl, hu, abs_of_nonpos (sub_nonpos.mpr a.property.2),
      abs_of_nonneg a.property.1]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  have hp := RankRegion.footrule_eq_abs_moment C
  have hpc := spearmanFootrule_ordinalSum_countermonotonic a
  change C.spearmanFootrule = _ at hpc
  rw [hpc] at hp
  rw [RankRegion.gamma_eq_abs_moments, integral_sub, habs]
  · linarith
  all_goals exact integrable_continuous_cube C.toMeasure (by fun_prop)

namespace RankRegion.TauGamma

/-- The non-Fréchet positive-gamma vertex of the parallelogram. -/
noncomputable def corner : Copula 2 :=
  countermonotonic.ordinalSum countermonotonic unitHalf

theorem corner_coefficients : corner.giniGamma = 1 / 2 ∧ corner.kendallTau = 0 ∧
    corner.spearmanFootrule = 1 / 4 := by
  norm_num [corner, giniGamma_ordinalSum_countermonotonic,
    kendallTau_ordinalSum_countermonotonic, spearmanFootrule_ordinalSum_countermonotonic, unitHalf]

theorem lower_boundary_left (a : I) :
    (countermonotonic.ordinalSum countermonotonic a).kendallTau =
      2 / 3 * (countermonotonic.ordinalSum countermonotonic a).giniGamma - 1 / 3 := by
  rw [kendallTau_ordinalSum_countermonotonic, giniGamma_ordinalSum_countermonotonic]
  ring

theorem lower_boundary_right (a : I) :
    (corner.mix (comonotonic 2) a).giniGamma = 1 - (a : ℝ) / 2 ∧
    (corner.mix (comonotonic 2) a).kendallTau = 1 - (a : ℝ) := by
  rw [giniGamma_mix, kendallTau_mix_comonotonic,
    corner_coefficients.1, corner_coefficients.2.1, corner_coefficients.2.2]
  simp only [giniGamma_comonotonic]
  constructor <;> ring

theorem exists_lower {g : ℝ} (hg : g ∈ Set.Icc (-1) 1) :
    ∃ C : Copula 2, C.giniGamma = g ∧
      C.kendallTau = max (2 / 3 * g - 1 / 3) (2 * g - 1) := by
  by_cases h : g ≤ 1 / 2
  · obtain ⟨a, ha⟩ := exists_unitInterval_eq (z := g)
      (f := fun a : I => 6 * ((a : ℝ) / 2) * (1 - (a : ℝ) / 2) - 1)
      (by fun_prop) (by norm_num; exact hg.1) (by norm_num; linarith)
    let b : I := ⟨(a : ℝ) / 2, by constructor <;> linarith [a.property.1, a.property.2]⟩
    refine ⟨countermonotonic.ordinalSum countermonotonic b, ?_, ?_⟩
    · exact (giniGamma_ordinalSum_countermonotonic b).trans ha
    · rw [lower_boundary_left, giniGamma_ordinalSum_countermonotonic]
      change 2 / 3 * (6 * ((a : ℝ) / 2) * (1 - (a : ℝ) / 2) - 1) - 1 / 3 = _
      rw [ha, max_eq_left (by linarith)]
  · let a : I := ⟨2 * (1 - g), by constructor <;> linarith [hg.2]⟩
    refine ⟨corner.mix (comonotonic 2) a, ?_, ?_⟩
    · rw [(lower_boundary_right a).1]
      dsimp [a]; ring
    · rw [(lower_boundary_right a).2, max_eq_right (by linarith)]
      dsimp [a]; ring

theorem exists_upper {g : ℝ} (hg : g ∈ Set.Icc (-1) 1) :
    ∃ C : Copula 2, C.giniGamma = g ∧
      C.kendallTau = min (2 / 3 * g + 1 / 3) (2 * g + 1) := by
  obtain ⟨C, hC, ht⟩ := exists_lower (g := -g) ⟨by linarith [hg.2], by linarith [hg.1]⟩
  refine ⟨C.reflect {1}, ?_, ?_⟩
  · rw [giniGamma_reflect_second, hC, neg_neg]
  · rw [kendallTau_reflect_second, ht]
    simp only [max_def, min_def]
    split_ifs <;> linarith

theorem exists_copula_iff (g t : ℝ) :
    (∃ C : Copula 2, C.giniGamma = g ∧ C.kendallTau = t) ↔
      g ∈ Set.Icc (-1) 1 ∧
      max (2 / 3 * g - 1 / 3) (2 * g - 1) ≤ t ∧
      t ≤ min (2 / 3 * g + 1 / 3) (2 * g + 1) := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    exact ⟨C.giniGamma_mem_Icc, C.gamma_le_kendallTau, C.kendallTau_le_gamma⟩
  · rintro ⟨hg, hl, hu⟩
    obtain ⟨C, hC, htC⟩ := exists_lower hg
    obtain ⟨D, hD, htD⟩ := exists_upper hg
    obtain ⟨a, ha⟩ := exists_unitInterval_eq (z := t) (continuous_tau_mix D C)
      (by simpa only [mix_zero, htC] using hl) (by simpa only [mix_one, htD] using hu)
    refine ⟨D.mix C a, ?_, ha⟩
    rw [giniGamma_mix, hD, hC]
    ring

end RankRegion.TauGamma
end ProbabilityTheory.Copula
