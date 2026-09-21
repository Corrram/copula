/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoBeta
import Copula.Rank.Region.Centered
import Copula.Rank.Region.Basic

/-! # The four exact regions involving Blomqvist beta

The fixed-median bounds recalled by Kokol Bukovšek et al. are attained by
centered half-turn shuffles and their reflections. Mixture paths preserve
beta and fill every fibre, including when the other coefficient is tau.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.Beta

/-- A centered half-turn is simultaneously extremal for all four other coefficients. -/
noncomputable def upperCopula (r : I) : Copula 2 :=
  centered (TauGamma.corner.reflect {1}) r

theorem upperCopula_coefficients (r : I) :
    (upperCopula r).blomqvistBeta = 1 - 2 * (r : ℝ) ∧
    (upperCopula r).spearmanRho = 1 - 3 / 2 * (r : ℝ) ^ 3 ∧
    (upperCopula r).kendallTau = 1 - (r : ℝ) ^ 2 ∧
    (upperCopula r).spearmanFootrule = 1 - 3 / 2 * (r : ℝ) ^ 2 ∧
    (upperCopula r).giniGamma = 1 - 3 / 2 * (r : ℝ) ^ 2 := by
  have hb0 : (TauGamma.corner.reflect {1}).blomqvistBeta = -1 :=
    blomqvistBeta_reflect_ordinalSum_half _ _
  have hp0 : (TauGamma.corner.reflect {1}).spearmanFootrule = -1 / 2 :=
    spearmanFootrule_reflect_ordinalSum_half _ _
  have hr0 : (TauGamma.corner.reflect {1}).spearmanRho = -1 / 2 := by
    rw [spearmanRho_reflect_second, TauGamma.corner, spearmanRho_ordinalSum_countermonotonic]
    norm_num [unitHalf]
  have ht0 : (TauGamma.corner.reflect {1}).kendallTau = 0 := by
    rw [kendallTau_reflect_second, TauGamma.corner_coefficients.2.1, neg_zero]
  have hb : (upperCopula r).blomqvistBeta = 1 - 2 * (r : ℝ) := by
    rw [upperCopula, centered_beta, hb0]; ring
  have hr : (upperCopula r).spearmanRho = 1 - 3 / 2 * (r : ℝ) ^ 3 := by
    rw [upperCopula, centered_rho, hr0]; ring
  have ht : (upperCopula r).kendallTau = 1 - (r : ℝ) ^ 2 := by
    rw [upperCopula, centered_tau, ht0]; ring
  have hp : (upperCopula r).spearmanFootrule = 1 - 3 / 2 * (r : ℝ) ^ 2 := by
    rw [upperCopula, centered_footrule, hp0]; ring
  refine ⟨hb, hr, ht, hp, ?_⟩
  have hu := (upperCopula r).giniGamma_le_beta
  have hl := (upperCopula r).kendallTau_le_gamma.trans (min_le_left _ _)
  rw [hb] at hu
  rw [ht] at hl
  nlinarith

/-- All four upper boundaries have a common witness at every prescribed beta. -/
theorem exists_upper {b : ℝ} (hb : b ∈ Set.Icc (-1) 1) :
    ∃ C : Copula 2, C.blomqvistBeta = b ∧
      C.spearmanRho = 1 - 3 / 16 * (1 - b) ^ 3 ∧
      C.kendallTau = 1 - 1 / 4 * (1 - b) ^ 2 ∧
      C.spearmanFootrule = 1 - 3 / 8 * (1 - b) ^ 2 ∧
      C.giniGamma = 1 - 3 / 8 * (1 - b) ^ 2 := by
  let r : I := ⟨(1 - b) / 2, by constructor <;> linarith [hb.1, hb.2]⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := upperCopula_coefficients r
  refine ⟨upperCopula r, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | rw [h1] | rw [h2] | rw [h3] | rw [h4] | rw [h5]
  all_goals dsimp [r]; ring

/-- Reflections supply all four lower boundaries, including the footrule normalization. -/
theorem exists_lower {b : ℝ} (hb : b ∈ Set.Icc (-1) 1) :
    ∃ C : Copula 2, C.blomqvistBeta = b ∧
      C.spearmanRho = 3 / 16 * (1 + b) ^ 3 - 1 ∧
      C.kendallTau = 1 / 4 * (1 + b) ^ 2 - 1 ∧
      C.spearmanFootrule = 3 / 16 * (1 + b) ^ 2 - 1 / 2 ∧
      C.giniGamma = 3 / 8 * (1 + b) ^ 2 - 1 := by
  obtain ⟨C, h1, h2, h3, h4, h5⟩ := exists_upper (b := -b)
    ⟨by linarith [hb.2], by linarith [hb.1]⟩
  refine ⟨C.reflect {1}, ?_, ?_, ?_, ?_, ?_⟩
  · rw [blomqvistBeta_reflect_second, h1, neg_neg]
  · rw [spearmanRho_reflect_second, h2]; ring
  · rw [kendallTau_reflect_second, h3]; ring
  · have h := C.giniGamma_eq_footrule_sub_reflect
    rw [h4, h5] at h
    nlinarith
  · rw [giniGamma_reflect_second, h5]; ring

theorem rho_iff (b r : ℝ) :
    (∃ C : Copula 2, C.blomqvistBeta = b ∧ C.spearmanRho = r) ↔
      b ∈ Set.Icc (-1) 1 ∧ 3 / 16 * (1 + b) ^ 3 - 1 ≤ r ∧
      r ≤ 1 - 3 / 16 * (1 - b) ^ 3 := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    exact ⟨C.blomqvistBeta_mem_Icc, C.beta_le_spearmanRho, C.spearmanRho_le_beta⟩
  · rintro ⟨hb, hl, hu⟩
    obtain ⟨C, hC, hrC, _⟩ := exists_lower hb
    obtain ⟨D, hD, hrD, _⟩ := exists_upper hb
    exact (mem_attainable_iff .beta .rho b r).mp
      (fixed_coefficient_intermediate .beta .rho (by decide) C D hC hD
        (by simpa only [Coefficient.eval, hrC] using hl)
        (by simpa only [Coefficient.eval, hrD] using hu))

theorem tau_iff (b t : ℝ) :
    (∃ C : Copula 2, C.blomqvistBeta = b ∧ C.kendallTau = t) ↔
      b ∈ Set.Icc (-1) 1 ∧ 1 / 4 * (1 + b) ^ 2 - 1 ≤ t ∧
      t ≤ 1 - 1 / 4 * (1 - b) ^ 2 := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    exact ⟨C.blomqvistBeta_mem_Icc, C.beta_le_kendallTau, C.kendallTau_le_beta⟩
  · rintro ⟨hb, hl, hu⟩
    obtain ⟨C, hC, _, htC, _⟩ := exists_lower hb
    obtain ⟨D, hD, _, htD, _⟩ := exists_upper hb
    exact (mem_attainable_iff .beta .tau b t).mp
      (fixed_coefficient_intermediate .beta .tau (by decide) C D hC hD
        (by simpa only [Coefficient.eval, htC] using hl)
        (by simpa only [Coefficient.eval, htD] using hu))

theorem footrule_iff (b p : ℝ) :
    (∃ C : Copula 2, C.blomqvistBeta = b ∧ C.spearmanFootrule = p) ↔
      b ∈ Set.Icc (-1) 1 ∧ 3 / 16 * (1 + b) ^ 2 - 1 / 2 ≤ p ∧
      p ≤ 1 - 3 / 8 * (1 - b) ^ 2 := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    exact ⟨C.blomqvistBeta_mem_Icc, C.beta_le_spearmanFootrule, C.spearmanFootrule_le_beta⟩
  · rintro ⟨hb, hl, hu⟩
    obtain ⟨C, hC, _, _, hpC, _⟩ := exists_lower hb
    obtain ⟨D, hD, _, _, hpD, _⟩ := exists_upper hb
    exact (mem_attainable_iff .beta .footrule b p).mp
      (fixed_coefficient_intermediate .beta .footrule (by decide) C D hC hD
        (by simpa only [Coefficient.eval, hpC] using hl)
        (by simpa only [Coefficient.eval, hpD] using hu))

theorem gamma_iff (b g : ℝ) :
    (∃ C : Copula 2, C.blomqvistBeta = b ∧ C.giniGamma = g) ↔
      b ∈ Set.Icc (-1) 1 ∧ 3 / 8 * (1 + b) ^ 2 - 1 ≤ g ∧
      g ≤ 1 - 3 / 8 * (1 - b) ^ 2 := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    exact ⟨C.blomqvistBeta_mem_Icc, C.beta_le_giniGamma, C.giniGamma_le_beta⟩
  · rintro ⟨hb, hl, hu⟩
    obtain ⟨C, hC, _, _, _, hgC⟩ := exists_lower hb
    obtain ⟨D, hD, _, _, _, hgD⟩ := exists_upper hb
    exact (mem_attainable_iff .beta .gamma b g).mp
      (fixed_coefficient_intermediate .beta .gamma (by decide) C D hC hD
        (by simpa only [Coefficient.eval, hgC] using hl)
        (by simpa only [Coefficient.eval, hgD] using hu))

end ProbabilityTheory.Copula.RankRegion.Beta
