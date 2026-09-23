import Copula.Rank.Region.TauFootruleBeta.Paper.FootruleBetaLower
import Copula.Rank.Region.TauFootruleBeta.Support.TauFootrule
import Copula.Rank.MedianExtrema

/-! # Proposition 2.1 and Corollary 4.2: both remaining pairwise regions

All witnesses are constructed copulas. The tau-beta projection is proved
directly, without assuming the still separate three-dimensional theorem.
-/

open ProbabilityTheory Set ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.TauFootruleBeta

theorem tau_footrule_bounds (C : Copula 2) :
    4 / 3 * C.spearmanFootrule - 1 / 3 ≤ C.kendallTau ∧
      C.kendallTau ≤ 2 / 3 * C.spearmanFootrule + 1 / 3 :=
  ⟨tau_footrule_lower C, tau_footrule_upper C⟩

theorem tau_beta_bounds (C : Copula 2) :
    (1 + C.blomqvistBeta) ^ 2 / 4 - 1 ≤ C.kendallTau ∧
      C.kendallTau ≤ 1 - (1 - C.blomqvistBeta) ^ 2 / 4 := by
  have h := tau_footrule_bounds C
  have hL := beta_lower_le_footrule C
  have hU := footrule_le_beta_upper C
  constructor <;> linarith

theorem exact_tau_beta_region (t b : ℝ) :
    (∃ C : Copula 2, C.kendallTau = t ∧ C.blomqvistBeta = b) ↔
      b ∈ Icc (-1) 1 ∧ (1 + b) ^ 2 / 4 - 1 ≤ t ∧ t ≤ 1 - (1 - b) ^ 2 / 4 := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    exact ⟨C.blomqvistBeta_mem_Icc, tau_beta_bounds C⟩
  · rintro ⟨hb, htL, htU⟩
    let hn : -b ∈ Icc (-1) 1 := by constructor <;> linarith [hb.1, hb.2]
    let D := (footruleBetaLower (-b) hn).reflect {1}
    have hdτ : D.kendallTau = 1 - (1 - b) ^ 2 / 4 := by
      dsimp only [D]
      rw [Copula.kendallTau_reflect_second, (footruleBetaLower_coefficients (-b) hn).1]
      ring
    have hdβ : D.blomqvistBeta = b := by
      dsimp only [D]
      rw [Copula.blomqvistBeta_reflect_second, (footruleBetaLower_coefficients (-b) hn).2.2]
      ring
    obtain ⟨a, ha⟩ := exists_unitInterval_eq (continuous_tau_mix D (footruleBetaLower b hb))
      (by simpa only [Copula.mix_zero, (footruleBetaLower_coefficients b hb).1] using htL)
      (by simpa only [Copula.mix_one, hdτ] using htU)
    refine ⟨D.mix (footruleBetaLower b hb) a, ha, ?_⟩
    rw [Copula.blomqvistBeta_mix, hdβ, (footruleBetaLower_coefficients b hb).2.2]
    ring

theorem upperTauSeed_coefficients :
    (medianWBlocks.reflect {1}).kendallTau = 0 ∧
      (medianWBlocks.reflect {1}).spearmanFootrule = -1 / 2 ∧
      (medianWBlocks.reflect {1}).blomqvistBeta = -1 := by
  constructor
  · norm_num [medianWBlocks, Copula.kendallTau_reflect_second,
      Copula.kendallTau_ordinalSum, Copula.unitHalf]
  constructor
  · exact Copula.spearmanFootrule_reflect_ordinalSum_half _ _
  · rw [Copula.blomqvistBeta_reflect_second, Copula.blomqvistBeta,
      medianWBlocks, Copula.cdf_ordinalSum_split]
    norm_num [Copula.unitHalf]

theorem centered_tau_endpoints (α : I) :
    let C := ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal Copula.countermonotonic α
    let D := ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal (medianWBlocks.reflect {1}) α
    C.spearmanFootrule = 1 - 3 / 2 * (α : ℝ) ^ 2 ∧
    D.spearmanFootrule = 1 - 3 / 2 * (α : ℝ) ^ 2 ∧
    C.kendallTau = 1 - 2 * (α : ℝ) ^ 2 ∧
    D.kendallTau = 1 - (α : ℝ) ^ 2 ∧
    C.blomqvistBeta = 1 - 2 * (α : ℝ) ∧ D.blomqvistBeta = 1 - 2 * (α : ℝ) := by
  dsimp only
  simp only [ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_footrule, ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_tau,
    ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_beta, Copula.spearmanFootrule_countermonotonic,
    Copula.kendallTau_countermonotonic, Copula.blomqvistBeta_countermonotonic,
    upperTauSeed_coefficients.1, upperTauSeed_coefficients.2.1, upperTauSeed_coefficients.2.2]
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem exact_tau_footrule_region (t p : ℝ) :
    (∃ C : Copula 2, C.kendallTau = t ∧ C.spearmanFootrule = p) ↔
      p ∈ Icc (-1 / 2) 1 ∧ 4 / 3 * p - 1 / 3 ≤ t ∧ t ≤ 2 / 3 * p + 1 / 3 := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    exact ⟨C.spearmanFootrule_mem_Icc, tau_footrule_bounds C⟩
  · rintro ⟨hp, htL, htU⟩
    obtain ⟨α, hα⟩ := exists_unitInterval_eq
      (f := fun α : I => 3 / 2 * (α : ℝ) ^ 2 - 1) (by fun_prop)
      (z := -p) (by norm_num; linarith [hp.2]) (by norm_num; linarith [hp.1])
    let C := ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal Copula.countermonotonic α
    let D := ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal (medianWBlocks.reflect {1}) α
    obtain ⟨hcφ, hdφ, hcτ, hdτ, _, _⟩ := centered_tau_endpoints α
    have hc : C.spearmanFootrule = p := by dsimp only [C]; linarith
    have hd : D.spearmanFootrule = p := by dsimp only [D]; linarith
    obtain ⟨a, ha⟩ := exists_unitInterval_eq (z := t) (continuous_tau_mix D C)
      (by rw [Copula.mix_zero]; dsimp only [C]; linarith)
      (by rw [Copula.mix_one]; dsimp only [D]; linarith)
    refine ⟨D.mix C a, ha, ?_⟩
    rw [Copula.spearmanFootrule_mix, hd, hc]
    ring

end ProbabilityTheory.Copula.RankRegion.TauFootruleBeta
