import Copula.Rank.Region.TauFootruleBeta.Paper.PairwiseRegions

/-! # The necessary joint bounds and the entire lower tau face

At every admissible (footrule,beta) pair, a centered lower seed attains the
lower tau bound simultaneously. The upper tau face is a separate obligation.
-/

open ProbabilityTheory Set ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.TauFootruleBeta

theorem joint_region_outer_bound (C : Copula 2) :
    C.blomqvistBeta ∈ Icc (-1) 1 ∧
      3 / 16 * (1 + C.blomqvistBeta) ^ 2 - 1 / 2 ≤ C.spearmanFootrule ∧
      C.spearmanFootrule ≤ 1 - 3 / 8 * (1 - C.blomqvistBeta) ^ 2 ∧
      4 / 3 * C.spearmanFootrule - 1 / 3 ≤ C.kendallTau ∧
      C.kendallTau ≤ 2 / 3 * C.spearmanFootrule + 1 / 3 :=
  ⟨C.blomqvistBeta_mem_Icc, beta_lower_le_footrule C,
    footrule_le_beta_upper C, tau_footrule_bounds C⟩

theorem lower_joint_face_attained (p b : ℝ) (hb : b ∈ Icc (-1) 1)
    (hpL : 3 / 16 * (1 + b) ^ 2 - 1 / 2 ≤ p)
    (hpU : p ≤ 1 - 3 / 8 * (1 - b) ^ 2) :
    ∃ C : Copula 2, C.spearmanFootrule = p ∧ C.blomqvistBeta = b ∧
      C.kendallTau = 4 / 3 * p - 1 / 3 := by
  by_cases hb1 : b = 1
  · subst b
    have hp : p ∈ Icc (1 / 4) 1 := by constructor <;> norm_num at * <;> linarith
    have ht : medianWBlocks.kendallTau = 0 := by
      norm_num [medianWBlocks, Copula.kendallTau_ordinalSum, Copula.unitHalf]
    have hφ : medianWBlocks.spearmanFootrule = 1 / 4 := by
      norm_num [medianWBlocks, Copula.spearmanFootrule_ordinalSum, Copula.unitHalf]
    have hβ : medianWBlocks.blomqvistBeta = 1 := by
      rw [Copula.blomqvistBeta, medianWBlocks, Copula.cdf_ordinalSum_split]
      norm_num [Copula.unitHalf]
    -- Here the central width is chosen with the decreasing footrule path.
    obtain ⟨a, ha⟩ := exists_unitInterval_eq
      (f := fun a : I => -((1 : ℝ) - 3 / 4 * (a : ℝ) ^ 2)) (by fun_prop)
      (z := -p) (by simpa using neg_le_neg hp.2) (by norm_num; linarith [hp.1])
    refine ⟨ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal medianWBlocks a, ?_, ?_, ?_⟩
    · rw [ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_footrule, hφ]
      linarith
    · rw [ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_beta, hβ]
      ring
    · rw [ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_tau, ht]
      linarith
  have hk : 0 < 1 - b := sub_pos.mpr (lt_of_le_of_ne hb.2 hb1)
  let k := 1 - b
  let F : ℝ → ℝ := fun a => 1 - 3 / 4 * a ^ 2 - 3 / 4 * k * a + 3 / 16 * k ^ 2
  let A : I → ℝ := fun t => k / 2 + (1 - k / 2) * (t : ℝ)
  have hA (t : I) : k / 2 ≤ A t ∧ A t ≤ 1 := by
    have hk2 : k ≤ 2 := by dsimp [k]; linarith [hb.1]
    have h0 := mul_nonneg (by linarith : 0 ≤ 1 - k / 2) t.property.1
    have h1 := mul_le_mul_of_nonneg_left t.property.2 (by linarith : 0 ≤ 1 - k / 2)
    dsimp [A]
    constructor <;> linarith
  obtain ⟨a, ha⟩ := exists_unitInterval_eq (f := fun a : I => -F (A a))
    (by dsimp [F, A]; fun_prop) (z := -p)
    (by dsimp [F, A, k]; norm_num; nlinarith [hpU])
    (by dsimp [F, A, k]; norm_num; nlinarith [hpL])
  let α : I := ⟨A a, ⟨by have := (hA a).1; dsimp [k] at *; linarith, (hA a).2⟩⟩
  have hαpos : 0 < (α : ℝ) := by have := (hA a).1; dsimp [α, k] at *; linarith
  have hαk : k ≤ 2 * (α : ℝ) := by have := (hA a).1; dsimp [α]; linarith
  let x := 1 - k / (α : ℝ)
  have hx : x ∈ Icc (-1) 1 := by
    dsimp [x]
    constructor
    · have hd : k / (α : ℝ) ≤ 2 := (div_le_iff₀ hαpos).mpr hαk
      linarith
    · have hd : 0 ≤ k / (α : ℝ) := div_nonneg (by dsimp [k]; linarith) hαpos.le
      linarith
  have hprod : (α : ℝ) * x = (α : ℝ) - k := by
    dsimp [x]
    field_simp [ne_of_gt hαpos]
  obtain ⟨ht, hφ, hβ⟩ := footruleBetaLower_coefficients x hx
  have hF : F α = p := by change -F (α : ℝ) = -p at ha; linarith
  refine ⟨ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal (footruleBetaLower x hx) α, ?_, ?_, ?_⟩
  · rw [ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_footrule, hφ]
    calc
      _ = 1 - 3 / 2 * (α : ℝ) ^ 2 + 3 / 16 * ((α : ℝ) + (α : ℝ) * x) ^ 2 := by ring
      _ = p := by rw [hprod, ← hF]; dsimp [F]; ring
  · rw [ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_beta, hβ, hprod]
    dsimp [k]
    ring
  · rw [ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_tau, ht]
    calc
      _ = 1 - 2 * (α : ℝ) ^ 2 + ((α : ℝ) + (α : ℝ) * x) ^ 2 / 4 := by ring
      _ = 4 / 3 * p - 1 / 3 := by rw [hprod, ← hF]; dsimp [F]; ring

end ProbabilityTheory.Copula.RankRegion.TauFootruleBeta
