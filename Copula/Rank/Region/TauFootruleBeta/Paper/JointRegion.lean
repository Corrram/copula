import Copula.Rank.Region.TauFootruleBeta.Paper.UpperSeed
import Copula.Rank.Region.TauFootruleBeta.Paper.Mixtures

/-! # Theorem 1.1: the exact joint region, with actual attaining copulas -/

open ProbabilityTheory Set ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.TauFootruleBeta

noncomputable def footruleBetaUpperTau (b : ℝ) (hb : b ∈ Icc (-1) 1) : Copula 2 :=
  upperSeed ((1 + b) / 8) ⟨by linarith [hb.1], by linarith [hb.2]⟩

theorem footruleBetaUpperTau_coefficients (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (footruleBetaUpperTau b hb).kendallTau = (1 + b) ^ 2 / 8 ∧
      (footruleBetaUpperTau b hb).spearmanFootrule = 3 / 16 * (1 + b) ^ 2 - 1 / 2 ∧
      (footruleBetaUpperTau b hb).blomqvistBeta = b := by
  obtain ⟨ht, hp, hb'⟩ := upperSeed_coefficients ((1 + b) / 8)
    (show (1 + b) / 8 ∈ Icc 0 (1 / 4) from ⟨by linarith [hb.1], by linarith [hb.2]⟩)
  change (upperSeed ((1 + b) / 8) _).kendallTau = _ ∧
    (upperSeed ((1 + b) / 8) _).spearmanFootrule = _ ∧
    (upperSeed ((1 + b) / 8) _).blomqvistBeta = _
  rw [ht, hp, hb']
  constructor
  · ring
  constructor <;> ring

theorem upper_joint_face_attained (p b : ℝ) (hb : b ∈ Icc (-1) 1)
    (hpL : 3 / 16 * (1 + b) ^ 2 - 1 / 2 ≤ p)
    (hpU : p ≤ 1 - 3 / 8 * (1 - b) ^ 2) :
    ∃ C : Copula 2, C.spearmanFootrule = p ∧ C.blomqvistBeta = b ∧
      C.kendallTau = 2 / 3 * p + 1 / 3 := by
  by_cases hb1 : b = 1
  · subst b
    have hp : p ∈ Icc (1 / 4) 1 := by constructor <;> norm_num at * <;> linarith
    let D := upperSeed (1 / 4) (by constructor <;> norm_num)
    have hD := upperSeed_coefficients (1 / 4) (by constructor <;> norm_num)
    norm_num at hD
    have ht : D.kendallTau = 1 / 2 := hD.1
    have hφ : D.spearmanFootrule = 1 / 4 := hD.2.1
    have hβ : D.blomqvistBeta = 1 := hD.2.2
    -- Here the central width is chosen with the decreasing footrule path.
    obtain ⟨a, ha⟩ := exists_unitInterval_eq
      (f := fun a : I => -((1 : ℝ) - 3 / 4 * (a : ℝ) ^ 2)) (by fun_prop)
      (z := -p) (by simpa using neg_le_neg hp.2) (by norm_num; linarith [hp.1])
    refine ⟨ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal D a, ?_, ?_, ?_⟩
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
  obtain ⟨ht, hφ, hβ⟩ := footruleBetaUpperTau_coefficients x hx
  have hF : F α = p := by change -F (α : ℝ) = -p at ha; linarith
  refine ⟨ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal (footruleBetaUpperTau x hx) α, ?_, ?_, ?_⟩
  · rw [ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_footrule, hφ]
    calc
      _ = 1 - 3 / 2 * (α : ℝ) ^ 2 + 3 / 16 * ((α : ℝ) + (α : ℝ) * x) ^ 2 := by ring
      _ = p := by rw [hprod, ← hF]; dsimp [F]; ring
  · rw [ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_beta, hβ, hprod]
    dsimp [k]
    ring
  · rw [ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_tau, ht]
    calc
      _ = 1 - (α : ℝ) ^ 2 + ((α : ℝ) + (α : ℝ) * x) ^ 2 / 8 := by ring
      _ = 2 / 3 * p + 1 / 3 := by rw [hprod, ← hF]; dsimp [F]; ring

theorem exact_joint_region (t p b : ℝ) :
    (∃ C : Copula 2, C.kendallTau = t ∧ C.spearmanFootrule = p ∧ C.blomqvistBeta = b) ↔
      b ∈ Icc (-1) 1 ∧ 3 / 16 * (1 + b) ^ 2 - 1 / 2 ≤ p ∧
      p ≤ 1 - 3 / 8 * (1 - b) ^ 2 ∧
      4 / 3 * p - 1 / 3 ≤ t ∧ t ≤ 2 / 3 * p + 1 / 3 := by
  constructor
  · rintro ⟨C, rfl, rfl, rfl⟩
    exact joint_region_outer_bound C
  · rintro ⟨hb, hpL, hpU, htL, htU⟩
    obtain ⟨C, hCp, hCb, hCt⟩ := lower_joint_face_attained p b hb hpL hpU
    obtain ⟨D, hDp, hDb, hDt⟩ := upper_joint_face_attained p b hb hpL hpU
    obtain ⟨E, hEp, hEb, hEt⟩ := fixed_footrule_beta_intermediate C D (t := t) hCp hDp hCb hDb
      (by linarith) (by linarith)
    exact ⟨E, hEt, hEp, hEb⟩

end ProbabilityTheory.Copula.RankRegion.TauFootruleBeta
