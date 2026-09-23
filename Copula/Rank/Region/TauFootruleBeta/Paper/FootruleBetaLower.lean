import Copula.Rank.Region.TauFootruleBeta.Paper.FootruleBeta
import Copula.Rank.Region.TauFootruleBeta.Support.CenteredMoments
import Copula.Rank.Region.TauFootruleBeta.Support.TentArea
import Copula.Rank.Region.TauFootruleBeta.Support.Mixture

/-! # The lower footrule-beta boundary and the complete pairwise region

The lower seed of Proposition 3.2 is constructed by reflection of a centered
ordinal sum. No shuffle formula or assumed coefficient values are required.
-/

open MeasureTheory ProbabilityTheory Set ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.TauFootruleBeta

theorem diagonal_beta_lower (C : Copula 2) (t : I) :
    Copula.countermonotonic.cdf ![t, t] +
      2 * medianTent ((C.blomqvistBeta + 1) / 4) t ≤ C.cdf ![t, t] := by
  have hm : C.cdf ![Copula.unitHalf, Copula.unitHalf] = (C.blomqvistBeta + 1) / 4 := by
    rw [Copula.blomqvistBeta]
    ring
  have h0 := C.cdf_nonneg ![t, t]
  have hw := Copula.cdf_countermonotonic_le C ![t, t]
  rw [Copula.cdf_countermonotonic] at hw ⊢
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hw ⊢
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · have h := C.cdf_sub_le_sum_abs ![Copula.unitHalf, Copula.unitHalf] ![t, t]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hm] at h
    change (C.blomqvistBeta + 1) / 4 - C.cdf ![t, t] ≤
      |1 / 2 - (t : ℝ)| + |1 / 2 - (t : ℝ)| at h
    rw [abs_of_nonneg (by linarith)] at h
    rw [max_eq_left (by linarith), medianTent, abs_of_nonpos (by linarith)]
    simp only [max_def]
    split_ifs <;> linarith
  · have h := C.monotone_cdf (show ![Copula.unitHalf, Copula.unitHalf] ≤ ![t, t] from by
        intro i; fin_cases i <;> change (1 / 2 : ℝ) ≤ t <;> linarith)
    rw [hm] at h
    rw [max_eq_right (by linarith), medianTent, abs_of_nonneg (by linarith)]
    rw [max_eq_right (by linarith)] at hw
    simp only [max_def]
    split_ifs <;> linarith

theorem beta_lower_le_footrule (C : Copula 2) :
    3 / 16 * (1 + C.blomqvistBeta) ^ 2 - 1 / 2 ≤ C.spearmanFootrule := by
  have hi := integral_mono
    (Copula.countermonotonic.integrable_diagonal_cdf.add
      ((Copula.integrable_continuous_unit volume (by
        exact (continuous_medianTent _).comp continuous_subtype_val)).const_mul 2))
    C.integrable_diagonal_cdf (diagonal_beta_lower C)
  simp only [Pi.add_apply] at hi
  rw [integral_add, integral_const_mul,
    integral_medianTent (by linarith [C.blomqvistBeta_mem_Icc.1])
      (by linarith [C.blomqvistBeta_mem_Icc.2])] at hi
  · have hw := Copula.spearmanFootrule_countermonotonic
    rw [Copula.spearmanFootrule] at hw ⊢
    nlinarith
  · exact Copula.countermonotonic.integrable_diagonal_cdf
  · exact (Copula.integrable_continuous_unit volume
      ((continuous_medianTent _).comp continuous_subtype_val)).const_mul 2

noncomputable def medianWBlocks : Copula 2 :=
  Copula.countermonotonic.ordinalSum Copula.countermonotonic Copula.unitHalf

noncomputable def lowerSeed (α : I) : Copula 2 :=
  (ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal (medianWBlocks.reflect {1}) α).reflect {1}

theorem lowerSeed_coefficients (α : I) :
    (lowerSeed α).kendallTau = (α : ℝ) ^ 2 - 1 ∧
    (lowerSeed α).spearmanFootrule = 3 / 4 * (α : ℝ) ^ 2 - 1 / 2 ∧
    (lowerSeed α).blomqvistBeta = 2 * (α : ℝ) - 1 := by
  have ht : medianWBlocks.kendallTau = 0 := by
    norm_num [medianWBlocks, Copula.kendallTau_ordinalSum, Copula.unitHalf]
  have hp : medianWBlocks.spearmanFootrule = 1 / 4 := by
    norm_num [medianWBlocks, Copula.spearmanFootrule_ordinalSum, Copula.unitHalf]
  have hb : medianWBlocks.blomqvistBeta = 1 := by
    rw [Copula.blomqvistBeta, medianWBlocks, Copula.cdf_ordinalSum_split]
    norm_num [Copula.unitHalf]
  simp only [lowerSeed, Copula.kendallTau_reflect_second, ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_tau,
    Copula.kendallTau_reflect_second, ht, centeredOrdinal_reflect_footrule,
    Copula.reflect_reflect, hp, Copula.blomqvistBeta_reflect_second,
    ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_beta, Copula.blomqvistBeta_reflect_second, hb]
  constructor
  · ring
  constructor <;> ring

noncomputable def footruleBetaLower (b : ℝ) (hb : b ∈ Icc (-1) 1) : Copula 2 :=
  lowerSeed ⟨(1 + b) / 2, by constructor <;> linarith [hb.1, hb.2]⟩

theorem footruleBetaLower_coefficients (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (footruleBetaLower b hb).kendallTau = (1 + b) ^ 2 / 4 - 1 ∧
    (footruleBetaLower b hb).spearmanFootrule = 3 / 16 * (1 + b) ^ 2 - 1 / 2 ∧
    (footruleBetaLower b hb).blomqvistBeta = b := by
  obtain ⟨ht, hp, hb'⟩ := lowerSeed_coefficients
    ⟨(1 + b) / 2, by constructor <;> linarith [hb.1, hb.2]⟩
  dsimp only at ht hp hb'
  unfold footruleBetaLower
  rw [ht, hp, hb']
  constructor
  · ring
  constructor <;> ring

theorem minimal_footrule_at_beta (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    ∃ D : Copula 2, D.blomqvistBeta = b ∧
      D.spearmanFootrule = 3 / 16 * (1 + b) ^ 2 - 1 / 2 ∧
      ∀ C : Copula 2, C.blomqvistBeta = b → D.spearmanFootrule ≤ C.spearmanFootrule := by
  obtain ⟨_, hp, hb'⟩ := footruleBetaLower_coefficients b hb
  refine ⟨footruleBetaLower b hb, hb', hp, ?_⟩
  intro C hC
  rw [hp]
  simpa only [hC] using beta_lower_le_footrule C

theorem exact_footrule_beta_region (p b : ℝ) :
    (∃ C : Copula 2, C.spearmanFootrule = p ∧ C.blomqvistBeta = b) ↔
      b ∈ Icc (-1) 1 ∧
      3 / 16 * (1 + b) ^ 2 - 1 / 2 ≤ p ∧ p ≤ 1 - 3 / 8 * (1 - b) ^ 2 := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    exact ⟨C.blomqvistBeta_mem_Icc, beta_lower_le_footrule C, footrule_le_beta_upper C⟩
  · rintro ⟨hb, hlo, hup⟩
    obtain ⟨a, ha⟩ := exists_unitInterval_eq
      (f := fun a : I => ((footruleBetaUpper b hb).mix (footruleBetaLower b hb) a).spearmanFootrule)
      (by simp_rw [Copula.spearmanFootrule_mix]; fun_prop)
      (by simpa only [Copula.mix_zero, (footruleBetaLower_coefficients b hb).2.1] using hlo)
      (by simpa only [Copula.mix_one, footruleBetaUpper_footrule] using hup)
    refine ⟨(footruleBetaUpper b hb).mix (footruleBetaLower b hb) a, ha, ?_⟩
    rw [Copula.blomqvistBeta_mix, footruleBetaUpper_beta,
      (footruleBetaLower_coefficients b hb).2.2]
    ring

end ProbabilityTheory.Copula.RankRegion.TauFootruleBeta
