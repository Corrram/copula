import Copula.Rank.Region.TauFootruleBeta.Paper.CenteredOrdinal
import Copula.Rank.Region.TauFootruleBeta.Support.CenteredProperties

/-! # Proposition 2.1: the sharp upper footrule-beta boundary

The diagonal is bounded pointwise by that of a centered W block. Integrating
this comparison proves the bound for all copulas, including singular ones.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.TauFootruleBeta

theorem diagonal_le_centralW (C : Copula 2) (α : I)
    (hβ : C.blomqvistBeta = 1 - 2 * (α : ℝ)) (t : I) :
    C.cdf ![t, t] ≤ (ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centralW α).cdf ![t, t] := by
  have hm : C.cdf ![Copula.unitHalf, Copula.unitHalf] = ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centralMargin α := by
    unfold Copula.blomqvistBeta at hβ
    dsimp [ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centralMargin]
    linarith
  rw [ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centralW_cdf_ordered α t t le_rfl]
  split_ifs
  · exact C.cdf_le_coord _ 0
  · by_cases ht : t ≤ Copula.unitHalf
    · have h := C.monotone_cdf (show ![t, t] ≤ ![Copula.unitHalf, Copula.unitHalf] from by
        intro i; fin_cases i <;> exact ht)
      rw [hm] at h
      have ht' : (t : ℝ) ≤ 1 / 2 := ht
      rw [max_eq_left (by linarith), add_zero]
      exact h
    · have ht' : (1 / 2 : ℝ) ≤ t := le_of_lt (lt_of_not_ge ht)
      have h := C.cdf_sub_le_sum_abs ![t, t] ![Copula.unitHalf, Copula.unitHalf]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hm] at h
      change C.cdf ![t, t] - (ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centralMargin α : ℝ) ≤
        |(t : ℝ) - 1 / 2| + |(t : ℝ) - 1 / 2| at h
      rw [abs_of_nonneg (by linarith)] at h
      rw [max_eq_right (by linarith)]
      linarith

noncomputable def footruleBetaUpper (b : ℝ) (hb : b ∈ Icc (-1) 1) : Copula 2 :=
  ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centralW ⟨(1 - b) / 2, by constructor <;> linarith [hb.1, hb.2]⟩

theorem footruleBetaUpper_beta (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (footruleBetaUpper b hb).blomqvistBeta = b := by
  rw [footruleBetaUpper, ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centralW_beta]
  dsimp
  ring

theorem footruleBetaUpper_footrule (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (footruleBetaUpper b hb).spearmanFootrule = 1 - 3 / 8 * (1 - b) ^ 2 := by
  rw [footruleBetaUpper, ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centralW, ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centeredOrdinal_footrule,
    Copula.spearmanFootrule_countermonotonic]
  dsimp
  ring

theorem footrule_le_beta_upper (C : Copula 2) :
    C.spearmanFootrule ≤ 1 - 3 / 8 * (1 - C.blomqvistBeta) ^ 2 := by
  let b := C.blomqvistBeta
  let α : I := ⟨(1 - b) / 2, by constructor <;> linarith [C.blomqvistBeta_mem_Icc.1,
    C.blomqvistBeta_mem_Icc.2]⟩
  have hd := diagonal_le_centralW C α (by dsimp [α, b]; ring)
  have hi := integral_mono C.integrable_diagonal_cdf
    (ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centralW α).integrable_diagonal_cdf hd
  have hp : C.spearmanFootrule ≤ (footruleBetaUpper b C.blomqvistBeta_mem_Icc).spearmanFootrule := by
    unfold Copula.spearmanFootrule
    change 6 * (∫ t : I, C.cdf ![t, t]) - 2 ≤
      6 * (∫ t : I, (ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support.centralW α).cdf ![t, t]) - 2
    linarith
  simpa only [footruleBetaUpper_footrule] using hp

/-- The upper inequality in equation (8) is attained at every admissible beta. -/
theorem maximal_footrule_at_beta (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    ∃ D : Copula 2, D.blomqvistBeta = b ∧ D.spearmanFootrule = 1 - 3 / 8 * (1 - b) ^ 2 ∧
      ∀ C : Copula 2, C.blomqvistBeta = b → C.spearmanFootrule ≤ D.spearmanFootrule := by
  refine ⟨footruleBetaUpper b hb, footruleBetaUpper_beta b hb, footruleBetaUpper_footrule b hb, ?_⟩
  intro C hC
  rw [footruleBetaUpper_footrule]
  simpa only [hC] using footrule_le_beta_upper C

end ProbabilityTheory.Copula.RankRegion.TauFootruleBeta
