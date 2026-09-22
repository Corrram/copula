import Copula.Rank.Region.XiRho.Paper.BandProfileIntegrals

/-! # Proposition 5(i)--(ii): exact xi and rho for every positive diagonal band -/

open ProbabilityTheory ProbabilityTheory.Copula.RankRegion.XiRho.Support

namespace ProbabilityTheory.Copula.RankRegion.XiRho

noncomputable def bandXi (b : ℝ) : ℝ :=
  if b ≤ 1 then b ^ 2 / 2 - b ^ 3 / 5 else 1 - 1 / b + 3 / (10 * b ^ 2)

noncomputable def bandRho (b : ℝ) : ℝ :=
  if b ≤ 1 then b - 3 * b ^ 2 / 10 else 1 - 1 / (2 * b ^ 2) + 1 / (5 * b ^ 3)

/-- Proposition 5(i): the exact Chatterjee coefficient throughout b>0. -/
theorem sourceBand_xi (b : ℝ) (hb : 0 < b) : (sourceBand b hb).chatterjeeXi = bandXi b := by
  rw [sourceBand_xi_integral, sourceBand_square_integral hb]
  unfold bandXi
  split_ifs <;> ring

/-- Proposition 5(ii): the exact Spearman coefficient throughout b>0. -/
theorem sourceBand_rho (b : ℝ) (hb : 0 < b) : (sourceBand b hb).spearmanRho = bandRho b := by
  rw [sourceBand_rho_integral, sourceBand_weight_integral hb]
  unfold bandRho
  split_ifs <;> ring

/-- The normalization-defined optimizer has exactly the source coordinates, including b=0. -/
theorem normalizedBand_coefficients (b : ℝ) (hb : 0 ≤ b) :
    (normalizedBand b hb).chatterjeeXi = bandXi b ∧ (normalizedBand b hb).spearmanRho = bandRho b := by
  rcases eq_or_lt_of_le hb with rfl | hb'
  · rw [normalizedBand_zero]
    norm_num [bandXi, bandRho, Copula.chatterjeeXi_independence, Copula.spearmanRho_independence]
  · rw [← sourceBand_eq_normalizedBand b hb']
    exact ⟨sourceBand_xi b hb', sourceBand_rho b hb'⟩

/-- The exact support bound expressed solely in the closed coefficient formulas. -/
theorem explicit_band_support (C : Copula 2) (b : ℝ) (hb : 0 ≤ b) :
    b * C.spearmanRho - C.chatterjeeXi ≤ b * bandRho b - bandXi b := by
  have h := normalizedBand_support C b hb
  rwa [(normalizedBand_coefficients b hb).1, (normalizedBand_coefficients b hb).2] at h

end ProbabilityTheory.Copula.RankRegion.XiRho
