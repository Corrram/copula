import Copula.Rank.Region.XiRho.Paper.SourceBand
import Copula.Rank.Region.XiRho.Support.ScaledRampMoments

/-! # Exact conditional moment profiles for the source diagonal bands -/

open MeasureTheory ProbabilityTheory Set ProbabilityTheory.Copula.RankRegion.XiRho.Support
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiRho

private theorem lower_bounds {b : ℝ} (hb : 0 < b) (v : I) (hv : (v : ℝ) ≤ bandCut b) :
    0 ≤ Real.sqrt (2 * b * (v : ℝ)) ∧ Real.sqrt (2 * b * (v : ℝ)) ≤ b ∧
      Real.sqrt (2 * b * (v : ℝ)) ≤ 1 := by
  have hvb := hv.trans (min_le_left _ _)
  have hv1 := hv.trans (min_le_right _ _)
  have hv1' := (le_div_iff₀ (by positivity : 0 < 2 * b)).mp hv1
  have hs := Real.sq_sqrt (show 0 ≤ 2 * b * (v : ℝ) from mul_nonneg (by positivity) v.property.1)
  have hn := Real.sqrt_nonneg (2 * b * (v : ℝ))
  exact ⟨hn, by nlinarith, by nlinarith⟩

noncomputable def bandSquareLow (b v : ℝ) : ℝ := Real.sqrt (2 * b * v) ^ 3 / (3 * b)
noncomputable def bandSquareHigh (b v : ℝ) : ℝ := 1 - 2 * v + bandSquareLow b v
noncomputable def bandSquareMid (b v : ℝ) : ℝ := if b ≤ 1 then v ^ 2 + b ^ 2 / 12 else v - 1 / (6 * b)
noncomputable def bandWeightLow (b v : ℝ) : ℝ := v - Real.sqrt (2 * b * v) ^ 3 / (6 * b ^ 2)
noncomputable def bandWeightHigh (b v : ℝ) : ℝ := 1 / 2 - Real.sqrt (2 * b * v) ^ 3 / (6 * b ^ 2)
noncomputable def bandWeightMid (b v : ℝ) : ℝ := if b ≤ 1 then v / 2 + b / 12 else v - v ^ 2 / 2 - 1 / (24 * b ^ 2)

private theorem lower_square {b : ℝ} (hb : 0 < b) (v : I) (hv : (v : ℝ) ≤ bandCut b) :
    clampedSquare b (Real.sqrt (2 * b * (v : ℝ))) = bandSquareLow b v := by
  have h := lower_bounds hb v hv
  exact clampedSquare_lower hb h.1 h.2.1 h.2.2

private theorem lower_weight {b : ℝ} (hb : 0 < b) (v : I) (hv : (v : ℝ) ≤ bandCut b) :
    clampedWeight b (Real.sqrt (2 * b * (v : ℝ))) = bandWeightLow b v := by
  have h := lower_bounds hb v hv
  have hs := Real.sq_sqrt (show 0 ≤ 2 * b * (v : ℝ) from mul_nonneg (by positivity) v.property.1)
  rw [clampedWeight_lower hb h.1 h.2.1 h.2.2, hs]
  unfold bandWeightLow
  field_simp

private theorem lower_mean {b : ℝ} (hb : 0 < b) (v : I) (hv : (v : ℝ) ≤ bandCut b) :
    clampedMean b (Real.sqrt (2 * b * (v : ℝ))) = (v : ℝ) := by
  have h := lower_bounds hb v hv
  have hs := Real.sq_sqrt (show 0 ≤ 2 * b * (v : ℝ) from mul_nonneg (by positivity) v.property.1)
  rw [clampedMean_lower hb h.1 h.2.1 h.2.2, hs]
  field_simp

private theorem middle_large_bounds {b : ℝ} (hb : 0 < b) (hb1 : 1 ≤ b) (v : I)
    (hv : bandCut b ≤ (v : ℝ)) (hw : (v : ℝ) ≤ 1 - bandCut b) :
    1 ≤ b * (v : ℝ) + 1 / 2 ∧ b * (v : ℝ) + 1 / 2 ≤ b := by
  rw [bandCut_large hb hb1] at hv hw
  have hlo := (div_le_iff₀ (by positivity : 0 < 2 * b)).mp hv
  have hhi := (div_le_iff₀ (by positivity : 0 < 2 * b)).mp
    (show 1 / (2 * b) ≤ 1 - (v : ℝ) by linarith)
  constructor <;> nlinarith

/-- The complete second-moment profile, including both transition points. -/
theorem sourceBand_square_profile {b : ℝ} (hb : 0 < b) (v : I) :
    clampedSquare b (sourceBandIntercept b v) =
      if (v : ℝ) ≤ bandCut b then bandSquareLow b v
      else if (v : ℝ) ≤ 1 - bandCut b then bandSquareMid b v
      else bandSquareHigh b (1 - (v : ℝ)) := by
  unfold sourceBandIntercept
  split_ifs with hv hw hb1
  · exact lower_square hb v hv
  · unfold bandSquareMid
    rw [ite_eq_left hb1]
    have hcut := bandCut_small hb hb1
    rw [hcut] at hv hw
    rw [clampedSquare_affine hb.le (by linarith) (by linarith)]
    ring
  · unfold bandSquareMid
    rw [ite_eq_right hb1]
    have h := middle_large_bounds hb (by linarith) v (by linarith) hw
    rw [clampedSquare_saturated hb h.1 h.2]
    field_simp
    ring
  · have hv' : ((unitInterval.symm v : I) : ℝ) ≤ bandCut b := by
      change 1 - (v : ℝ) ≤ bandCut b; linarith
    rw [clampedSquare_complement]
    have hm := lower_mean hb (unitInterval.symm v) hv'
    have hs := lower_square hb (unitInterval.symm v) hv'
    change clampedMean b (Real.sqrt (2 * b * (1 - (v : ℝ)))) = 1 - (v : ℝ) at hm
    change clampedSquare b (Real.sqrt (2 * b * (1 - (v : ℝ)))) = bandSquareLow b (1 - (v : ℝ)) at hs
    rw [hm, hs]
    rfl

/-- The complete weighted first-moment profile for Spearman rho. -/
theorem sourceBand_weight_profile {b : ℝ} (hb : 0 < b) (v : I) :
    clampedWeight b (sourceBandIntercept b v) =
      if (v : ℝ) ≤ bandCut b then bandWeightLow b v
      else if (v : ℝ) ≤ 1 - bandCut b then bandWeightMid b v
      else bandWeightHigh b (1 - (v : ℝ)) := by
  unfold sourceBandIntercept
  split_ifs with hv hw hb1
  · exact lower_weight hb v hv
  · unfold bandWeightMid
    rw [ite_eq_left hb1]
    have hcut := bandCut_small hb hb1
    rw [hcut] at hv hw
    rw [clampedWeight_affine hb.le (by linarith) (by linarith)]
    ring
  · unfold bandWeightMid
    rw [ite_eq_right hb1]
    have h := middle_large_bounds hb (by linarith) v (by linarith) hw
    rw [clampedWeight_saturated hb h.1 h.2]
    field_simp
    ring
  · have hv' : ((unitInterval.symm v : I) : ℝ) ≤ bandCut b := by
      change 1 - (v : ℝ) ≤ bandCut b; linarith
    rw [clampedWeight_complement]
    have hm := lower_mean hb (unitInterval.symm v) hv'
    have hs := lower_weight hb (unitInterval.symm v) hv'
    change clampedMean b (Real.sqrt (2 * b * (1 - (v : ℝ)))) = 1 - (v : ℝ) at hm
    change clampedWeight b (Real.sqrt (2 * b * (1 - (v : ℝ)))) = bandWeightLow b (1 - (v : ℝ)) at hs
    rw [hm, hs]
    unfold bandWeightLow bandWeightHigh
    ring

theorem sourceBand_xi_integral (b : ℝ) (hb : 0 < b) :
    (sourceBand b hb).chatterjeeXi = 6 * (∫ v : I, clampedSquare b (sourceBandIntercept b v)) - 2 := by
  unfold Copula.chatterjeeXi
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => integral_congr_ae
    ((sourceBand_conditionalCDF b hb v).fun_comp (fun r : ℝ => r ^ 2))

theorem sourceBand_rho_integral (b : ℝ) (hb : 0 < b) :
    (sourceBand b hb).spearmanRho = 12 * (∫ v : I, clampedWeight b (sourceBandIntercept b v)) - 3 := by
  rw [rho_conditional_formula]
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => integral_congr_ae (by
    filter_upwards [sourceBand_conditionalCDF b hb v] with u hu
    rw [hu])

end ProbabilityTheory.Copula.RankRegion.XiRho
