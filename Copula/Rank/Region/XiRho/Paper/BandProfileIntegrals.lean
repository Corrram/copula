import Copula.Rank.Region.XiRho.Paper.SourceBandMoments
import Copula.Rank.Region.XiRho.Support.ThreePieceIntegrals

/-! # Exact integrals of the diagonal-band moment profiles -/

open MeasureTheory ProbabilityTheory Set ProbabilityTheory.Copula.RankRegion.XiRho.Support
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiRho

theorem bandSquare_pair_integral (b c : ℝ) :
    (∫ v in (0 : ℝ)..c, bandSquareLow b v + bandSquareHigh b v) =
      c - c ^ 2 + 2 / (3 * b) * ∫ v in (0 : ℝ)..c, Real.sqrt (2 * b * v) ^ 3 := by
  have he (v : ℝ) : bandSquareLow b v + bandSquareHigh b v =
      1 - 2 * v + (2 / (3 * b)) * Real.sqrt (2 * b * v) ^ 3 := by
    simp only [bandSquareLow, bandSquareHigh]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_id]
  simp
  ring

theorem bandWeight_pair_integral (b c : ℝ) :
    (∫ v in (0 : ℝ)..c, bandWeightLow b v + bandWeightHigh b v) =
      c / 2 + c ^ 2 / 2 - 1 / (3 * b ^ 2) * ∫ v in (0 : ℝ)..c, Real.sqrt (2 * b * v) ^ 3 := by
  have he (v : ℝ) : bandWeightLow b v + bandWeightHigh b v =
      1 / 2 + v - (1 / (3 * b ^ 2)) * Real.sqrt (2 * b * v) ^ 3 := by
    unfold bandWeightLow bandWeightHigh
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, integral_id]
  simp
  ring

theorem bandSquare_mid_small (b c d : ℝ) (hb : b ≤ 1) :
    (∫ v in c..d, bandSquareMid b v) = (d ^ 3 - c ^ 3) / 3 + b ^ 2 / 12 * (d - c) := by
  simp only [bandSquareMid, ite_eq_left hb]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop), integral_pow]
  norm_num
  ring

theorem bandSquare_mid_large (b c d : ℝ) (hb : ¬b ≤ 1) :
    (∫ v in c..d, bandSquareMid b v) = (d ^ 2 - c ^ 2) / 2 - (d - c) / (6 * b) := by
  simp only [bandSquareMid, ite_eq_right hb]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop), integral_id]
  simp
  ring

theorem bandWeight_mid_small (b c d : ℝ) (hb : b ≤ 1) :
    (∫ v in c..d, bandWeightMid b v) = (d ^ 2 - c ^ 2) / 4 + b / 12 * (d - c) := by
  simp only [bandWeightMid, ite_eq_left hb]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_div, integral_id]
  simp
  ring

theorem bandWeight_mid_large (b c d : ℝ) (hb : ¬b ≤ 1) :
    (∫ v in c..d, bandWeightMid b v) =
      (d ^ 2 - c ^ 2) / 2 - (d ^ 3 - c ^ 3) / 6 - (d - c) / (24 * b ^ 2) := by
  simp only [bandWeightMid, ite_eq_right hb]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_div, integral_id, integral_pow]
  norm_num
  ring

private theorem sqrt_integral_small {b : ℝ} (hb : 0 < b) :
    (∫ v in (0 : ℝ)..(b / 2), Real.sqrt (2 * b * v) ^ 3) = b ^ 4 / 5 := by
  have h := integral_sqrt_scaled_cube hb hb.le
  rw [show b ^ 2 / (2 * b) = b / 2 by field_simp] at h
  rw [h]
  field_simp

private theorem sqrt_integral_large {b : ℝ} (hb : 0 < b) :
    (∫ v in (0 : ℝ)..(1 / (2 * b)), Real.sqrt (2 * b * v) ^ 3) = 1 / (5 * b) := by
  simpa using integral_sqrt_scaled_cube hb (by norm_num : (0 : ℝ) ≤ 1)

theorem sourceBand_square_integral {b : ℝ} (hb : 0 < b) :
    (∫ v : I, clampedSquare b (sourceBandIntercept b v)) =
      if b ≤ 1 then 1 / 3 + b ^ 2 / 12 - b ^ 3 / 30
      else 1 / 2 - 1 / (6 * b) + 1 / (20 * b ^ 2) := by
  simp_rw [sourceBand_square_profile hb]
  have hc := bandCut_mem hb
  have hmid : Continuous (bandSquareMid b) := by
    unfold bandSquareMid
    split_ifs <;> fun_prop
  rw [integral_unit_three_pieces hc.1 hc.2 (bandSquareLow b) (bandSquareMid b) (bandSquareHigh b)
    (by unfold bandSquareLow; fun_prop) hmid (by unfold bandSquareHigh bandSquareLow; fun_prop),
    bandSquare_pair_integral]
  split_ifs with hb1
  · rw [bandSquare_mid_small _ _ _ hb1, bandCut_small hb hb1, sqrt_integral_small hb]
    field_simp
    ring
  · rw [bandSquare_mid_large _ _ _ hb1, bandCut_large hb (by linarith), sqrt_integral_large hb]
    field_simp
    ring

theorem sourceBand_weight_integral {b : ℝ} (hb : 0 < b) :
    (∫ v : I, clampedWeight b (sourceBandIntercept b v)) =
      if b ≤ 1 then 1 / 4 + b / 12 - b ^ 2 / 40
      else 1 / 3 - 1 / (24 * b ^ 2) + 1 / (60 * b ^ 3) := by
  simp_rw [sourceBand_weight_profile hb]
  have hc := bandCut_mem hb
  have hmid : Continuous (bandWeightMid b) := by
    unfold bandWeightMid
    split_ifs <;> fun_prop
  rw [integral_unit_three_pieces hc.1 hc.2 (bandWeightLow b) (bandWeightMid b) (bandWeightHigh b)
    (by unfold bandWeightLow; fun_prop) hmid (by unfold bandWeightHigh; fun_prop),
    bandWeight_pair_integral]
  split_ifs with hb1
  · rw [bandWeight_mid_small _ _ _ hb1, bandCut_small hb hb1, sqrt_integral_small hb]
    field_simp
    ring
  · rw [bandWeight_mid_large _ _ _ hb1, bandCut_large hb (by linarith), sqrt_integral_large hb]
    field_simp
    ring

end ProbabilityTheory.Copula.RankRegion.XiRho
