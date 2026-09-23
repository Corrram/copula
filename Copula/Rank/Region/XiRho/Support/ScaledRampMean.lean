import Copula.Rank.Region.XiRho.Support.DiagonalBand
import Copula.Rank.Region.XiRho.Support.RampIntegrals

/-! # Exact marginal means of scaled clamped affine sections -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

theorem unitClamp_positive_parts (x : ℝ) : unitClamp x = max 0 x - max 0 (x - 1) := by
  unfold unitClamp
  rcases le_total x 0 with h | h
  · rw [max_eq_left h, max_eq_left (by linarith : x - 1 ≤ 0)]
    norm_num
  · rw [max_eq_right h]
    rcases le_total x 1 with h1 | h1
    · rw [min_eq_right h1, max_eq_left (by linarith : x - 1 ≤ 0)]
      ring
    · rw [min_eq_left h1, max_eq_right (by linarith : 0 ≤ x - 1)]
      ring

theorem unitClamp_complement (x : ℝ) : unitClamp (1 - x) = 1 - unitClamp x := by
  rw [unitClamp_positive_parts, unitClamp_positive_parts]
  rcases le_total x 0 with h | h
  · rw [max_eq_left h, max_eq_left (by linarith : x - 1 ≤ 0),
      max_eq_right (by linarith : 0 ≤ 1 - x), max_eq_right (by linarith : 0 ≤ 1 - x - 1)]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith : 1 - x - 1 ≤ 0)]
    rcases le_total x 1 with h1 | h1
    · rw [max_eq_right (by linarith : 0 ≤ 1 - x), max_eq_left (by linarith : x - 1 ≤ 0)]
      ring
    · rw [max_eq_left (by linarith : 1 - x ≤ 0), max_eq_right (by linarith : 0 ≤ x - 1)]
      ring

theorem integral_positive_ramp {b a : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ u : I, max 0 (a - b * (u : ℝ))) = a ^ 2 / (2 * b) := by
  let q : I := ⟨a / b, div_nonneg ha hb.le, (div_le_one hb).mpr hab⟩
  have he : (fun u : I => max 0 (a - b * (u : ℝ))) = fun u => b * ramp q u := by
    funext u
    unfold ramp
    dsimp [q]
    rcases le_total (a / b - (u : ℝ)) 0 with h | h
    · rw [max_eq_left h, max_eq_left]
      · ring
      · have hh := (div_le_iff₀ hb).mp (by linarith : a / b ≤ (u : ℝ))
        nlinarith
    · rw [max_eq_right h, max_eq_right]
      · field_simp
      · have hh := (le_div_iff₀ hb).mp (by linarith : (u : ℝ) ≤ a / b)
        nlinarith
  rw [he, integral_const_mul, integral_ramp]
  dsimp [q]
  field_simp

theorem clampedMean_lower {b a : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (hab : a ≤ b) (ha1 : a ≤ 1) :
    clampedMean b a = a ^ 2 / (2 * b) := by
  unfold clampedMean
  have he (u : I) : unitClamp (a - b * (u : ℝ)) = max 0 (a - b * (u : ℝ)) := by
    unfold unitClamp
    apply min_eq_right
    exact max_le zero_le_one (by nlinarith [u.property.1])
  simp_rw [he]
  exact integral_positive_ramp hb ha hab

theorem clampedMean_affine {b a : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1) :
    clampedMean b a = a - b / 2 := by
  unfold clampedMean
  have he (u : I) : unitClamp (a - b * (u : ℝ)) = a - b * (u : ℝ) := by
    unfold unitClamp
    rw [max_eq_right (by nlinarith [u.property.2]), min_eq_right (by nlinarith [u.property.1])]
  simp_rw [he]
  rw [integral_sub (integrable_const _) ((Copula.integrable_continuous_unit volume continuous_subtype_val).const_mul _),
    integral_const_mul, Copula.integral_unit_id]
  simp
  ring

theorem clampedMean_saturated {b a : ℝ} (hb : 0 < b) (ha1 : 1 ≤ a) (hab : a ≤ b) :
    clampedMean b a = (a - 1 / 2) / b := by
  unfold clampedMean
  simp_rw [unitClamp_positive_parts]
  have he (u : I) : a - b * (u : ℝ) - 1 = (a - 1) - b * (u : ℝ) := by ring
  simp_rw [he]
  rw [integral_sub (Copula.integrable_continuous_unit volume (by fun_prop))
    (Copula.integrable_continuous_unit volume (by fun_prop)),
    integral_positive_ramp hb (by linarith) hab,
    integral_positive_ramp hb (by linarith) (by linarith)]
  field_simp
  ring

theorem clampedMean_complement (b a : ℝ) : clampedMean b (b + 1 - a) = 1 - clampedMean b a := by
  unfold clampedMean
  have he (u : I) : unitClamp (b + 1 - a - b * (u : ℝ)) =
      1 - unitClamp (a - b * (unitInterval.symm u : ℝ)) := by
    rw [show b + 1 - a - b * (u : ℝ) = 1 - (a - b * (unitInterval.symm u : ℝ)) by
      simp only [unitInterval.coe_symm_eq]; ring, unitClamp_complement]
  simp_rw [he]
  rw [integral_sub (integrable_const _) (Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop)),
    integral_unit_reflection (fun u : I => unitClamp (a - b * (u : ℝ)))]
  simp

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
