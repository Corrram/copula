import Copula.Rank.Region.XiRho.Support.ScaledRampMean

/-! # Polynomial moments of all clamped-affine section regimes -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

private theorem positive_scaled_ramp {b a : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (hab : a ≤ b) (u : I) :
    max 0 (a - b * (u : ℝ)) = b * ramp ⟨a / b, div_nonneg ha hb.le, (div_le_one hb).mpr hab⟩ u := by
  unfold ramp
  rcases le_total (a / b - (u : ℝ)) 0 with h | h
  · rw [max_eq_left h, max_eq_left]
    · ring
    · have hh := (div_le_iff₀ hb).mp (by linarith : a / b ≤ (u : ℝ))
      nlinarith
  · rw [max_eq_right h, max_eq_right]
    · field_simp
    · have hh := (le_div_iff₀ hb).mp (by linarith : (u : ℝ) ≤ a / b)
      nlinarith

theorem integral_positive_ramp_sq {b a : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ u : I, (max 0 (a - b * (u : ℝ))) ^ 2) = a ^ 3 / (3 * b) := by
  simp_rw [positive_scaled_ramp hb ha hab, mul_pow]
  rw [integral_const_mul, integral_ramp_sq]
  dsimp
  field_simp

theorem integral_id_positive_ramp {b a : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ u : I, (u : ℝ) * max 0 (a - b * (u : ℝ))) = a ^ 3 / (6 * b ^ 2) := by
  simp_rw [positive_scaled_ramp hb ha hab]
  have he (u : I) (r : ℝ) : (u : ℝ) * (b * r) = b * ((u : ℝ) * r) := by ring
  simp_rw [he]
  rw [integral_const_mul, integral_id_mul_ramp]
  dsimp
  field_simp

noncomputable def clampedSquare (b a : ℝ) : ℝ := ∫ u : I, unitClamp (a - b * (u : ℝ)) ^ 2
noncomputable def clampedWeight (b a : ℝ) : ℝ := ∫ u : I, (1 - (u : ℝ)) * unitClamp (a - b * (u : ℝ))

private theorem clamp_lower {b a : ℝ} (hb : 0 ≤ b) (ha1 : a ≤ 1) (u : I) :
    unitClamp (a - b * (u : ℝ)) = max 0 (a - b * (u : ℝ)) := by
  apply min_eq_right
  exact max_le zero_le_one (by nlinarith [u.property.1])

theorem clampedSquare_lower {b a : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (hab : a ≤ b) (ha1 : a ≤ 1) :
    clampedSquare b a = a ^ 3 / (3 * b) := by
  unfold clampedSquare
  simp_rw [clamp_lower hb.le ha1]
  exact integral_positive_ramp_sq hb ha hab

theorem clampedWeight_lower {b a : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (hab : a ≤ b) (ha1 : a ≤ 1) :
    clampedWeight b a = a ^ 2 / (2 * b) - a ^ 3 / (6 * b ^ 2) := by
  unfold clampedWeight
  simp_rw [clamp_lower hb.le ha1, sub_mul, one_mul]
  rw [integral_sub (Copula.integrable_continuous_unit volume (by fun_prop))
    (Copula.integrable_continuous_unit volume (by fun_prop)),
    integral_positive_ramp hb ha hab, integral_id_positive_ramp hb ha hab]

private theorem clamp_affine {b a : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1) (u : I) :
    unitClamp (a - b * (u : ℝ)) = a - b * (u : ℝ) := by
  unfold unitClamp
  rw [max_eq_right (by nlinarith [u.property.2]), min_eq_right (by nlinarith [u.property.1])]

theorem clampedSquare_affine {b a : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1) :
    clampedSquare b a = a ^ 2 - a * b + b ^ 2 / 3 := by
  unfold clampedSquare
  simp_rw [clamp_affine hb hba ha1]
  have he (u : I) : (a - b * (u : ℝ)) ^ 2 = a ^ 2 - (2 * a * b) * (u : ℝ) + b ^ 2 * (u : ℝ) ^ 2 := by ring
  simp_rw [he]
  rw [integral_add (Copula.integrable_continuous_unit volume (by fun_prop))
    (Copula.integrable_continuous_unit volume (by fun_prop)),
    integral_sub (integrable_const _) (Copula.integrable_continuous_unit volume (by fun_prop)),
    integral_const_mul, integral_const_mul, Copula.integral_unit_id, Copula.integral_unit_pow]
  simp
  ring

theorem clampedWeight_affine {b a : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1) :
    clampedWeight b a = a / 2 - b / 6 := by
  unfold clampedWeight
  simp_rw [clamp_affine hb hba ha1]
  have he (u : I) : (1 - (u : ℝ)) * (a - b * (u : ℝ)) = a - (a + b) * (u : ℝ) + b * (u : ℝ) ^ 2 := by ring
  simp_rw [he]
  rw [integral_add (Copula.integrable_continuous_unit volume (by fun_prop))
    (Copula.integrable_continuous_unit volume (by fun_prop)),
    integral_sub (integrable_const _) (Copula.integrable_continuous_unit volume (by fun_prop)),
    integral_const_mul, integral_const_mul, Copula.integral_unit_id, Copula.integral_unit_pow]
  simp
  ring

private theorem clamp_square_parts (x : ℝ) :
    unitClamp x ^ 2 = (max 0 x) ^ 2 - (max 0 (x - 1)) ^ 2 - 2 * max 0 (x - 1) := by
  rw [unitClamp_positive_parts]
  rcases le_total x 1 with h | h
  · rw [max_eq_left (by linarith : x - 1 ≤ 0)]
    ring
  · rw [max_eq_right (by linarith : 0 ≤ x), max_eq_right (by linarith : 0 ≤ x - 1)]
    ring

theorem clampedSquare_saturated {b a : ℝ} (hb : 0 < b) (ha1 : 1 ≤ a) (hab : a ≤ b) :
    clampedSquare b a = (a - 2 / 3) / b := by
  unfold clampedSquare
  simp_rw [clamp_square_parts]
  have he (u : I) : a - b * (u : ℝ) - 1 = (a - 1) - b * (u : ℝ) := by ring
  simp_rw [he]
  rw [integral_sub (Copula.integrable_continuous_unit volume (by fun_prop))
    (Copula.integrable_continuous_unit volume (by fun_prop)),
    integral_sub (Copula.integrable_continuous_unit volume (by fun_prop))
    (Copula.integrable_continuous_unit volume (by fun_prop)), integral_const_mul,
    integral_positive_ramp_sq hb (by linarith) hab,
    integral_positive_ramp_sq hb (by linarith) (by linarith),
    integral_positive_ramp hb (by linarith) (by linarith)]
  field_simp
  ring

theorem clampedWeight_saturated {b a : ℝ} (hb : 0 < b) (ha1 : 1 ≤ a) (hab : a ≤ b) :
    clampedWeight b a = (a - 1 / 2) / b - (a ^ 2 - a + 1 / 3) / (2 * b ^ 2) := by
  unfold clampedWeight
  simp_rw [sub_mul, one_mul]
  rw [integral_sub (Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop))
    (Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop))]
  change clampedMean b a - _ = _
  rw [clampedMean_saturated hb ha1 hab]
  simp_rw [unitClamp_positive_parts, mul_sub]
  have he (u : I) : a - b * (u : ℝ) - 1 = (a - 1) - b * (u : ℝ) := by ring
  simp_rw [he]
  rw [integral_sub (Copula.integrable_continuous_unit volume (by fun_prop))
    (Copula.integrable_continuous_unit volume (by fun_prop)),
    integral_id_positive_ramp hb (by linarith) hab,
    integral_id_positive_ramp hb (by linarith) (by linarith)]
  ring

theorem clampedSquare_complement (b a : ℝ) :
    clampedSquare b (b + 1 - a) = 1 - 2 * clampedMean b a + clampedSquare b a := by
  unfold clampedSquare clampedMean
  have he (u : I) : unitClamp (b + 1 - a - b * (u : ℝ)) ^ 2 =
      (fun w : I => 1 - 2 * unitClamp (a - b * (w : ℝ)) + unitClamp (a - b * (w : ℝ)) ^ 2)
        (unitInterval.symm u) := by
    rw [show b + 1 - a - b * (u : ℝ) = 1 - (a - b * (unitInterval.symm u : ℝ)) by
      simp only [unitInterval.coe_symm_eq]; ring, unitClamp_complement]
    ring
  simp_rw [he]
  rw [integral_unit_reflection (fun w : I => 1 - 2 * unitClamp (a - b * (w : ℝ)) + unitClamp (a - b * (w : ℝ)) ^ 2),
    integral_add (Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop))
      (Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop)),
    integral_sub (integrable_const _) (Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop)),
    integral_const_mul]
  simp

theorem clampedWeight_complement (b a : ℝ) :
    clampedWeight b (b + 1 - a) = 1 / 2 - clampedMean b a + clampedWeight b a := by
  unfold clampedWeight clampedMean
  have he (u : I) : (1 - (u : ℝ)) * unitClamp (b + 1 - a - b * (u : ℝ)) =
      (fun w : I => (w : ℝ) - unitClamp (a - b * (w : ℝ)) +
        (1 - (w : ℝ)) * unitClamp (a - b * (w : ℝ))) (unitInterval.symm u) := by
    rw [show b + 1 - a - b * (u : ℝ) = 1 - (a - b * (unitInterval.symm u : ℝ)) by
      simp only [unitInterval.coe_symm_eq]; ring, unitClamp_complement]
    simp only [unitInterval.coe_symm_eq]
    ring
  simp_rw [he]
  rw [integral_unit_reflection (fun w : I => (w : ℝ) - unitClamp (a - b * (w : ℝ)) +
      (1 - (w : ℝ)) * unitClamp (a - b * (w : ℝ))),
    integral_add (Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop))
      (Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop)),
    integral_sub (Copula.integrable_continuous_unit volume (by fun_prop))
      (Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop)), Copula.integral_unit_id]

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
