import Copula.Rank.Region.XiBlest.Support.ClampedRhoOptimization
import Copula.Rank.Region.XiBlest.Support.RampIntegrals

/-! # Uniform-noise moments of a translated clamp -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

private theorem clamp_sub_ramp (h : I) (z : I) :
    unitClamp ((z : ℝ)-(h : ℝ)) = ramp (unitInterval.symm h) (unitInterval.symm z) := by
  unfold unitClamp ramp
  simp only [unitInterval.coe_symm_eq]
  rw [min_eq_right (max_le zero_le_one (by linarith [z.property.2,h.property.1]))]
  congr 1
  ring

private theorem clamp_add_ramp (h : I) (z : I) :
    unitClamp ((z : ℝ)+(h : ℝ)) = 1-ramp (unitInterval.symm h) z := by
  unfold unitClamp ramp
  simp only [unitInterval.coe_symm_eq]
  rw [max_eq_right (add_nonneg z.property.1 h.property.1)]
  rcases le_total ((z : ℝ)+(h : ℝ)) 1 with he | he
  · rw [min_eq_right he,max_eq_right (by linarith)]
    ring
  · rw [min_eq_left he,max_eq_left (by linarith)]
    ring

theorem clamp_noise_sub (h : I) :
    (∫ z : I, unitClamp ((z : ℝ)-(h : ℝ))) = (1-(h : ℝ))^2/2 := by
  simp_rw [clamp_sub_ramp]
  rw [integral_unit_reflection,integral_ramp,unitInterval.coe_symm_eq]

theorem clamp_noise_sub_sq (h : I) :
    (∫ z : I, unitClamp ((z : ℝ)-(h : ℝ))^2) = (1-(h : ℝ))^3/3 := by
  simp_rw [clamp_sub_ramp]
  rw [integral_unit_reflection (fun z => ramp (unitInterval.symm h) z ^ 2),
    integral_ramp_sq,unitInterval.coe_symm_eq]

theorem clamp_noise_add (h : I) :
    (∫ z : I, unitClamp ((z : ℝ)+(h : ℝ))) = 1-(1-(h : ℝ))^2/2 := by
  simp_rw [clamp_add_ramp]
  rw [integral_sub (integrable_const _) (Copula.integrable_continuous_unit volume (continuous_ramp _)),
    integral_ramp,unitInterval.coe_symm_eq]
  simp

theorem clamp_noise_add_sq (h : I) :
    (∫ z : I, unitClamp ((z : ℝ)+(h : ℝ))^2) =
      1-(1-(h : ℝ))^2+(1-(h : ℝ))^3/3 := by
  simp_rw [clamp_add_ramp]
  have he (z : I) : (1-ramp (unitInterval.symm h) z)^2 =
      1-2*ramp (unitInterval.symm h) z+ramp (unitInterval.symm h) z^2 := by ring
  simp_rw [he]
  have hi := Copula.integrable_continuous_unit volume (continuous_ramp (unitInterval.symm h))
  have hs : Integrable (fun z => ramp (unitInterval.symm h) z ^ 2) :=
    Copula.integrable_continuous_unit volume ((continuous_ramp (unitInterval.symm h)).pow 2)
  have hh : Integrable (fun z => 1-2*ramp (unitInterval.symm h) z) :=
    (integrable_const (1 : ℝ)).sub (hi.const_mul 2)
  rw [integral_add hh hs,
    integral_sub (integrable_const _) (hi.const_mul 2),integral_const_mul,
    integral_ramp,integral_ramp_sq,unitInterval.coe_symm_eq]
  simp
  ring

theorem clamp_noise_moment (d : ℝ) (hd : |d| ≤ 1) :
    (∫ z : I, unitClamp ((z : ℝ)+d)) = 1/2+d-d*|d|/2 := by
  rcases le_total 0 d with h | h
  · have he := clamp_noise_add ⟨d,h,by simpa only [abs_of_nonneg h] using hd⟩
    rw [abs_of_nonneg h]
    dsimp only at he
    rw [he]
    ring
  · have he := clamp_noise_sub ⟨-d,by constructor <;> linarith [(abs_le.mp hd).1]⟩
    simp only [sub_neg_eq_add] at he
    rw [abs_of_nonpos h,he]
    ring

theorem clamp_noise_square_pair (d : ℝ) (hd : |d| ≤ 1) :
    ((∫ z : I, unitClamp ((z : ℝ)+d)^2)+(∫ z : I, unitClamp ((z : ℝ)-d)^2))/2 =
      1/3+d^2/2-|d|^3/3 := by
  rcases le_total 0 d with h | h
  · have h1 := clamp_noise_add_sq ⟨d,h,by simpa only [abs_of_nonneg h] using hd⟩
    have h2 := clamp_noise_sub_sq ⟨d,h,by simpa only [abs_of_nonneg h] using hd⟩
    dsimp only at h1 h2
    rw [h1,h2,abs_of_nonneg h]
    ring
  · have h1 := clamp_noise_add_sq ⟨-d,by constructor <;> linarith [(abs_le.mp hd).1]⟩
    have h2 := clamp_noise_sub_sq ⟨-d,by constructor <;> linarith [(abs_le.mp hd).1]⟩
    simp only [← sub_eq_add_neg,sub_neg_eq_add] at h1 h2
    rw [h1,h2,abs_of_nonpos h]
    ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
