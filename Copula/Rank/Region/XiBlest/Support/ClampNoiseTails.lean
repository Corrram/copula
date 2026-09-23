import Copula.Rank.Region.XiBlest.Support.QuadraticBandPolynomial

/-! # The clipped tail corrections beyond the polynomial branch -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

theorem noiseMoment_ge_one (d : ℝ) (hd : 1 ≤ d) (k : ℕ) : noiseMoment k d=1 := by
  have he (z : I) : unitClamp ((z : ℝ)+d)=1 := by
    unfold unitClamp
    rw [max_eq_right (by linarith [z.property.1]),min_eq_left (by linarith [z.property.1])]
  unfold noiseMoment
  simp_rw [he]
  simp

theorem noiseMoment_le_neg_one (d : ℝ) (hd : d ≤ -1) (k : ℕ) (hk : k ≠ 0) : noiseMoment k d=0 := by
  have he (z : I) : unitClamp ((z : ℝ)+d)=0 := by
    unfold unitClamp
    rw [max_eq_left (by linarith [z.property.2])]
    norm_num
  unfold noiseMoment
  simp_rw [he]
  simp [hk]

theorem noise_square_full (d : ℝ) :
    (noiseMoment 2 d+noiseMoment 2 (-d))/2 =
      1/3+d^2/2-|d|^3/3+(max 0 (|d|-1))^2*(2*|d|+1)/6 := by
  by_cases hd : |d| ≤ 1
  · have h := clamp_noise_square_pair d hd
    have hn : noiseMoment 2 (-d)=(∫ z : I, unitClamp ((z : ℝ)-d)^2) := by simp [noiseMoment,sub_eq_add_neg]
    rw [hn,max_eq_left (by linarith)]
    simpa only [noiseMoment,zero_pow (by decide : 2 ≠ 0),zero_mul,zero_div,add_zero] using h
  · rcases le_total 0 d with hs | hs
    · rw [abs_of_nonneg hs] at hd ⊢
      rw [noiseMoment_ge_one d (by linarith) 2,noiseMoment_le_neg_one (-d) (by linarith) 2 (by decide),
        max_eq_right (by linarith)]
      ring
    · rw [abs_of_nonpos hs] at hd ⊢
      rw [noiseMoment_le_neg_one d (by linarith) 2 (by decide),noiseMoment_ge_one (-d) (by linarith) 2,
        max_eq_right (by linarith)]
      ring

theorem noise_weighted_full (b x y : ℝ) (hb : 0 ≤ b) :
    (x*noiseMoment 1 (b*(x-y))+y*noiseMoment 1 (b*(y-x)))/2 =
      (x+y)/4+(b/2)*(x-y)^2-(b^2/4)*|x-y|^3+
        |x-y| *(max 0 (b*|x-y|-1))^2/4 := by
  by_cases hd : b*|x-y| ≤ 1
  · have hdx : |b*(x-y)| ≤ 1 := by rwa [abs_mul,abs_of_nonneg hb]
    have hdy : |b*(y-x)| ≤ 1 := by rwa [abs_mul,abs_of_nonneg hb,abs_sub_comm y x]
    have h1 := clamp_noise_moment (b*(x-y)) hdx
    have h2 := clamp_noise_moment (b*(y-x)) hdy
    have hn (d : ℝ) : noiseMoment 1 d=∫ z : I, unitClamp ((z : ℝ)+d) := by simp [noiseMoment]
    rw [hn,hn,h1,h2,max_eq_left (by linarith)]
    simp only [abs_mul,abs_of_nonneg hb,abs_sub_comm y x,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_div,add_zero]
    rw [show |x-y|^3=(x-y)^2*|x-y| by rw [pow_succ,sq_abs]]
    ring
  · rcases le_total y x with hs | hs
    · rw [abs_of_nonneg (sub_nonneg.mpr hs)] at hd ⊢
      rw [noiseMoment_ge_one (b*(x-y)) (by linarith) 1,
        noiseMoment_le_neg_one (b*(y-x)) (by nlinarith) 1 (by decide),max_eq_right (by linarith)]
      ring
    · rw [abs_of_nonpos (sub_nonpos.mpr hs)] at hd ⊢
      rw [noiseMoment_ge_one (b*(y-x)) (by nlinarith) 1,
        noiseMoment_le_neg_one (b*(x-y)) (by nlinarith) 1 (by decide),max_eq_right (by linarith)]
      ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
