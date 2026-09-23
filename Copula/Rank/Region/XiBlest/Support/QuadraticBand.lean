import Copula.Rank.Region.XiBlest.Support.ClampedRhoOptimization
import Copula.Rank.Region.XiBlest.Support.ConditionalCopula

/-! # Quadratically clamped copulas for the xi–Blest boundary

The intercept is chosen by the uniform marginal constraint. Its existence
uses the intermediate value theorem, and the ordering of its means proves
monotonicity in the response threshold. No asserted copula or optimizer is
passed as a hypothesis.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

noncomputable def quadraticMean (b a : ℝ) : ℝ :=
  ∫ u : I, unitClamp (a + b * (1 - (u : ℝ)) ^ 2)

theorem continuous_quadraticMean (b : ℝ) : Continuous (quadraticMean b) := by
  have h := continuous_parametric_integral_of_continuous (μ := (volume : Measure I))
    (f := fun a : ℝ => fun u : I => unitClamp (a + b * (1 - (u : ℝ)) ^ 2))
    (by unfold unitClamp; fun_prop) isCompact_univ
  change Continuous (fun a : ℝ => ∫ u : I, unitClamp (a + b * (1 - (u : ℝ)) ^ 2))
  simpa only [Measure.restrict_univ] using h

theorem quadraticMean_monotone (b : ℝ) : Monotone (quadraticMean b) := by
  intro a c hac
  apply integral_mono
    (Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop))
    (Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop))
  intro u
  exact min_le_min le_rfl (max_le_max le_rfl (add_le_add_left hac _))

theorem quadraticMean_zero (b : ℝ) (hb : 0 ≤ b) : quadraticMean b (-b) = 0 := by
  unfold quadraticMean
  have he (u : I) : unitClamp (-b + b * (1 - (u : ℝ)) ^ 2) = 0 := by
    unfold unitClamp
    rw [max_eq_left (by nlinarith [u.property.1, u.property.2, mul_nonneg hb (mul_nonneg u.property.1 (sub_nonneg.mpr u.property.2))])]
    norm_num
  simp_rw [he]
  simp

theorem quadraticMean_top (b : ℝ) (hb : 0 ≤ b) : quadraticMean b 1 = 1 := by
  unfold quadraticMean
  have he (u : I) : unitClamp (1 + b * (1 - (u : ℝ)) ^ 2) = 1 := by
    have h : 1 ≤ 1 + b * (1 - (u : ℝ)) ^ 2 := by nlinarith [mul_nonneg hb (sq_nonneg (1 - (u : ℝ)))]
    unfold unitClamp
    rw [max_eq_right (by linarith), min_eq_left h]
  simp_rw [he]
  simp

theorem exists_quadratic_intercept (b : ℝ) (hb : 0 ≤ b) (v : I) :
    ∃ a ∈ Icc (-b) (1 : ℝ), quadraticMean b a = (v : ℝ) := by
  have h := intermediate_value_Icc (show -b ≤ (1 : ℝ) by linarith)
    (continuous_quadraticMean b).continuousOn
  rw [quadraticMean_zero b hb, quadraticMean_top b hb] at h
  exact h v.property

noncomputable def quadraticIntercept (b : ℝ) (hb : 0 ≤ b) (v : I) : ℝ :=
  if v = 0 then -b else if v = 1 then 1
  else (exists_quadratic_intercept b hb v).choose

theorem quadraticIntercept_mean (b : ℝ) (hb : 0 ≤ b) (v : I) :
    quadraticMean b (quadraticIntercept b hb v) = (v : ℝ) := by
  unfold quadraticIntercept
  split_ifs with hz ho
  · subst v
    exact quadraticMean_zero b hb
  · subst v
    exact quadraticMean_top b hb
  · exact (exists_quadratic_intercept b hb v).choose_spec.2

theorem quadraticIntercept_monotone (b : ℝ) (hb : 0 ≤ b) : Monotone (quadraticIntercept b hb) := by
  intro v w hvw
  rcases eq_or_lt_of_le hvw with rfl | hvw
  · rfl
  · by_contra h
    have he := quadraticMean_monotone b (le_of_not_ge h)
    rw [quadraticIntercept_mean, quadraticIntercept_mean] at he
    exact (not_le_of_gt hvw) he

noncomputable def quadraticKernel (b : ℝ) (hb : 0 ≤ b) (v u : I) : ℝ :=
  unitClamp (quadraticIntercept b hb v + b * (1 - (u : ℝ)) ^ 2)

theorem quadraticKernel_integrable (b : ℝ) (hb : 0 ≤ b) (v : I) :
    Integrable (quadraticKernel b hb v) :=
  Copula.integrable_continuous_unit volume (by unfold quadraticKernel unitClamp; fun_prop)

theorem quadraticKernel_monotone (b : ℝ) (hb : 0 ≤ b) (u : I) :
    Monotone (fun v => quadraticKernel b hb v u) := by
  intro v w hvw
  exact min_le_min le_rfl (max_le_max le_rfl (add_le_add_left (quadraticIntercept_monotone b hb hvw) _))

theorem quadraticKernel_zero (b : ℝ) (hb : 0 ≤ b) (u : I) : quadraticKernel b hb 0 u = 0 := by
  simp only [quadraticKernel, quadraticIntercept, ↓reduceIte]
  unfold unitClamp
  rw [max_eq_left (by nlinarith [u.property.1, u.property.2, mul_nonneg hb (mul_nonneg u.property.1 (sub_nonneg.mpr u.property.2))])]
  norm_num

theorem quadraticKernel_one (b : ℝ) (hb : 0 ≤ b) (u : I) : quadraticKernel b hb 1 u = 1 := by
  have he : quadraticIntercept b hb 1 = 1 := by simp [quadraticIntercept]
  have h : 1 ≤ 1 + b * (1 - (u : ℝ)) ^ 2 := by nlinarith [mul_nonneg hb (sq_nonneg (1 - (u : ℝ)))]
  unfold quadraticKernel unitClamp
  rw [he, max_eq_right (by linarith), min_eq_left h]

/-- Actual quadratic-band copula at slope `b`; normalization is solved internally. -/
noncomputable def quadraticBand (b : ℝ) (hb : 0 ≤ b) : Copula 2 :=
  copulaOfConditional (quadraticKernel b hb) (quadraticKernel_integrable b hb) (quadraticKernel_monotone b hb)
    (quadraticKernel_zero b hb) (quadraticKernel_one b hb) (quadraticIntercept_mean b hb)

theorem quadraticBand_cdf (b : ℝ) (hb : 0 ≤ b) (u v : I) :
    (quadraticBand b hb).cdf ![u, v] = ∫ t in Iic u, unitClamp (quadraticIntercept b hb v + b * (1 - (t : ℝ)) ^ 2) :=
  copulaOfConditional_cdf _ _ _ _ _ _ u v

theorem quadraticBand_conditionalCDF (b : ℝ) (hb : 0 ≤ b) (v : I) :
    (fun u => (quadraticBand b hb).conditionalCDF u v) =ᵐ[volume]
      fun u => unitClamp (quadraticIntercept b hb v + b * (1 - (u : ℝ)) ^ 2) :=
  copulaOfConditional_kernel _ _ _ _ _ _ v

theorem quadraticBand_isSI (b : ℝ) (hb : 0 ≤ b) : (quadraticBand b hb).IsSI := by
  intro a c d v hac hcd
  simp only [quadraticBand_cdf]
  apply Copula.integral_Iic_concave_of_antitone (quadraticKernel_integrable b hb v) _ a c d hac hcd
  intro u w huw
  apply min_le_min le_rfl
  apply max_le_max le_rfl
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ hb
  nlinarith [u.property.1, u.property.2, w.property.1, w.property.2,
    show (u : ℝ) ≤ w from huw]

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
