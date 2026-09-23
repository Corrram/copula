import Copula.Rank.Region.XiBlest.Support.ClampedRhoOptimization
import Copula.Rank.Region.XiBlest.Support.ConditionalCopula

/-! # Diagonal-band copulas at every nonnegative slope

The intercept is chosen by the uniform marginal constraint. Its existence
uses the intermediate value theorem, and the ordering of its means proves
monotonicity in the response threshold. No asserted copula or optimizer is
passed as a hypothesis.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

noncomputable def clampedMean (b a : ℝ) : ℝ :=
  ∫ u : I, unitClamp (a - b * (u : ℝ))

theorem continuous_clampedMean (b : ℝ) : Continuous (clampedMean b) := by
  have h := continuous_parametric_integral_of_continuous (μ := (volume : Measure I))
    (f := fun a : ℝ => fun u : I => unitClamp (a - b * (u : ℝ)))
    (by unfold unitClamp; fun_prop) isCompact_univ
  change Continuous (fun a : ℝ => ∫ u : I, unitClamp (a - b * (u : ℝ)))
  simpa only [Measure.restrict_univ] using h

theorem clampedMean_monotone (b : ℝ) : Monotone (clampedMean b) := by
  intro a c hac
  apply integral_mono
    (Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop))
    (Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop))
  intro u
  exact min_le_min le_rfl (max_le_max le_rfl (sub_le_sub_right hac _))

theorem clampedMean_zero (b : ℝ) (hb : 0 ≤ b) : clampedMean b 0 = 0 := by
  unfold clampedMean
  have he (u : I) : unitClamp (0 - b * (u : ℝ)) = 0 := by
    unfold unitClamp
    rw [max_eq_left (by nlinarith [u.property.1])]
    norm_num
  simp_rw [he]
  simp

theorem clampedMean_top (b : ℝ) (hb : 0 ≤ b) : clampedMean b (b + 1) = 1 := by
  unfold clampedMean
  have he (u : I) : unitClamp (b + 1 - b * (u : ℝ)) = 1 := by
    have h : 1 ≤ b + 1 - b * (u : ℝ) := by nlinarith [u.property.2]
    unfold unitClamp
    rw [max_eq_right (by linarith), min_eq_left h]
  simp_rw [he]
  simp

theorem exists_clamped_intercept (b : ℝ) (hb : 0 ≤ b) (v : I) :
    ∃ a ∈ Icc (0 : ℝ) (b + 1), clampedMean b a = (v : ℝ) := by
  have h := intermediate_value_Icc (show (0 : ℝ) ≤ b + 1 by linarith)
    (continuous_clampedMean b).continuousOn
  rw [clampedMean_zero b hb, clampedMean_top b hb] at h
  exact h v.property

noncomputable def bandIntercept (b : ℝ) (hb : 0 ≤ b) (v : I) : ℝ :=
  if v = 0 then 0 else if v = 1 then b + 1
  else (exists_clamped_intercept b hb v).choose

theorem bandIntercept_mean (b : ℝ) (hb : 0 ≤ b) (v : I) :
    clampedMean b (bandIntercept b hb v) = (v : ℝ) := by
  unfold bandIntercept
  split_ifs with hz ho
  · subst v
    exact clampedMean_zero b hb
  · subst v
    exact clampedMean_top b hb
  · exact (exists_clamped_intercept b hb v).choose_spec.2

theorem bandIntercept_monotone (b : ℝ) (hb : 0 ≤ b) : Monotone (bandIntercept b hb) := by
  intro v w hvw
  rcases eq_or_lt_of_le hvw with rfl | hvw
  · rfl
  · by_contra h
    have he := clampedMean_monotone b (le_of_not_ge h)
    rw [bandIntercept_mean, bandIntercept_mean] at he
    exact (not_le_of_gt hvw) he

noncomputable def bandKernel (b : ℝ) (hb : 0 ≤ b) (v u : I) : ℝ :=
  unitClamp (bandIntercept b hb v - b * (u : ℝ))

theorem bandKernel_integrable (b : ℝ) (hb : 0 ≤ b) (v : I) :
    Integrable (bandKernel b hb v) :=
  Copula.integrable_continuous_unit volume (by unfold bandKernel unitClamp; fun_prop)

theorem bandKernel_monotone (b : ℝ) (hb : 0 ≤ b) (u : I) :
    Monotone (fun v => bandKernel b hb v u) := by
  intro v w hvw
  exact min_le_min le_rfl (max_le_max le_rfl (sub_le_sub_right (bandIntercept_monotone b hb hvw) _))

theorem bandKernel_zero (b : ℝ) (hb : 0 ≤ b) (u : I) : bandKernel b hb 0 u = 0 := by
  simp only [bandKernel, bandIntercept, ↓reduceIte]
  unfold unitClamp
  rw [max_eq_left (by nlinarith [u.property.1])]
  norm_num

theorem bandKernel_one (b : ℝ) (hb : 0 ≤ b) (u : I) : bandKernel b hb 1 u = 1 := by
  have he : bandIntercept b hb 1 = b + 1 := by simp [bandIntercept]
  have h : 1 ≤ b + 1 - b * (u : ℝ) := by nlinarith [u.property.2]
  unfold bandKernel unitClamp
  rw [he, max_eq_right (by linarith), min_eq_left h]

/-- Actual diagonal-band copula at slope `b`; normalization is solved internally. -/
noncomputable def diagonalBand (b : ℝ) (hb : 0 ≤ b) : Copula 2 :=
  copulaOfConditional (bandKernel b hb) (bandKernel_integrable b hb) (bandKernel_monotone b hb)
    (bandKernel_zero b hb) (bandKernel_one b hb) (bandIntercept_mean b hb)

theorem diagonalBand_cdf (b : ℝ) (hb : 0 ≤ b) (u v : I) :
    (diagonalBand b hb).cdf ![u, v] = ∫ t in Iic u, unitClamp (bandIntercept b hb v - b * (t : ℝ)) :=
  copulaOfConditional_cdf _ _ _ _ _ _ u v

theorem diagonalBand_conditionalCDF (b : ℝ) (hb : 0 ≤ b) (v : I) :
    (fun u => (diagonalBand b hb).conditionalCDF u v) =ᵐ[volume]
      fun u => unitClamp (bandIntercept b hb v - b * (u : ℝ)) :=
  copulaOfConditional_kernel _ _ _ _ _ _ v

theorem diagonalBand_isSI (b : ℝ) (hb : 0 ≤ b) : (diagonalBand b hb).IsSI := by
  intro a c d v hac hcd
  simp only [diagonalBand_cdf]
  apply Copula.integral_Iic_concave_of_antitone (bandKernel_integrable b hb v) _ a c d hac hcd
  intro u w huw
  exact min_le_min le_rfl (max_le_max le_rfl
    (sub_le_sub_left (mul_le_mul_of_nonneg_left (show (u : ℝ) ≤ w from huw) hb) _))

theorem diagonalBand_support (C : Copula 2) (b : ℝ) (hb : 0 ≤ b) :
    b * C.spearmanRho - C.chatterjeeXi ≤
      b * (diagonalBand b hb).spearmanRho - (diagonalBand b hb).chatterjeeXi :=
  clamped_rho_support C (diagonalBand b hb) b (Filter.Eventually.of_forall fun v =>
    ⟨bandIntercept b hb v, diagonalBand_conditionalCDF b hb v⟩)

theorem diagonalBand_support_eq_iff (C : Copula 2) (b : ℝ) (hb : 0 ≤ b) :
    b * C.spearmanRho - C.chatterjeeXi =
      b * (diagonalBand b hb).spearmanRho - (diagonalBand b hb).chatterjeeXi ↔
      C = diagonalBand b hb :=
  clamped_rho_support_eq_iff C (diagonalBand b hb) b (Filter.Eventually.of_forall fun v =>
    ⟨bandIntercept b hb v, diagonalBand_conditionalCDF b hb v⟩)

/-- Every constructed positive-slope band is the unique maximizer of rho at its xi. -/
theorem diagonalBand_maximal_rho (C : Copula 2) (b : ℝ) (hb : 0 < b)
    (hx : C.chatterjeeXi ≤ (diagonalBand b hb.le).chatterjeeXi) :
    C.spearmanRho ≤ (diagonalBand b hb.le).spearmanRho := by
  have h := diagonalBand_support C b hb.le
  nlinarith

theorem diagonalBand_maximal_rho_eq_iff (C : Copula 2) (b : ℝ) (hb : 0 < b)
    (hx : C.chatterjeeXi = (diagonalBand b hb.le).chatterjeeXi) :
    C.spearmanRho = (diagonalBand b hb.le).spearmanRho ↔ C = diagonalBand b hb.le := by
  refine ⟨fun hr => (diagonalBand_support_eq_iff C b hb.le).mp ?_, fun he => he ▸ rfl⟩
  rw [hx, hr]

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
