import Copula.Rank.Region.XiRho.Support.ClampedRhoOptimization
import Copula.Rank.Region.XiRho.Support.ConditionalCopula
import Copula.Rank.Region.XiRho.Support.RampIntegrals

/-! # The unit-slope diagonal-band copula

The `b = 1` member of equations (19)--(22), including both response endpoints.
-/

open MeasureTheory ProbabilityTheory Set ProbabilityTheory.Copula.RankRegion.XiRho.Support
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiRho

noncomputable def unitBandIntercept (v : I) : ℝ :=
  if (v : ℝ) ≤ 1 / 2 then Real.sqrt (2 * (v : ℝ))
  else 2 - Real.sqrt (2 * (1 - (v : ℝ)))

noncomputable def unitBandKernel (v u : I) : ℝ :=
  unitClamp (unitBandIntercept v - (u : ℝ))

theorem sqrt_two_mem {v : I} (hv : (v : ℝ) ≤ 1 / 2) :
    Real.sqrt (2 * (v : ℝ)) ∈ Icc 0 1 := by
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  have h := Real.sq_sqrt (show 0 ≤ 2 * (v : ℝ) by nlinarith [v.property.1])
  nlinarith [Real.sqrt_nonneg (2 * (v : ℝ))]

theorem unitBandIntercept_monotone : Monotone unitBandIntercept := by
  intro v w hvw
  have hvw' : (v : ℝ) ≤ w := hvw
  unfold unitBandIntercept
  split_ifs with hv hw hw
  · exact Real.sqrt_le_sqrt (by linarith)
  · have hv1 := (sqrt_two_mem hv).2
    have hw1 := (sqrt_two_mem (v := unitInterval.symm w)
      (by change 1 - (w : ℝ) ≤ 1 / 2; linarith)).2
    change Real.sqrt (2 * (1 - (w : ℝ))) ≤ 1 at hw1
    linarith
  · linarith
  · have he := Real.sqrt_le_sqrt (show 2 * (1 - (w : ℝ)) ≤ 2 * (1 - (v : ℝ)) by linarith)
    linarith

theorem unitBandKernel_monotone (u : I) : Monotone (fun v => unitBandKernel v u) := by
  intro v w hvw
  exact min_le_min le_rfl (max_le_max le_rfl
    (sub_le_sub_right (unitBandIntercept_monotone hvw) _))

theorem unitBandKernel_integrable (v : I) : Integrable (unitBandKernel v) :=
  Copula.integrable_continuous_unit volume (by unfold unitBandKernel unitClamp; fun_prop)

theorem unitBandKernel_lower (v u : I) (hv : (v : ℝ) ≤ 1 / 2) :
    unitBandKernel v u = ramp ⟨Real.sqrt (2 * (v : ℝ)), sqrt_two_mem hv⟩ u := by
  unfold unitBandKernel unitBandIntercept unitClamp ramp
  rw [ite_eq_left hv, min_eq_right]
  exact max_le zero_le_one (by linarith [(sqrt_two_mem hv).2, u.property.1])

theorem unitBandKernel_upper (v u : I) (hv : 1 / 2 ≤ (v : ℝ)) :
    unitBandKernel v u = 1 - ramp
      ⟨Real.sqrt (2 * (1 - (v : ℝ))), sqrt_two_mem
        (v := unitInterval.symm v) (by change 1 - (v : ℝ) ≤ 1 / 2; linarith)⟩
      (unitInterval.symm u) := by
  have hq := sqrt_two_mem (v := unitInterval.symm v)
    (by change 1 - (v : ℝ) ≤ 1 / 2; linarith)
  change Real.sqrt (2 * (1 - (v : ℝ))) ∈ Icc 0 1 at hq
  have he : unitBandIntercept v = 2 - Real.sqrt (2 * (1 - (v : ℝ))) := by
    unfold unitBandIntercept
    split_ifs with h
    · have hv' : (v : ℝ) = 1 / 2 := by linarith
      norm_num [hv']
    · rfl
  unfold unitBandKernel unitClamp ramp
  rw [he]
  change min 1 (max 0 (2 - Real.sqrt (2 * (1 - (v : ℝ))) - (u : ℝ))) =
    1 - max 0 (Real.sqrt (2 * (1 - (v : ℝ))) - (1 - (u : ℝ)))
  rw [max_eq_right (by linarith [hq.2, u.property.2])]
  rcases le_total (Real.sqrt (2 * (1 - (v : ℝ))) - (1 - (u : ℝ))) 0 with h | h
  · rw [max_eq_left h, min_eq_left (by linarith)]
    ring
  · rw [max_eq_right h, min_eq_right (by linarith)]
    ring

theorem unitBandKernel_zero (u : I) : unitBandKernel 0 u = 0 := by
  simp [unitBandKernel, unitBandIntercept, unitClamp, max_eq_left (neg_nonpos.mpr u.property.1)]

theorem unitBandKernel_one (u : I) : unitBandKernel 1 u = 1 := by
  norm_num [unitBandKernel, unitBandIntercept, unitClamp,
    max_eq_right (show 0 ≤ 2 - (u : ℝ) by linarith [u.property.2]),
    min_eq_left (show 1 ≤ 2 - (u : ℝ) by linarith [u.property.2])]

theorem unitBandKernel_mean (v : I) : (∫ u : I, unitBandKernel v u) = (v : ℝ) := by
  by_cases hv : (v : ℝ) ≤ 1 / 2
  · simp_rw [unitBandKernel_lower v _ hv]
    rw [integral_ramp]
    have h := Real.sq_sqrt (show 0 ≤ 2 * (v : ℝ) by nlinarith [v.property.1])
    dsimp
    linarith
  · let q : I := ⟨Real.sqrt (2 * (1 - (v : ℝ))), sqrt_two_mem
        (v := unitInterval.symm v) (by change 1 - (v : ℝ) ≤ 1 / 2; linarith)⟩
    have he (u : I) : unitBandKernel v u = 1 - ramp q (unitInterval.symm u) :=
      unitBandKernel_upper v u (by linarith)
    simp_rw [he]
    have hi : Integrable (fun u : I => ramp q (unitInterval.symm u)) := by
      simpa only [Function.comp_def] using Copula.integrable_continuous_unit volume
        ((continuous_ramp q).comp unitInterval.continuous_symm)
    rw [integral_sub (integrable_const _) hi,
      integral_unit_reflection, integral_ramp]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have h := Real.sq_sqrt (show 0 ≤ 2 * (1 - (v : ℝ)) by linarith [v.property.2])
    dsimp [q]
    linarith

/-- The actual copula `C₁` from the article, constructed from its conditional law. -/
noncomputable def unitDiagonalBand : Copula 2 :=
  copulaOfConditional unitBandKernel unitBandKernel_integrable unitBandKernel_monotone
    unitBandKernel_zero unitBandKernel_one unitBandKernel_mean

theorem unitDiagonalBand_cdf (u v : I) :
    unitDiagonalBand.cdf ![u, v] = ∫ t in Iic u, unitBandKernel v t :=
  copulaOfConditional_cdf _ _ _ _ _ _ u v

theorem unitDiagonalBand_conditionalCDF (v : I) :
    (fun u => unitDiagonalBand.conditionalCDF u v) =ᵐ[volume] unitBandKernel v :=
  copulaOfConditional_kernel _ _ _ _ _ _ v

theorem unitDiagonalBand_derivative (v : I) :
    (fun u : I => deriv (Copula.cdfSection unitDiagonalBand v) (u : ℝ)) =ᵐ[volume]
      fun u => unitClamp (unitBandIntercept v - (u : ℝ)) :=
  (unitDiagonalBand.conditionalCDF_eq_deriv v).symm.trans (unitDiagonalBand_conditionalCDF v)

theorem unitDiagonalBand_isSI : unitDiagonalBand.IsSI := by
  intro a b c v hab hbc
  simp only [unitDiagonalBand_cdf]
  apply Copula.integral_Iic_concave_of_antitone (unitBandKernel_integrable v) _ a b c hab hbc
  intro u w huw
  exact min_le_min le_rfl (max_le_max le_rfl (sub_le_sub_left (show (u : ℝ) ≤ w from huw) _))

theorem unitDiagonalBand_support (C : Copula 2) :
    C.spearmanRho - C.chatterjeeXi ≤
      unitDiagonalBand.spearmanRho - unitDiagonalBand.chatterjeeXi := by
  simpa using clamped_rho_support C unitDiagonalBand 1 (Filter.Eventually.of_forall fun v =>
    ⟨unitBandIntercept v, by simp only [one_mul]; exact unitDiagonalBand_conditionalCDF v⟩)

theorem unitDiagonalBand_support_eq_iff (C : Copula 2) :
    C.spearmanRho - C.chatterjeeXi =
      unitDiagonalBand.spearmanRho - unitDiagonalBand.chatterjeeXi ↔ C = unitDiagonalBand := by
  simpa using clamped_rho_support_eq_iff C unitDiagonalBand 1 (Filter.Eventually.of_forall fun v =>
    ⟨unitBandIntercept v, by simp only [one_mul]; exact unitDiagonalBand_conditionalCDF v⟩)

end ProbabilityTheory.Copula.RankRegion.XiRho
