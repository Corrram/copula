import Copula.Rank.Region.XiRho.Paper.BandOptimization
import Copula.Rank.Region.XiRho.Support.ScaledRampMean

/-! # Equations (19)--(22): the explicit diagonal-band family at every positive slope -/

open MeasureTheory ProbabilityTheory Set ProbabilityTheory.Copula.RankRegion.XiRho.Support
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiRho

noncomputable def bandCut (b : ℝ) : ℝ := min (b / 2) (1 / (2 * b))

/-- The source's b*s(v), so the conditional section is clamp(a(v)-b*u,0,1). -/
noncomputable def sourceBandIntercept (b : ℝ) (v : I) : ℝ :=
  if (v : ℝ) ≤ bandCut b then Real.sqrt (2 * b * (v : ℝ))
  else if (v : ℝ) ≤ 1 - bandCut b then
    (if b ≤ 1 then (v : ℝ) + b / 2 else b * (v : ℝ) + 1 / 2)
  else b + 1 - Real.sqrt (2 * b * (1 - (v : ℝ)))

theorem bandCut_small {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) : bandCut b = b / 2 := by
  apply min_eq_left
  apply (le_div_iff₀ (by positivity : 0 < 2 * b)).mpr
  nlinarith

theorem bandCut_large {b : ℝ} (hb : 0 < b) (hb1 : 1 ≤ b) : bandCut b = 1 / (2 * b) := by
  apply min_eq_right
  apply (div_le_iff₀ (by positivity : 0 < 2 * b)).mpr
  nlinarith

theorem bandCut_mem {b : ℝ} (hb : 0 < b) : bandCut b ∈ Icc (0 : ℝ) (1 / 2) := by
  refine ⟨le_min (by positivity) (by positivity), ?_⟩
  by_cases hb1 : b ≤ 1
  · rw [bandCut_small hb hb1]
    linarith
  · rw [bandCut_large hb (by linarith)]
    apply (div_le_iff₀ (by positivity : 0 < 2 * b)).mpr
    linarith

private theorem source_lower_mean {b : ℝ} (hb : 0 < b) (v : I) (hv : (v : ℝ) ≤ bandCut b) :
    clampedMean b (Real.sqrt (2 * b * (v : ℝ))) = (v : ℝ) := by
  have hvb := hv.trans (min_le_left _ _)
  have hv1 := hv.trans (min_le_right _ _)
  have hv1' := (le_div_iff₀ (by positivity : 0 < 2 * b)).mp hv1
  have hs := Real.sq_sqrt (show 0 ≤ 2 * b * (v : ℝ) by exact mul_nonneg (by positivity) v.property.1)
  have hn := Real.sqrt_nonneg (2 * b * (v : ℝ))
  have hqb : Real.sqrt (2 * b * (v : ℝ)) ≤ b := by nlinarith
  have hq1 : Real.sqrt (2 * b * (v : ℝ)) ≤ 1 := by nlinarith
  rw [clampedMean_lower hb hn hqb hq1, hs]
  field_simp

/-- The complete source formula satisfies the uniform marginal equation. -/
theorem sourceBandIntercept_mean {b : ℝ} (hb : 0 < b) (v : I) :
    clampedMean b (sourceBandIntercept b v) = (v : ℝ) := by
  unfold sourceBandIntercept
  split_ifs with hv hl hb1
  · exact source_lower_mean hb v hv
  · have hcut := bandCut_small hb hb1
    rw [hcut] at hv hl
    rw [clampedMean_affine hb.le (by linarith) (by linarith)]
    ring
  · have hcut := bandCut_large hb (by linarith)
    rw [hcut] at hv hl
    have hlo : 1 ≤ 2 * b * (v : ℝ) := by
      have h := (div_lt_iff₀ (by positivity : 0 < 2 * b)).mp (lt_of_not_ge hv)
      nlinarith
    have hhi : 2 * b * (v : ℝ) ≤ 2 * b - 1 := by
      have h : 1 / (2 * b) ≤ 1 - (v : ℝ) := by linarith
      have h' := (div_le_iff₀ (by positivity : 0 < 2 * b)).mp h
      nlinarith
    rw [clampedMean_saturated hb (by linarith) (by linarith)]
    field_simp
    ring
  · rw [clampedMean_complement]
    have h := source_lower_mean hb (unitInterval.symm v) (by
      change 1 - (v : ℝ) ≤ bandCut b
      linarith)
    change clampedMean b (Real.sqrt (2 * b * (1 - (v : ℝ)))) = 1 - (v : ℝ) at h
    rw [h]
    ring

/-- Ordering is forced by the exact marginal means, including the two transition points. -/
theorem sourceBandIntercept_monotone {b : ℝ} (hb : 0 < b) : Monotone (sourceBandIntercept b) := by
  intro v w hvw
  rcases eq_or_lt_of_le hvw with rfl | hvw
  · rfl
  · by_contra h
    have hh := clampedMean_monotone b (le_of_not_ge h)
    rw [sourceBandIntercept_mean hb, sourceBandIntercept_mean hb] at hh
    exact (not_le_of_gt hvw) hh

private theorem sourceBandIntercept_zero {b : ℝ} (hb : 0 < b) : sourceBandIntercept b 0 = 0 := by
  simp [sourceBandIntercept, (bandCut_mem hb).1]

private theorem sourceBandIntercept_one {b : ℝ} (hb : 0 < b) : sourceBandIntercept b 1 = b + 1 := by
  have hp : 0 < bandCut b := lt_min (by positivity) (by positivity)
  have hc := (bandCut_mem hb).2
  simp [sourceBandIntercept, show ¬(1 : ℝ) ≤ bandCut b by linarith,
    show ¬(1 : ℝ) ≤ 1 - bandCut b by linarith]

/-- The source C_b, constructed from its explicit conditional sections. -/
noncomputable def sourceBand (b : ℝ) (hb : 0 < b) : Copula 2 :=
  copulaOfConditional (fun v u => unitClamp (sourceBandIntercept b v - b * (u : ℝ)))
    (fun _ => Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop))
    (fun u v w hvw => min_le_min le_rfl (max_le_max le_rfl
      (sub_le_sub_right (sourceBandIntercept_monotone hb hvw) _)))
    (fun u => by rw [sourceBandIntercept_zero hb]; unfold unitClamp
                 rw [max_eq_left (by nlinarith [u.property.1])]; norm_num)
    (fun u => by rw [sourceBandIntercept_one hb]; unfold unitClamp
                 rw [max_eq_right (by nlinarith [u.property.2]), min_eq_left (by nlinarith [u.property.2])])
    (sourceBandIntercept_mean hb)

/-- Equation (19), as the integral of its explicit clamped section. -/
theorem sourceBand_cdf (b : ℝ) (hb : 0 < b) (u v : I) :
    (sourceBand b hb).cdf ![u,v] =
      ∫ t in Iic u, unitClamp (sourceBandIntercept b v-b*(t : ℝ)) :=
  copulaOfConditional_cdf _ _ _ _ _ _ u v

theorem sourceBand_conditionalCDF (b : ℝ) (hb : 0 < b) (v : I) :
    (fun u => (sourceBand b hb).conditionalCDF u v) =ᵐ[volume]
      fun u => unitClamp (sourceBandIntercept b v - b * (u : ℝ)) :=
  copulaOfConditional_kernel _ _ _ _ _ _ v

theorem sourceBand_derivative (b : ℝ) (hb : 0 < b) (v : I) :
    (fun u : I => deriv (Copula.cdfSection (sourceBand b hb) v) (u : ℝ)) =ᵐ[volume]
      fun u => unitClamp (sourceBandIntercept b v-b*(u : ℝ)) :=
  ((sourceBand b hb).conditionalCDF_eq_deriv v).symm.trans (sourceBand_conditionalCDF b hb v)

/-- The explicit source family is the previously proved normalization-defined optimizer. -/
theorem sourceBand_eq_normalizedBand (b : ℝ) (hb : 0 < b) :
    sourceBand b hb = normalizedBand b hb.le := by
  apply (normalizedBand_support_eq_iff (sourceBand b hb) b hb.le).mp
  apply le_antisymm (normalizedBand_support _ _ _)
  exact clamped_rho_support (normalizedBand b hb.le) (sourceBand b hb) b
    (Filter.Eventually.of_forall fun v => ⟨sourceBandIntercept b v, sourceBand_conditionalCDF b hb v⟩)

end ProbabilityTheory.Copula.RankRegion.XiRho
