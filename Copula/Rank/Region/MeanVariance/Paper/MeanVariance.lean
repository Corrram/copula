import Copula.Rank.Region.MeanVariance.Paper.Dispersion

/-! # Corollary 1.7 and Remark 1.8: the exact mean-variance region -/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.MeanVariance

noncomputable def meanDistance (C : Copula 2) : ℝ := ∫ x, |(x 0 : ℝ) - x 1| ∂C.toMeasure

noncomputable def distanceVariance (C : Copula 2) : ℝ :=
  ∫ x, (|(x 0 : ℝ) - x 1| - meanDistance C) ^ 2 ∂C.toMeasure

/-- Equation (23); the nonnegative real power is written as a cube of a square root. -/
noncomputable def maximumVariance (m : ℝ) : ℝ := (1 - (Real.sqrt (1 - 2 * m)) ^ 3) / 3 - m ^ 2

/-- The absolute displacement mean has precisely the admissible range [0,1/2]. -/
theorem meanDistance_mem (C : Copula 2) : meanDistance C ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  have h := C.spearmanFootrule_mem_Icc
  have hm : C.spearmanFootrule = 1 - 3 * meanDistance C := ProbabilityTheory.Copula.RankRegion.MeanVariance.Support.footrule_eq_abs_moment C
  rw [hm] at h
  constructor <;> linarith [h.1, h.2]

/-- The affine conversion between rho and the variance at a fixed mean. -/
theorem distanceVariance_eq (C : Copula 2) :
    distanceVariance C = (1 - C.spearmanRho) / 6 - (meanDistance C) ^ 2 := by
  have h := quadratic_defect C
  have hm : C.spearmanFootrule = 1 - 3 * meanDistance C := ProbabilityTheory.Copula.RankRegion.MeanVariance.Support.footrule_eq_abs_moment C
  rw [hm, show (1 - (1 - 3 * meanDistance C)) / 3 = meanDistance C by ring] at h
  change _ = 6 * distanceVariance C at h
  nlinarith only [h]

/-- Corollary 1.7: both sharp variance bounds. -/
theorem sharp_variance_bounds (C : Copula 2) :
    minimumVariance (meanDistance C) ≤ distanceVariance C ∧
      distanceVariance C ≤ maximumVariance (meanDistance C) := by
  have hu := sharp_upper_bound C
  have hl := sharp_lower_bound C
  have hm : C.spearmanFootrule = 1 - 3 * meanDistance C := ProbabilityTheory.Copula.RankRegion.MeanVariance.Support.footrule_eq_abs_moment C
  rw [hm] at hu hl
  rw [show (1 + 2 * (1 - 3 * meanDistance C)) / 3 = 1 - 2 * meanDistance C by ring] at hl
  rw [distanceVariance_eq]
  dsimp [minimumVariance, maximumVariance]
  constructor <;> linarith

/-- The two boundary variances are ordered throughout the admissible mean range. -/
theorem minimumVariance_le_maximumVariance {m : ℝ} (hm : m ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    minimumVariance m ≤ maximumVariance m := by
  obtain ⟨C, hmean, hvar⟩ := minimum_variance_attained hm
  have he : meanDistance C = m := hmean
  have hv : distanceVariance C = minimumVariance m := by
    unfold distanceVariance
    rw [he]
    exact hvar
  have h := (sharp_variance_bounds C).2
  rwa [he, hv] at h

/-- Remark 1.8(a): every intermediate variance is attained, and no others are. -/
theorem exact_mean_variance_region (m v : ℝ) :
    (∃ C : Copula 2, meanDistance C = m ∧ distanceVariance C = v) ↔
      m ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ minimumVariance m ≤ v ∧ v ≤ maximumVariance m := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    exact ⟨meanDistance_mem C, sharp_variance_bounds C⟩
  · rintro ⟨hm, hlo, hhi⟩
    have hp : 1 - 3 * m ∈ Set.Icc (-1 / 2 : ℝ) 1 := by constructor <;> linarith [hm.1, hm.2]
    have hlow : Copula.RankRegion.RhoFootrule.lowerBoundary (1 - 3 * m) ≤ 1 - 6 * (v + m ^ 2) := by
      unfold Copula.RankRegion.RhoFootrule.lowerBoundary
      rw [show (1 + 2 * (1 - 3 * m)) / 3 = 1 - 2 * m by ring]
      dsimp [maximumVariance] at hhi
      linarith
    have hupp : 1 - 6 * (v + m ^ 2) ≤ upperRho (1 - 3 * m) := by
      dsimp [minimumVariance] at hlo
      linarith
    obtain ⟨C, hr, hphi⟩ := (exact_region (1 - 6 * (v + m ^ 2)) (1 - 3 * m)).mpr ⟨hp, hlow, hupp⟩
    have he : meanDistance C = m := by
      have hh : C.spearmanFootrule = 1 - 3 * meanDistance C := ProbabilityTheory.Copula.RankRegion.MeanVariance.Support.footrule_eq_abs_moment C
      linarith only [hh, hphi]
    refine ⟨C, he, ?_⟩
    rw [distanceVariance_eq, hr, he]
    ring

/-- Corollary 1.7: the upper variance bound is attained for every prescribed mean. -/
theorem maximum_variance_attained {m : ℝ} (hm : m ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    ∃ C : Copula 2, meanDistance C = m ∧ distanceVariance C = maximumVariance m :=
  (exact_mean_variance_region m (maximumVariance m)).mpr
    ⟨hm, minimumVariance_le_maximumVariance hm, le_rfl⟩

end ProbabilityTheory.Copula.RankRegion.MeanVariance
