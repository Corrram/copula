/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.Rank
import Copula.Dependence.TotalPositivity
import Copula.Rank.FGM

/-! # Exact positive-dependence parameter ranges for FGM copulas -/

open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem isSI_fgm (θ : ℝ) (hθ : |θ| ≤ 1) (hpos : 0 ≤ θ) : (fgm θ hθ).IsSI := by
  intro a b c v hab hbc
  have hab' : 0 ≤ (b : ℝ) - (a : ℝ) := sub_nonneg.mpr hab
  have hbc' : 0 ≤ (c : ℝ) - (b : ℝ) := sub_nonneg.mpr hbc
  have hac' : 0 ≤ (c : ℝ) - (a : ℝ) := by linarith
  have hn := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hpos v.property.1)
    (sub_nonneg.mpr v.property.2)) hab') hbc') hac'
  simp only [cdf_fgm, Matrix.cons_val_zero, Matrix.cons_val_one, fgmCDF]
  nlinarith

theorem isTP2CDF_fgm (θ : ℝ) (hθ : |θ| ≤ 1) (hpos : 0 ≤ θ) : (fgm θ hθ).IsTP2CDF := by
  intro a b c d hab hcd
  have hn := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    hpos a.property.1) b.property.1) c.property.1) d.property.1)
    (sub_nonneg.mpr (show (a : ℝ) ≤ (b : ℝ) from hab)))
    (sub_nonneg.mpr (show (c : ℝ) ≤ (d : ℝ) from hcd))
  simp only [cdf_fgm, Matrix.cons_val_zero, Matrix.cons_val_one, fgmCDF]
  nlinarith

theorem isPQD_fgm_iff (θ : ℝ) (hθ : |θ| ≤ 1) : (fgm θ hθ).IsPQD ↔ 0 ≤ θ := by
  constructor
  · intro h
    have hb := h.blomqvistBeta_nonneg
    rw [blomqvistBeta_fgm] at hb
    linarith
  · exact fun h => (isSI_fgm θ hθ h).isPQD

theorem isLTD_fgm_iff (θ : ℝ) (hθ : |θ| ≤ 1) : (fgm θ hθ).IsLTD ↔ 0 ≤ θ :=
  ⟨fun h => (isPQD_fgm_iff θ hθ).mp h.isPQD, fun h => (isSI_fgm θ hθ h).isLTD⟩

theorem isRTI_fgm_iff (θ : ℝ) (hθ : |θ| ≤ 1) : (fgm θ hθ).IsRTI ↔ 0 ≤ θ :=
  ⟨fun h => (isPQD_fgm_iff θ hθ).mp h.isPQD, fun h => (isSI_fgm θ hθ h).isRTI⟩

theorem isSI_fgm_iff (θ : ℝ) (hθ : |θ| ≤ 1) : (fgm θ hθ).IsSI ↔ 0 ≤ θ :=
  ⟨fun h => (isPQD_fgm_iff θ hθ).mp h.isPQD, isSI_fgm θ hθ⟩

theorem isTP2CDF_fgm_iff (θ : ℝ) (hθ : |θ| ≤ 1) : (fgm θ hθ).IsTP2CDF ↔ 0 ≤ θ :=
  ⟨fun h => (isPQD_fgm_iff θ hθ).mp h.isPQD, isTP2CDF_fgm θ hθ⟩

end ProbabilityTheory.Copula
