/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.ConditionalMonotonicity
import Copula.Dependence.DensityTotalPositivity
import Copula.Families.Nelsen
import Copula.TailDependence.Nelsen2
import Copula.TailDependence.Quadrant
open scoped unitInterval
namespace ProbabilityTheory.Copula
/-- Positive upper-tail dependence excludes CD at every parameter above one. -/
theorem not_isCD_nelsen2 (θ : ℝ) (hθ : 1 < θ) :
    ¬(nelsen2 θ (le_of_lt hθ)).IsCD := by
  intro h
  have hzero := isNQD_hasUpperTailDependence_zero h.isNQD
  have htail := hasUpperTailDependence_nelsen2 θ (le_of_lt hθ)
  have heq := hzero.unique htail
  have hθ0 : 0 < θ := by linarith
  have hi : 0 < θ⁻¹ := inv_pos.mpr hθ0
  have hcancel : θ * θ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hθ0)
  have hinv : θ⁻¹ < 1 := by
    have hm := mul_lt_mul_of_pos_right hθ hi
    nlinarith
  have hp := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hinv
  linarith

/-- The lower-Fréchet Nelsen 2 endpoint is CD. -/
theorem isCD_nelsen2_one : (nelsen2 1 le_rfl).IsCD := by
  simpa only [nelsen2_one] using isCD_countermonotonic

/-- Nelsen 2 is CD exactly at θ = 1. -/
theorem isCD_nelsen2_iff (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen2 θ hθ).IsCD ↔ θ = 1 := by
  constructor
  · intro h
    rcases eq_or_lt_of_le hθ with heq | hlt
    · exact heq.symm
    · exact False.elim (not_isCD_nelsen2 θ hlt h)
  · intro heq
    subst θ
    simpa using isCD_nelsen2_one
/-- A positive diagonal point has zero CDF for every finite parameter. -/
theorem not_isPQD_nelsen2 (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(nelsen2 θ hθ).IsPQD := by
  let q : ℝ := (2 : ℝ) ^ (-θ⁻¹)
  have hθ0 : 0 < θ := by linarith
  have hi : 0 < θ⁻¹ := inv_pos.mpr hθ0
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqlt : q < 1 := by
    dsimp [q]
    have hp := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (show -θ⁻¹ < 0 by linarith)
    norm_num at hp
    exact hp
  let t : ℝ := 1 - q
  have ht0 : 0 < t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  let ti : I := ⟨t, ht0.le, ht1⟩
  have hpow : q ^ θ = 1 / 2 := by
    dsimp [q]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have he : -θ⁻¹ * θ = -1 := by
      have hc : θ⁻¹ * θ = 1 := inv_mul_cancel₀ (ne_of_gt hθ0)
      linarith
    rw [he]
    norm_num
  have hcdf : (nelsen2 θ hθ).cdf ![ti, ti] = 0 := by
    rw [nelsen2_cdf_full]
    have hti : ti ≠ 0 := by
      intro hz
      have hz' := congrArg (fun x : I => (x : ℝ)) hz
      change t = 0 at hz'
      linarith
    simp only [hti, or_self, ↓reduceIte]
    have hs : (1 - (ti : ℝ)) ^ θ + (1 - (ti : ℝ)) ^ θ = 1 := by
      change (1-t)^θ + (1-t)^θ = 1
      dsimp [t]
      have hbase : 1 - (1 - q) = q := by ring
      rw [hbase, hpow]
      ring
    rw [hs]
    norm_num
  intro h
  have hp := h ti ti
  rw [hcdf] at hp
  nlinarith [mul_pos ht0 ht0]

/-- No Nelsen 2 member is conditionally increasing. -/
theorem not_isCI_nelsen2 (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(nelsen2 θ hθ).IsCI := fun h => not_isPQD_nelsen2 θ hθ h.isPQD
/-- No Nelsen 2 CDF is TP2. -/
theorem not_isTP2CDF_nelsen2 (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(nelsen2 θ hθ).IsTP2CDF :=
  fun h => not_isPQD_nelsen2 θ hθ h.isPQD

/-- No Nelsen 2 copula has an MTP2 Lebesgue density. -/
theorem not_hasMTP2Density_nelsen2 (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(nelsen2 θ hθ).HasMTP2Density :=
  fun h => not_isPQD_nelsen2 θ hθ (hasMTP2Density_isPQD _ h)
end ProbabilityTheory.Copula