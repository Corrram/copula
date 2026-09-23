/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Nelsen8
import Copula.Dependence.ConditionalMonotonicity
import Copula.Dependence.DensityTotalPositivity

/-! # Nelsen 8 dependence exclusions

A positive diagonal point has CDF zero. This excludes PQD, CI, CDF-level TP2,
and an MTP2 density for every finite θ ≥ 1. The θ = 1 endpoint is CD.
-/
open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem n8_zero_diagonal_witness (θ : ℝ) (hθ : 1 ≤ θ) :
    ∃ t : I, 0 < (t : ℝ) ∧ (nelsen8 θ hθ).cdf ![t,t] = 0 := by
  let t : ℝ := 1/(θ+1)
  have hd : 0 < θ+1 := by linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  let ti : I := ⟨t, ht.le, ht1⟩
  refine ⟨ti, ht, ?_⟩
  have hn : θ^2*t^2-(1-t)^2 = 0 := by
    dsimp [t]
    field_simp [ne_of_gt hd]
    ring
  rw [nelsen8_cdf_full]
  have hn' : θ^2*(ti:ℝ)*(ti:ℝ) - (1-(ti:ℝ))*(1-(ti:ℝ)) = 0 := by
    change θ^2*t*t-(1-t)*(1-t)=0
    nlinarith [hn]
  rw [hn']
  simp

/-- Every Nelsen 8 copula fails positive quadrant dependence. -/
theorem not_isPQD_nelsen8 (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(nelsen8 θ hθ).IsPQD := by
  obtain ⟨t, ht, hz⟩ := n8_zero_diagonal_witness θ hθ
  intro h
  have hh := h t t
  rw [hz] at hh
  nlinarith [mul_pos ht ht]

/-- No Nelsen 8 copula is conditionally increasing. -/
theorem not_isCI_nelsen8 (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(nelsen8 θ hθ).IsCI :=
  fun h => not_isPQD_nelsen8 θ hθ h.isPQD

/-- Nelsen 8 never has a TP2 CDF. -/
theorem not_isTP2CDF_nelsen8 (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(nelsen8 θ hθ).IsTP2CDF :=
  fun h => not_isPQD_nelsen8 θ hθ h.isPQD

/-- Nelsen 8 never has an MTP2 Lebesgue density. -/
theorem not_hasMTP2Density_nelsen8 (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(nelsen8 θ hθ).HasMTP2Density :=
  fun h => not_isPQD_nelsen8 θ hθ (hasMTP2Density_isPQD _ h)

/-- The lower-Fréchet endpoint of Nelsen 8 is conditionally decreasing. -/
theorem isCD_nelsen8_one : (nelsen8 1 le_rfl).IsCD := by
  simpa only [nelsen8_one] using isCD_countermonotonic

end ProbabilityTheory.Copula
