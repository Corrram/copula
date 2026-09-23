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

private noncomputable def n8ThreeQuarter : I := ⟨3/4, by constructor <;> norm_num⟩
private theorem n8_half_cdf (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen8 θ hθ).cdf ![unitHalf, unitHalf] = (θ-1)/(3*θ-1) := by
  rw [nelsen8_cdf_full]
  norm_num [unitHalf]
  have hnum : 0 ≤ θ^2-1 := by nlinarith
  have hden : 0 < 3*θ^2+2*θ-1 := by nlinarith
  have hden2 : 3*θ-1 ≠ 0 := by linarith
  have hdorig : 0 < θ^2-(θ-1)^2*(1/2)*(1/2) := by nlinarith
  have hq : 0 ≤ (θ^2*(1/2)*(1/2)-1/4) / (θ^2-(θ-1)^2*(1/2)*(1/2)) := by
    apply div_nonneg
    · nlinarith
    · exact hdorig.le
  rw [max_eq_right hq]
  field_simp [ne_of_gt hdorig, ne_of_gt hden, hden2]
  ring_nf
  have hnf3 : (-1+θ*2+θ^2*3) ≠ 0 := by nlinarith [hden]
  have hnf1 : (-1+θ*3) ≠ 0 := by nlinarith [hden2]
  field_simp [hnf3, hnf1]
  ring
private theorem n8_three_quarter_cdf (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen8 θ hθ).cdf ![n8ThreeQuarter, unitHalf] =
      (3*θ^2-1)/(7*θ^2+2*θ-1) := by
  rw [nelsen8_cdf_full]
  norm_num [n8ThreeQuarter, unitHalf]
  have hnum : 0 ≤ 3*θ^2-1 := by nlinarith
  have hden : 0 < 7*θ^2+2*θ-1 := by nlinarith
  have hdorig : 0 < θ^2-(θ-1)^2*(1/4)*(1/2) := by nlinarith
  have hq : 0 ≤ (θ^2*(3/4)*(1/2)-1/8) / (θ^2-(θ-1)^2*(1/4)*(1/2)) := by
    apply div_nonneg
    · nlinarith
    · exact hdorig.le
  rw [max_eq_right hq]
  field_simp [ne_of_gt hdorig, ne_of_gt hden]
  ring
/-- Nelsen 8 is not conditionally decreasing at any parameter strictly above one. -/
theorem not_isCD_nelsen8 (θ : ℝ) (hθ : 1 < θ) :
    ¬(nelsen8 θ (le_of_lt hθ)).IsCD := by
  intro h
  have hs := h.isSD unitHalf n8ThreeQuarter 1 unitHalf
    (by change (1/2:ℝ) ≤ 3/4; norm_num)
    (by change (3/4:ℝ) ≤ 1; norm_num)
  rw [n8_half_cdf, n8_three_quarter_cdf, cdf_two_one_left] at hs
  norm_num [unitHalf, n8ThreeQuarter] at hs
  have hd1 : 0 < 3*θ-1 := by linarith
  have hd2 : 0 < 7*θ^2+2*θ-1 := by nlinarith
  have hdiff : 0 < (θ-1)^2*(θ+1) /
      (2*(3*θ-1)*(7*θ^2+2*θ-1)) := by positivity
  have heq : 2*((3*θ^2-1)/(7*θ^2+2*θ-1)) -
      (θ-1)/(3*θ-1) - 1/2 =
      (θ-1)^2*(θ+1)/(2*(3*θ-1)*(7*θ^2+2*θ-1)) := by
    have hnf7 : (-1+θ*2+θ^2*7) ≠ 0 := by nlinarith [hd2]
    field_simp [hnf7]
    ring_nf
    field_simp [hnf7]
    ring
  linarith
/-- The lower-Fréchet endpoint is the only conditionally decreasing Nelsen 8 copula. -/
theorem isCD_nelsen8_iff (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen8 θ hθ).IsCD ↔ θ = 1 := by
  constructor
  · intro h
    rcases eq_or_lt_of_le hθ with heq | hlt
    · exact heq.symm
    · exact False.elim (not_isCD_nelsen8 θ hlt h)
  · intro heq
    subst θ
    simpa using isCD_nelsen8_one
end ProbabilityTheory.Copula
