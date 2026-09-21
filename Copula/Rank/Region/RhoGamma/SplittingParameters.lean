/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoGamma.GluedPotential
import Copula.Rank.Region.RhoFootrule.UpperLipschitz

open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoGamma

/-- The positive root gives the ratio of central and corner lengths. -/
noncomputable def splitRatio (s c : ℝ) : ℝ := (s + Real.sqrt (s ^ 2 + 2 * c)) / 2

theorem splitRatio_properties {s c w : ℝ} (hs : 0 < s) (hc : c < 0)
    (_hw : 0 ≤ w) (hdisc : w ^ 2 ≤ s ^ 2 + 2 * c) :
    0 < splitRatio s c ∧ splitRatio s c < s ∧
      s + w ≤ 2 * splitRatio s c ∧
      2 * splitRatio s c * (splitRatio s c - s) = c := by
  have hd : 0 ≤ s ^ 2 + 2 * c := (sq_nonneg w).trans hdisc
  have he := Real.sq_sqrt hd
  have hn := Real.sqrt_nonneg (s ^ 2 + 2 * c)
  have hl : w ≤ Real.sqrt (s ^ 2 + 2 * c) := by nlinarith only [he, hdisc, hn]
  have hu : Real.sqrt (s ^ 2 + 2 * c) < s := by nlinarith only [he, hs, hc, hn]
  dsimp [splitRatio]
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  nlinarith only [he]

noncomputable def centralLength (s c : ℝ) : ℝ := splitRatio s c / (1 + splitRatio s c)
noncomputable def cornerLength (s c : ℝ) : ℝ := 1 / (1 + splitRatio s c)
noncomputable def supportingSlope (s c : ℝ) : ℝ := s * cornerLength s c

theorem splitting_properties {s c w : ℝ} (hs : 0 < s) (hc : c < 0)
    (hw : 0 ≤ w) (hdisc : w ^ 2 ≤ s ^ 2 + 2 * c) :
    0 < centralLength s c ∧ centralLength s c < 1 ∧ 0 < cornerLength s c ∧
      centralLength s c + cornerLength s c = 1 ∧
      centralLength s c < supportingSlope s c ∧
      supportingSlope s c + cornerLength s c * w ≤ 2 * centralLength s c ∧
      (cornerLength s c) ^ 2 * c =
        2 * centralLength s c * (centralLength s c - supportingSlope s c) := by
  obtain ⟨hA, hAs, hAw, hEq⟩ := splitRatio_properties hs hc hw hdisc
  have hden : 0 < 1 + splitRatio s c := by linarith
  have hden0 := ne_of_gt hden
  dsimp [centralLength, cornerLength, supportingSlope]
  refine ⟨div_pos hA hden, (div_lt_one hden).mpr (by linarith),
    div_pos zero_lt_one hden, ?_, ?_, ?_, ?_⟩
  · field_simp; ring
  · rw [mul_one_div]
    exact (div_lt_div_iff_of_pos_right hden).mpr hAs
  · have hh := div_le_div_of_nonneg_right hAw hden.le
    convert hh using 1 <;> ring
  · field_simp
    nlinarith only [hEq]

end ProbabilityTheory.Copula.RankRegion.RhoGamma
