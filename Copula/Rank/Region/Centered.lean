/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.Rank
import Copula.Rank.Region.Moments

/-! # A central copula block with comonotonic outer blocks

This endpoint-safe construction places a copula in the centered square
of side length `r`. It is useful for fixed-median extremizing shuffles.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion

noncomputable def centeredEdge (r : I) : I :=
  ⟨(1 - (r : ℝ)) / 2, by constructor <;> linarith [r.property.1, r.property.2]⟩

noncomputable def centeredSplit (r : I) : I :=
  ⟨2 * (r : ℝ) / (1 + (r : ℝ)), by
    constructor
    · exact div_nonneg (mul_nonneg (by norm_num) r.property.1) (by linarith [r.property.1])
    · apply (div_le_one (by linarith [r.property.1])).mpr; linarith [r.property.2]⟩

/-- Insert `C` in the centered square of side `r`, with `M` on either side. -/
noncomputable def centered (C : Copula 2) (r : I) : Copula 2 :=
  (comonotonic 2).ordinalSum (C.ordinalSum (comonotonic 2) (centeredSplit r)) (centeredEdge r)

theorem centered_rho (C : Copula 2) (r : I) :
    (centered C r).spearmanRho = 1 - (r : ℝ) ^ 3 * (1 - C.spearmanRho) := by
  simp only [centered, spearmanRho_ordinalSum, spearmanRho_comonotonic, sub_self,
    mul_zero, sub_zero, centeredEdge, centeredSplit]
  have hd : 1 + (r : ℝ) ≠ 0 := by linarith [r.property.1]
  field_simp
  ring

theorem centered_tau (C : Copula 2) (r : I) :
    (centered C r).kendallTau = 1 - (r : ℝ) ^ 2 * (1 - C.kendallTau) := by
  simp only [centered, kendallTau_ordinalSum, kendallTau_comonotonic, sub_self,
    mul_zero, sub_zero, centeredEdge, centeredSplit]
  have hd : 1 + (r : ℝ) ≠ 0 := by linarith [r.property.1]
  field_simp
  ring

theorem centered_footrule (C : Copula 2) (r : I) :
    (centered C r).spearmanFootrule = 1 - (r : ℝ) ^ 2 * (1 - C.spearmanFootrule) := by
  simp only [centered, spearmanFootrule_ordinalSum, spearmanFootrule_comonotonic, sub_self,
    mul_zero, sub_zero, centeredEdge, centeredSplit]
  have hd : 1 + (r : ℝ) ≠ 0 := by linarith [r.property.1]
  field_simp
  ring

theorem centered_beta (C : Copula 2) (r : I) :
    (centered C r).blomqvistBeta = 1 - (r : ℝ) * (1 - C.blomqvistBeta) := by
  by_cases hr : r = 0
  · subst r
    have he : centeredSplit 0 = 0 := by ext; norm_num [centeredSplit]
    simp [centered, he, ordinalSum_comonotonic]
  have hr0 : 0 < (r : ℝ) := lt_of_le_of_ne r.property.1 (fun h => hr (Subtype.ext h.symm))
  have ha : centeredEdge r < 1 := by change (1 - (r : ℝ)) / 2 < 1; linarith
  have hb : 0 < centeredSplit r := by change (0 : ℝ) < 2 * (r : ℝ) / (1 + (r : ℝ)); positivity
  have he : OrdinalSum.upperEmbed (centeredEdge r)
      (OrdinalSum.lowerEmbed (centeredSplit r) unitHalf) = unitHalf := by
    apply Subtype.ext
    change (1 - (r : ℝ)) / 2 + (1 - (1 - (r : ℝ)) / 2) *
      (2 * (r : ℝ) / (1 + (r : ℝ)) * (1 / 2)) = 1 / 2
    have hd : 1 + (r : ℝ) ≠ 0 := by linarith [r.property.1]
    field_simp; ring
  have h := cdf_ordinalSum_upperEmbed (comonotonic 2)
    (C.ordinalSum (comonotonic 2) (centeredSplit r)) (centeredEdge r)
    (OrdinalSum.lowerEmbed (centeredSplit r) unitHalf)
    (OrdinalSum.lowerEmbed (centeredSplit r) unitHalf) ha
  rw [he, cdf_ordinalSum_lowerEmbed _ _ _ _ _ hb] at h
  unfold blomqvistBeta
  change 4 * ((comonotonic 2).ordinalSum _ _).cdf ![unitHalf, unitHalf] - 1 = _
  rw [h]
  dsimp [centeredEdge, centeredSplit]
  have hd : 1 + (r : ℝ) ≠ 0 := by linarith [r.property.1]
  field_simp; ring

end ProbabilityTheory.Copula.RankRegion
