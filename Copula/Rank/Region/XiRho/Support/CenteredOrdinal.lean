import Copula.OrdinalSum.Rank

/-! # The centered ordinal-sum identities (equation 9)

The parameter here is the central width `alpha=1-2a`. Both zero width
and full width are included, and the CDF is checked on the central square.
-/

open ProbabilityTheory
open Copula.OrdinalSum
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

noncomputable def centralMargin (α : I) : I :=
  ⟨(1 - (α : ℝ)) / 2, by constructor <;> linarith [α.property.1, α.property.2]⟩

noncomputable def centralSplit (α : I) : I :=
  ⟨2 * (α : ℝ) / (1 + α), by
    have hp : 0 < 1 + (α : ℝ) := by linarith [α.property.1]
    exact ⟨div_nonneg (by linarith [α.property.1]) hp.le,
      (div_le_one hp).mpr (by linarith [α.property.2])⟩⟩

theorem central_weight (α : I) :
    (1 - (centralMargin α : ℝ)) * centralSplit α = (α : ℝ) := by
  have hp : 1 + (α : ℝ) ≠ 0 := by linarith [α.property.1]
  dsimp [centralMargin, centralSplit]
  field_simp [hp]
  ring

noncomputable def centeredOrdinal (C : Copula 2) (α : I) : Copula 2 :=
  (Copula.comonotonic 2).ordinalSum
    (C.ordinalSum (Copula.comonotonic 2) (centralSplit α)) (centralMargin α)

theorem centeredOrdinal_zero (C : Copula 2) : centeredOrdinal C 0 = Copula.comonotonic 2 := by
  have hs : centralSplit 0 = 0 := by apply Subtype.ext; norm_num [centralSplit]
  simp [centeredOrdinal, hs, Copula.ordinalSum_comonotonic]

theorem centeredOrdinal_one (C : Copula 2) : centeredOrdinal C 1 = C := by
  have hs : centralSplit 1 = 1 := by apply Subtype.ext; norm_num [centralSplit]
  have hm : centralMargin 1 = 0 := by apply Subtype.ext; norm_num [centralMargin]
  simp [centeredOrdinal, hs, hm]

/-- Embed a point into the central interval. -/
noncomputable def centralEmbed (α u : I) : I :=
  upperEmbed (centralMargin α) (lowerEmbed (centralSplit α) u)

theorem coe_centralEmbed (α u : I) :
    (centralEmbed α u : ℝ) = (1 - (α : ℝ)) / 2 + (α : ℝ) * u := by
  change (centralMargin α : ℝ) + (1 - (centralMargin α : ℝ)) *
    ((centralSplit α : ℝ) * u) = _
  rw [← mul_assoc, central_weight]
  rfl

/-- The actual CDF on the central square, including the collapsed endpoint. -/
theorem centeredOrdinal_cdf (C : Copula 2) (α u v : I) :
    (centeredOrdinal C α).cdf ![centralEmbed α u, centralEmbed α v] =
      (1 - (α : ℝ)) / 2 + (α : ℝ) * C.cdf ![u, v] := by
  by_cases hα : α = 0
  · subst α
    rw [centeredOrdinal_zero, Copula.cdf_comonotonic_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, coe_centralEmbed]
    norm_num
  have hα0 : (0 : ℝ) < α := lt_of_le_of_ne α.property.1
    (fun he => hα (Subtype.ext he.symm))
  have hm : centralMargin α < 1 := by
    change (1 - (α : ℝ)) / 2 < 1
    linarith [α.property.1]
  have hs : 0 < centralSplit α := by
    change (0 : ℝ) < 2 * (α : ℝ) / (1 + α)
    positivity
  unfold centeredOrdinal centralEmbed
  rw [Copula.cdf_ordinalSum_upperEmbed _ _ _ _ _ hm,
    Copula.cdf_ordinalSum_lowerEmbed _ _ _ _ _ hs, ← mul_assoc, central_weight]
  rfl

theorem centeredOrdinal_tau (C : Copula 2) (α : I) :
    (centeredOrdinal C α).kendallTau = (α : ℝ) ^ 2 * C.kendallTau + 1 - (α : ℝ) ^ 2 := by
  simp only [centeredOrdinal, Copula.kendallTau_ordinalSum, Copula.kendallTau_comonotonic]
  have hw := central_weight α
  calc
    _ = 1 - ((1 - (centralMargin α : ℝ)) * centralSplit α) ^ 2 * (1 - C.kendallTau) := by ring
    _ = _ := by rw [hw]; ring

theorem centeredOrdinal_footrule (C : Copula 2) (α : I) :
    (centeredOrdinal C α).spearmanFootrule =
      (α : ℝ) ^ 2 * C.spearmanFootrule + 1 - (α : ℝ) ^ 2 := by
  simp only [centeredOrdinal, Copula.spearmanFootrule_ordinalSum, Copula.spearmanFootrule_comonotonic]
  have hw := central_weight α
  calc
    _ = 1 - ((1 - (centralMargin α : ℝ)) * centralSplit α) ^ 2 * (1 - C.spearmanFootrule) := by ring
    _ = _ := by rw [hw]; ring

theorem centeredOrdinal_beta (C : Copula 2) (α : I) :
    (centeredOrdinal C α).blomqvistBeta = (α : ℝ) * C.blomqvistBeta + 1 - (α : ℝ) := by
  have hh : centralEmbed α Copula.unitHalf = Copula.unitHalf := by
    apply Subtype.ext
    rw [coe_centralEmbed]
    change (1 - (α : ℝ)) / 2 + (α : ℝ) * (1 / 2) = 1 / 2
    ring
  have hc := centeredOrdinal_cdf C α Copula.unitHalf Copula.unitHalf
  rw [hh] at hc
  rw [Copula.blomqvistBeta, hc, Copula.blomqvistBeta]
  ring

theorem centeredOrdinal_rho (C : Copula 2) (α : I) :
    (centeredOrdinal C α).spearmanRho = (α : ℝ) ^ 3 * C.spearmanRho + 1 - (α : ℝ) ^ 3 := by
  simp only [centeredOrdinal, Copula.spearmanRho_ordinalSum, Copula.spearmanRho_comonotonic]
  have hw := central_weight α
  calc
    _ = 1 - ((1 - (centralMargin α : ℝ)) * centralSplit α) ^ 3 * (1 - C.spearmanRho) := by ring
    _ = _ := by rw [hw]; ring

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
