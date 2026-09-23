import Copula.Rank.Region.XiBlest.Support.CenteredOrdinal
import Copula.Rank.Region.XiBlest.Support.Functional

/-! # Dependence and symmetry of a central countermonotonic block -/

open ProbabilityTheory Set
open Copula.OrdinalSum
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

private theorem cdf_M_lower (D : Copula 2) (a u v : I) (huv : u ≤ v) (hu : u ≤ a) :
    ((Copula.comonotonic 2).ordinalSum D a).cdf ![u, v] = u := by
  rcases le_total v a with hv | hv
  · rw [Copula.cdf_ordinalSum_lower _ _ _ _ _ hu hv, Copula.cdf_comonotonic_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [min_eq_left (show (lowerCoord a u : ℝ) ≤ lowerCoord a v from lowerCoord_mono a huv), weight_lowerCoord,
      min_eq_right (show (u : ℝ) ≤ a from hu)]
  · exact Copula.cdf_ordinalSum_lower_upper _ _ _ _ _ hu hv

private theorem cdf_M_upper (C : Copula 2) (a u v : I) (huv : u ≤ v) (hv : a ≤ v) :
    (C.ordinalSum (Copula.comonotonic 2) a).cdf ![u, v] = u := by
  rcases le_total u a with hu | hu
  · exact Copula.cdf_ordinalSum_lower_upper _ _ _ _ _ hu hv
  · rw [Copula.cdf_ordinalSum_upper _ _ _ _ _ hu hv, Copula.cdf_comonotonic_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [min_eq_left (show (upperCoord a u : ℝ) ≤ upperCoord a v from upperCoord_mono a huv), weight_upperCoord,
      max_eq_right (sub_nonneg.mpr (show (a : ℝ) ≤ u from hu))]
    ring

theorem centralMargin_lt_one (α : I) : centralMargin α < 1 := by
  change (1 - (α : ℝ)) / 2 < 1
  linarith [α.property.1]

theorem central_top (α : I) :
    upperEmbed (centralMargin α) (centralSplit α) = unitInterval.symm (centralMargin α) := by
  apply Subtype.ext
  change (centralMargin α : ℝ) + (1 - (centralMargin α : ℝ)) * centralSplit α =
    1 - (centralMargin α : ℝ)
  rw [central_weight]
  dsimp [centralMargin]
  ring

theorem centeredOrdinal_cdf_below (C : Copula 2) (α u v : I)
    (huv : u ≤ v) (hu : u ≤ centralMargin α) :
    (centeredOrdinal C α).cdf ![u, v] = u :=
  cdf_M_lower _ _ _ _ huv hu

theorem centeredOrdinal_cdf_above (C : Copula 2) (α u v : I)
    (huv : u ≤ v) (hv : unitInterval.symm (centralMargin α) ≤ v) :
    (centeredOrdinal C α).cdf ![u, v] = u := by
  rcases le_total u (centralMargin α) with hu | hu
  · exact centeredOrdinal_cdf_below C α u v huv hu
  have hav : centralMargin α ≤ v := hu.trans huv
  have hv' : centralSplit α ≤ upperCoord (centralMargin α) v := by
    apply (upperEmbed_le_iff _ _ _ (centralMargin_lt_one α) hav).mp
    simpa only [central_top] using hv
  rw [centeredOrdinal, Copula.cdf_ordinalSum_upper _ _ _ _ _ hu hav,
    cdf_M_upper _ _ _ _ (upperCoord_mono _ huv) hv', weight_upperCoord,
    max_eq_right (sub_nonneg.mpr (show (centralMargin α : ℝ) ≤ u from hu))]
  ring

theorem centralEmbed_surjectiveOn (α u : I)
    (hu : centralMargin α ≤ u) (hv : u ≤ unitInterval.symm (centralMargin α)) :
    ∃ t : I, centralEmbed α t = u := by
  by_cases hα : α = 0
  · subst α
    refine ⟨0, ?_⟩
    apply Subtype.ext
    rw [coe_centralEmbed]
    change (1 - (0 : ℝ)) / 2 + 0 * 0 = (u : ℝ)
    have hL : (centralMargin (0 : I) : ℝ) ≤ u := hu
    have hU : (u : ℝ) ≤ 1 - (centralMargin (0 : I) : ℝ) := hv
    norm_num [centralMargin] at hL hU
    linarith
  have hp : (0 : ℝ) < α := lt_of_le_of_ne α.property.1
    (fun he => hα (Subtype.ext he.symm))
  have hu' : (centralMargin α : ℝ) ≤ u := hu
  have hv' : (u : ℝ) ≤ 1 - (centralMargin α : ℝ) := hv
  let t : I := ⟨((u : ℝ) - centralMargin α) / α,
    div_nonneg (sub_nonneg.mpr hu') hp.le, (div_le_one hp).mpr (by
      dsimp [centralMargin] at *
      linarith)⟩
  refine ⟨t, ?_⟩
  apply Subtype.ext
  rw [coe_centralEmbed]
  change (1 - (α : ℝ)) / 2 + (α : ℝ) * (((u : ℝ) - centralMargin α) / α) = u
  dsimp [centralMargin]
  field_simp
  ring

noncomputable def centralW (α : I) : Copula 2 := centeredOrdinal Copula.countermonotonic α

theorem centralW_exchangeable (α : I) : (centralW α).IsExchangeable :=
  Copula.isExchangeable_comonotonic.ordinalSum
    (Copula.isExchangeable_countermonotonic.ordinalSum Copula.isExchangeable_comonotonic _) _

theorem centralW_xi (α : I) : (centralW α).chatterjeeXi = 1 :=
  (functional_comonotonic.ordinalSum
    (functional_countermonotonic.ordinalSum functional_comonotonic _) _).xi_eq_one

theorem centralW_beta (α : I) : (centralW α).blomqvistBeta = 1 - 2 * (α : ℝ) := by
  rw [centralW, centeredOrdinal_beta, Copula.blomqvistBeta_countermonotonic]
  ring

theorem centralW_cdf_inside (α u v : I)
    (hu : centralMargin α ≤ u) (hu' : u ≤ unitInterval.symm (centralMargin α))
    (hv : centralMargin α ≤ v) (hv' : v ≤ unitInterval.symm (centralMargin α)) :
    (centralW α).cdf ![u, v] = (centralMargin α : ℝ) + max 0 ((u : ℝ) + v - 1) := by
  obtain ⟨s, rfl⟩ := centralEmbed_surjectiveOn α u hu hu'
  obtain ⟨t, rfl⟩ := centralEmbed_surjectiveOn α v hv hv'
  rw [centralW, centeredOrdinal_cdf, Copula.cdf_countermonotonic]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, coe_centralEmbed]
  rw [mul_max_of_nonneg _ _ α.property.1, mul_zero]
  change _ = (1 - (α : ℝ)) / 2 + _
  congr 2
  ring

/-- A pointwise formula covering the central square and both outer identity strips. -/
theorem centralW_cdf_ordered (α u v : I) (huv : u ≤ v) :
    (centralW α).cdf ![u, v] =
      if u ≤ centralMargin α ∨ unitInterval.symm (centralMargin α) ≤ v then (u : ℝ)
      else (centralMargin α : ℝ) + max 0 ((u : ℝ) + v - 1) := by
  split_ifs with h
  · rcases h with hu | hv
    · exact centeredOrdinal_cdf_below _ _ _ _ huv hu
    · exact centeredOrdinal_cdf_above _ _ _ _ huv hv
  · push Not at h
    exact centralW_cdf_inside α u v h.1.le (huv.trans h.2.le) (h.1.le.trans huv) h.2.le

theorem centralW_radiallySymmetric (α : I) : (centralW α).IsRadiallySymmetric := by
  apply (Copula.isRadiallySymmetric_iff _).mpr
  suffices h : ∀ u v : I, u ≤ v → (centralW α).cdf ![u, v] =
      (u : ℝ) + v - 1 + (centralW α).cdf ![unitInterval.symm u, unitInterval.symm v] by
    intro u v
    rcases le_total u v with huv | hvu
    · exact h u v huv
    · have hs := (Copula.isExchangeable_iff _).mp (centralW_exchangeable α)
      rw [hs u v, hs (unitInterval.symm u) (unitInterval.symm v)]
      convert h v u hvu using 1
      ring
  intro u v huv
  have hs := (Copula.isExchangeable_iff _).mp (centralW_exchangeable α)
  rw [hs (unitInterval.symm u) (unitInterval.symm v), centralW_cdf_ordered α u v huv,
    centralW_cdf_ordered α (unitInterval.symm v) (unitInterval.symm u)
      (show unitInterval.symm v ≤ unitInterval.symm u from unitInterval.symm_le_symm.mpr huv)]
  have hc : (unitInterval.symm v ≤ centralMargin α ∨ unitInterval.symm (centralMargin α) ≤ unitInterval.symm u) ↔
      (u ≤ centralMargin α ∨ unitInterval.symm (centralMargin α) ≤ v) := by
    simp only [unitInterval.symm_le_comm, unitInterval.symm_symm, or_comm]
  simp only [hc]
  split_ifs
  · simp only [unitInterval.coe_symm_eq]
    ring
  · simp only [unitInterval.coe_symm_eq]
    by_cases hz : (u : ℝ) + v ≤ 1
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
      ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      ring

theorem centralW_pqd (α : I) (hα : (α : ℝ) ≤ 1 / 2) : (centralW α).IsPQD := by
  suffices h : ∀ u v : I, u ≤ v → (u : ℝ) * v ≤ (centralW α).cdf ![u, v] by
    intro u v
    rcases le_total u v with huv | hvu
    · exact h u v huv
    · rw [(Copula.isExchangeable_iff _).mp (centralW_exchangeable α) u v, mul_comm]
      exact h v u hvu
  intro u v huv
  rw [centralW_cdf_ordered α u v huv]
  split_ifs
  · exact mul_le_of_le_one_right u.property.1 v.property.2
  · have ha : (1 / 4 : ℝ) ≤ centralMargin α := by dsimp [centralMargin]; linarith
    by_cases hz : (u : ℝ) + v ≤ 1
    · rw [max_eq_left (by linarith)]
      have hm := mul_nonneg (show 0 ≤ 1 - (u : ℝ) - v by linarith)
        (show 0 ≤ 1 + (u : ℝ) + v by linarith [u.property.1, v.property.1])
      nlinarith [sq_nonneg ((u : ℝ) - v)]
    · rw [max_eq_right (by linarith)]
      have hm := mul_nonneg (show 0 ≤ (u : ℝ) + v - 1 by linarith)
        (show 0 ≤ 3 - (u : ℝ) - v by linarith [u.property.2, v.property.2])
      nlinarith [sq_nonneg ((u : ℝ) - v)]

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
