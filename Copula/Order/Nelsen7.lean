/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Order.SymmetricSchur
import Copula.Rank.Nelsen7

/-! # Exact Schur ordering of Nelsen's seventh family -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- A two-valued conditional CDF maximizes convex tests among conditional CDFs
with the same mean and values bounded by its upper value. -/
theorem integral_convex_le_of_conditionalCDF_binary (C D : Copula 2) (v H : I)
    (hC : ∀ᵐ u, C.conditionalCDF u v ≤ (H : ℝ))
    (hD : ∀ᵐ u, D.conditionalCDF u v = 0 ∨ D.conditionalCDF u v = (H : ℝ))
    (φ : ℝ → ℝ) (hc : Continuous φ) (hv : ConvexOn ℝ (Icc 0 1) φ) :
    (∫ u : I, φ (C.conditionalCDF u v)) ≤ ∫ u : I, φ (D.conditionalCDF u v) := by
  by_cases hz : (H : ℝ) = 0
  · apply le_of_eq
    apply integral_congr_ae
    filter_upwards [hC, hD] with u hu hdu
    have hc0 := le_antisymm (hu.trans_eq hz) (C.conditionalCDF_nonneg u v)
    have hd0 : D.conditionalCDF u v = 0 := hdu.elim id (fun h => h.trans hz)
    rw [hc0, hd0]
  have hp : 0 < (H : ℝ) := lt_of_le_of_ne H.property.1 (Ne.symm hz)
  let L : ℝ → ℝ := fun x => (1 - x / H) * φ 0 + (x / H) * φ H
  have hi (E : Copula 2) : Integrable (fun u => L (E.conditionalCDF u v)) :=
    (((integrable_const 1).sub ((E.integrable_conditionalCDF v).div_const _)).mul_const _).add
      (((E.integrable_conditionalCDF v).div_const _).mul_const _)
  have he (E : Copula 2) : (∫ u : I, L (E.conditionalCDF u v)) = L v := by
    dsimp [L]
    rw [integral_add, integral_mul_const, integral_mul_const, integral_sub,
      integral_div, E.integral_conditionalCDF]
    · simp
    · exact integrable_const _
    · exact (E.integrable_conditionalCDF v).div_const _
    · exact ((integrable_const 1).sub ((E.integrable_conditionalCDF v).div_const _)).mul_const _
    · exact ((E.integrable_conditionalCDF v).div_const _).mul_const _
  calc
    _ ≤ ∫ u : I, L (C.conditionalCDF u v) := by
      apply integral_mono_ae (C.integrable_comp_conditionalCDF v hc) (hi C)
      filter_upwards [hC] with u hu
      have hx : 0 ≤ C.conditionalCDF u v / (H : ℝ) :=
        div_nonneg (C.conditionalCDF_nonneg u v) hp.le
      have hx1 : C.conditionalCDF u v / (H : ℝ) ≤ 1 := (div_le_one hp).mpr hu
      have h := hv.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num) H.property
        (sub_nonneg.mpr hx1) hx (by ring)
      simpa [L, smul_eq_mul, hz] using h
    _ = ∫ u : I, L (D.conditionalCDF u v) := by rw [he, he]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hD] with u hu
      rcases hu with hu | hu <;> simp [L, hu, hz]

theorem schurLE_nelsen7_iff {θ η : I} :
    (nelsen7 θ).SchurLE (nelsen7 η) ↔ η ≤ θ := by
  constructor
  · intro h
    have hx := h.chatterjeeXi_le
    rw [chatterjeeXi_nelsen7, chatterjeeXi_nelsen7] at hx
    change (η : ℝ) ≤ θ
    linarith
  · intro h v φ hc hv
    let H : I := ⟨(η : ℝ) * v + 1 - η, by
      constructor
      · nlinarith [η.property.2, mul_nonneg η.property.1 v.property.1]
      · nlinarith [mul_nonneg η.property.1 (sub_nonneg.mpr v.property.2)]⟩
    apply integral_convex_le_of_conditionalCDF_binary (nelsen7 θ) (nelsen7 η) v H _ _ φ hc hv
    · filter_upwards [conditionalCDF_nelsen7 θ v] with u hu
      rw [hu]
      unfold nelsen7ConditionalCDF
      by_cases hm : u ∈ Ioi (nelsen7Threshold θ v)
      · rw [indicator_of_mem hm]
        dsimp [H]
        have h' : (η : ℝ) ≤ θ := h
        nlinarith [mul_nonneg (sub_nonneg.mpr h') (sub_nonneg.mpr v.property.2)]
      · rw [indicator_of_notMem hm]
        exact H.property.1
    · filter_upwards [conditionalCDF_nelsen7 η v] with u hu
      rw [hu]
      unfold nelsen7ConditionalCDF
      by_cases hm : u ∈ Ioi (nelsen7Threshold η v)
      · exact Or.inr (indicator_of_mem hm _)
      · exact Or.inl (indicator_of_notMem hm _)

theorem schurBothLE_nelsen7_iff {θ η : I} :
    (nelsen7 θ).SchurBothLE (nelsen7 η) ↔ η ≤ θ := by
  rw [schurBothLE_iff_of_exchangeable (isArchimedean_nelsen7 θ).isExchangeable
    (isArchimedean_nelsen7 η).isExchangeable, schurLE_nelsen7_iff]

end ProbabilityTheory.Copula
