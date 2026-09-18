/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Order.SymmetricSchur
import Copula.Rank.FGMChatterjee

/-! # Exact Schur ordering of FGM copulas

Schur order compares absolute parameters. The proof averages a conditional
CDF with its measure-preserving reflection and applies convexity.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem fgmConditionalCDF_le_one (θ : ℝ) (hθ : |θ| ≤ 1) (u v : I) :
    fgmConditionalCDF θ u v ≤ 1 := by
  have h := fgmConditionalCDF_nonneg (-θ) (by simpa only [abs_neg] using hθ)
    u (unitInterval.symm v)
  simp only [fgmConditionalCDF, unitInterval.coe_symm_eq] at h ⊢
  nlinarith

theorem schurLE_fgm_iff {θ η : ℝ} (hθ : |θ| ≤ 1) (hη : |η| ≤ 1) :
    (fgm θ hθ).SchurLE (fgm η hη) ↔ |θ| ≤ |η| := by
  constructor
  · intro h
    have hx := h.chatterjeeXi_le
    rw [chatterjeeXi_fgm, chatterjeeXi_fgm] at hx
    exact sq_le_sq.mp (by linarith)
  · intro h
    by_cases hz : η = 0
    · subst η
      have ht : θ = 0 := abs_eq_zero.mp (le_antisymm (by simpa using h) (abs_nonneg θ))
      subst θ
      exact SchurLE.refl _
    have hr : |θ / η| ≤ 1 := by
      rw [abs_div, div_le_one (abs_pos.mpr hz)]
      exact h
    let a := (1 + θ / η) / 2
    let b := (1 - θ / η) / 2
    have ha : 0 ≤ a := by dsimp [a]; linarith [(abs_le.mp hr).1]
    have hb : 0 ≤ b := by dsimp [b]; linarith [(abs_le.mp hr).2]
    have hab : a + b = 1 := by dsimp [a, b]; ring
    intro v φ hc hv
    have hi (δ : ℝ) (hδ : |δ| ≤ 1) :
        (∫ u : I, φ ((fgm δ hδ).conditionalCDF u v)) =
          ∫ u : I, φ (fgmConditionalCDF δ u v) := by
      apply integral_congr_ae
      filter_upwards [conditionalCDF_fgm δ hδ v] with u hu
      rw [hu]
    rw [hi θ hθ, hi η hη]
    have hcont (δ : ℝ) : Continuous (fun u : I => φ (fgmConditionalCDF δ u v)) :=
      hc.comp (by unfold fgmConditionalCDF; fun_prop)
    have hir : (∫ u : I, φ (fgmConditionalCDF η (unitInterval.symm u) v)) =
        ∫ u : I, φ (fgmConditionalCDF η u v) :=
      unitInterval.measurePreserving_symm.integral_comp
        unitInterval.symmMeasurableEquiv.measurableEmbedding
        (fun u : I => φ (fgmConditionalCDF η u v))
    calc
      _ ≤ ∫ u : I, a * φ (fgmConditionalCDF η u v) +
          b * φ (fgmConditionalCDF η (unitInterval.symm u) v) := by
        apply integral_mono (integrable_continuous_unit volume (hcont θ))
          (integrable_continuous_unit volume (by unfold fgmConditionalCDF; fun_prop))
        intro u
        have hc' := hv.2
          ⟨fgmConditionalCDF_nonneg η hη u v, fgmConditionalCDF_le_one η hη u v⟩
          ⟨fgmConditionalCDF_nonneg η hη (unitInterval.symm u) v,
            fgmConditionalCDF_le_one η hη (unitInterval.symm u) v⟩ ha hb hab
        simp only [smul_eq_mul] at hc'
        have he : a * fgmConditionalCDF η u v +
            b * fgmConditionalCDF η (unitInterval.symm u) v = fgmConditionalCDF θ u v := by
          dsimp [a, b, fgmConditionalCDF]
          field_simp
          ring
        rwa [he] at hc'
      _ = _ := by
        rw [integral_add, integral_const_mul, integral_const_mul, hir]
        · rw [← add_mul, hab, one_mul]
        all_goals exact integrable_continuous_unit volume (by unfold fgmConditionalCDF; fun_prop)

theorem schurBothLE_fgm_iff {θ η : ℝ} (hθ : |θ| ≤ 1) (hη : |η| ≤ 1) :
    (fgm θ hθ).SchurBothLE (fgm η hη) ↔ |θ| ≤ |η| := by
  rw [schurBothLE_iff_of_exchangeable (isExchangeable_fgm θ hθ) (isExchangeable_fgm η hη),
    schurLE_fgm_iff]

end ProbabilityTheory.Copula
