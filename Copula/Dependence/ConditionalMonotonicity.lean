/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.Examples
import Copula.Dependence.FGM
import Copula.Archimedean.Symmetry

/-! # Conditional increasingness and decreasingness in both directions

The CI/CD terminology follows Ansari–Rockel, Definition 2.5. `IsSI` is
directional CIS; `IsSD` is its convex-section counterpart, CDS.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Stochastic decreasingness of the second coordinate given the first. -/
def IsSD (C : Copula 2) : Prop :=
  ∀ a b c v : I, a ≤ b → b ≤ c →
    ((c : ℝ) - (a : ℝ)) * C.cdf ![b, v] ≤
      ((b : ℝ) - (a : ℝ)) * C.cdf ![c, v] +
        ((c : ℝ) - (b : ℝ)) * C.cdf ![a, v]

/-- Conditional increasingness in both coordinate directions. -/
def IsCI (C : Copula 2) : Prop := C.IsSI ∧ C.transpose.IsSI

/-- Conditional decreasingness in both coordinate directions. -/
def IsCD (C : Copula 2) : Prop := C.IsSD ∧ C.transpose.IsSD

theorem IsSD.isNQD {C : Copula 2} (h : C.IsSD) : C.IsNQD := by
  intro u v
  simpa using h 0 u 1 v u.property.1 u.property.2

theorem IsCI.isSI {C : Copula 2} (h : C.IsCI) : C.IsSI := h.1
theorem IsCD.isSD {C : Copula 2} (h : C.IsCD) : C.IsSD := h.1
theorem IsCI.isPQD {C : Copula 2} (h : C.IsCI) : C.IsPQD := h.1.isPQD
theorem IsCD.isNQD {C : Copula 2} (h : C.IsCD) : C.IsNQD := h.1.isNQD

@[simp] theorem isCI_transpose_iff (C : Copula 2) : C.transpose.IsCI ↔ C.IsCI := by
  simp only [IsCI, transpose_transpose, and_comm]

@[simp] theorem isCD_transpose_iff (C : Copula 2) : C.transpose.IsCD ↔ C.IsCD := by
  simp only [IsCD, transpose_transpose, and_comm]

theorem IsExchangeable.isCI_iff {C : Copula 2} (h : C.IsExchangeable) : C.IsCI ↔ C.IsSI := by
  change C.transpose = C at h
  simp only [IsCI, h, and_self]

theorem IsExchangeable.isCD_iff {C : Copula 2} (h : C.IsExchangeable) : C.IsCD ↔ C.IsSD := by
  change C.transpose = C at h
  simp only [IsCD, h, and_self]

theorem IsArchimedean.isCI_iff {C : Copula 2} (h : C.IsArchimedean) : C.IsCI ↔ C.IsSI :=
  h.isExchangeable.isCI_iff

theorem IsArchimedean.isCD_iff {C : Copula 2} (h : C.IsArchimedean) : C.IsCD ↔ C.IsSD :=
  h.isExchangeable.isCD_iff

theorem isSI_reflect_second_iff (C : Copula 2) : (C.reflect {1}).IsSI ↔ C.IsSD := by
  constructor
  · intro h a b c v hab hbc
    have ht := h a b c (unitInterval.symm v) hab hbc
    simp only [cdf_reflect_second, unitInterval.symm_symm] at ht
    nlinarith
  · intro h a b c v hab hbc
    have ht := h a b c (unitInterval.symm v) hab hbc
    simp only [cdf_reflect_second]
    nlinarith

theorem isSD_reflect_second_iff (C : Copula 2) : (C.reflect {1}).IsSD ↔ C.IsSI := by
  rw [← isSI_reflect_second_iff, reflect_reflect]

theorem isSD_independence : (independence 2).IsSD := by
  intro a b c v _ _
  simp only [cdf_independence, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring_nf
  exact le_rfl

theorem isCI_independence : (independence 2).IsCI :=
  isExchangeable_independence.isCI_iff.mpr isSI_independence

theorem isCD_independence : (independence 2).IsCD :=
  isExchangeable_independence.isCD_iff.mpr isSD_independence

theorem isCI_comonotonic : (comonotonic 2).IsCI :=
  isExchangeable_comonotonic.isCI_iff.mpr isSI_comonotonic

theorem isSD_countermonotonic : countermonotonic.IsSD := by
  rw [← reflect_comonotonic_eq_countermonotonic, isSD_reflect_second_iff]
  exact isSI_comonotonic

theorem isCD_countermonotonic : countermonotonic.IsCD :=
  isExchangeable_countermonotonic.isCD_iff.mpr isSD_countermonotonic

theorem isSD_fgm (θ : ℝ) (hθ : |θ| ≤ 1) (hneg : θ ≤ 0) : (fgm θ hθ).IsSD := by
  intro a b c v hab hbc
  have hab' : 0 ≤ (b : ℝ) - (a : ℝ) := sub_nonneg.mpr hab
  have hbc' : 0 ≤ (c : ℝ) - (b : ℝ) := sub_nonneg.mpr hbc
  have hac' : 0 ≤ (c : ℝ) - (a : ℝ) := by linarith
  have hn := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (neg_nonneg.mpr hneg)
    v.property.1) (sub_nonneg.mpr v.property.2)) hab') hbc') hac'
  simp only [cdf_fgm, Matrix.cons_val_zero, Matrix.cons_val_one, fgmCDF]
  nlinarith

theorem isSD_fgm_iff (θ : ℝ) (hθ : |θ| ≤ 1) : (fgm θ hθ).IsSD ↔ θ ≤ 0 := by
  constructor
  · intro h
    have ht := h.isNQD unitHalf unitHalf
    norm_num [cdf_fgm, fgmCDF, unitHalf] at ht
    linarith
  · exact isSD_fgm θ hθ

theorem isCI_fgm_iff (θ : ℝ) (hθ : |θ| ≤ 1) : (fgm θ hθ).IsCI ↔ 0 ≤ θ := by
  rw [(isExchangeable_fgm θ hθ).isCI_iff, isSI_fgm_iff]

theorem isCD_fgm_iff (θ : ℝ) (hθ : |θ| ≤ 1) : (fgm θ hθ).IsCD ↔ θ ≤ 0 := by
  rw [(isExchangeable_fgm θ hθ).isCD_iff, isSD_fgm_iff]

end ProbabilityTheory.Copula
