/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Reflection.Bivariate
import Copula.Rank.Basic
import Copula.Families.FGM

/-! # Exchangeability, radial symmetry and symmetrization

Copula-level symmetries as in Nelsen, second edition, §2.7.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Exchangeability of the two uniform coordinates. -/
def IsExchangeable (C : Copula 2) : Prop := C.transpose = C

/-- Invariance under simultaneous reflection of both coordinates. -/
def IsRadiallySymmetric (C : Copula 2) : Prop := C.survivalCopula = C

theorem isExchangeable_iff (C : Copula 2) :
    C.IsExchangeable ↔ ∀ u v : I, C.cdf ![u, v] = C.cdf ![v, u] := by
  constructor
  · intro h u v
    have he := C.cdf_transpose u v
    rw [h] at he
    exact he
  · intro h
    apply ext_cdf_two
    intro u v
    rw [cdf_transpose, h]

theorem isRadiallySymmetric_iff (C : Copula 2) :
    C.IsRadiallySymmetric ↔ ∀ u v : I, C.cdf ![u, v] =
      (u : ℝ) + (v : ℝ) - 1 + C.cdf ![unitInterval.symm u, unitInterval.symm v] := by
  constructor
  · intro h u v
    have he := C.cdf_survivalCopula u v
    rw [h] at he
    exact he
  · intro h
    apply ext_cdf_two
    intro u v
    rw [cdf_survivalCopula, ← h]

theorem transpose_survivalCopula (C : Copula 2) :
    C.survivalCopula.transpose = C.transpose.survivalCopula := by
  apply ext_cdf_two
  intro u v
  rw [cdf_transpose, cdf_survivalCopula, cdf_survivalCopula, cdf_transpose]
  ring

theorem transpose_mix (C D : Copula 2) (a : I) :
    (C.mix D a).transpose = C.transpose.mix D.transpose a := by
  apply ext_cdf_two
  intro u v
  simp

theorem survivalCopula_mix (C D : Copula 2) (a : I) :
    (C.mix D a).survivalCopula = C.survivalCopula.mix D.survivalCopula a := by
  apply ext_cdf_two
  intro u v
  simp only [cdf_survivalCopula, cdf_mix]
  ring

theorem IsExchangeable.mix {C D : Copula 2} (hC : C.IsExchangeable)
    (hD : D.IsExchangeable) (a : I) : (C.mix D a).IsExchangeable := by
  unfold IsExchangeable at *
  rw [transpose_mix, hC, hD]

theorem IsRadiallySymmetric.mix {C D : Copula 2} (hC : C.IsRadiallySymmetric)
    (hD : D.IsRadiallySymmetric) (a : I) : (C.mix D a).IsRadiallySymmetric := by
  unfold IsRadiallySymmetric at *
  rw [survivalCopula_mix, hC, hD]

/-- Averaging a copula with its transpose produces an exchangeable copula. -/
theorem isExchangeable_symmetrize (C : Copula 2) : (C.mix C.transpose unitHalf).IsExchangeable := by
  rw [isExchangeable_iff]
  intro u v
  simp only [cdf_mix, cdf_transpose, unitHalf]
  ring

/-- Averaging with the survival copula produces radial symmetry. -/
theorem isRadiallySymmetric_symmetrize (C : Copula 2) :
    (C.mix C.survivalCopula unitHalf).IsRadiallySymmetric := by
  unfold IsRadiallySymmetric
  rw [survivalCopula_mix, survivalCopula_survivalCopula]
  apply ext_cdf_two
  intro u v
  simp only [cdf_mix, unitHalf]
  ring

theorem isExchangeable_fgm (θ : ℝ) (hθ : |θ| ≤ 1) : (fgm θ hθ).IsExchangeable := by
  rw [isExchangeable_iff]
  intro u v
  simp only [cdf_fgm, Matrix.cons_val_zero, Matrix.cons_val_one, fgmCDF]
  ring

theorem isRadiallySymmetric_fgm (θ : ℝ) (hθ : |θ| ≤ 1) : (fgm θ hθ).IsRadiallySymmetric := by
  rw [isRadiallySymmetric_iff]
  intro u v
  simp only [cdf_fgm, Matrix.cons_val_zero, Matrix.cons_val_one, fgmCDF, unitInterval.coe_symm_eq]
  ring

theorem isExchangeable_independence : (independence 2).IsExchangeable := by
  simpa only [fgm_zero] using isExchangeable_fgm 0 (by norm_num)

theorem isRadiallySymmetric_independence : (independence 2).IsRadiallySymmetric := by
  simpa only [fgm_zero] using isRadiallySymmetric_fgm 0 (by norm_num)

theorem isExchangeable_comonotonic : (comonotonic 2).IsExchangeable := by
  rw [isExchangeable_iff]
  intro u v
  simp only [cdf_comonotonic_two, Matrix.cons_val_zero, Matrix.cons_val_one, min_comm]

theorem isRadiallySymmetric_comonotonic : (comonotonic 2).IsRadiallySymmetric := by
  rw [isRadiallySymmetric_iff]
  intro u v
  simp only [cdf_comonotonic_two, Matrix.cons_val_zero, Matrix.cons_val_one, unitInterval.coe_symm_eq]
  rcases le_total (u : ℝ) (v : ℝ) with h | h
  · rw [min_eq_left h, min_eq_right (sub_le_sub_left h 1)]
    ring
  · rw [min_eq_right h, min_eq_left (sub_le_sub_left h 1)]
    ring

theorem isExchangeable_countermonotonic : countermonotonic.IsExchangeable := by
  rw [isExchangeable_iff]
  intro u v
  simp [add_comm]

theorem isRadiallySymmetric_countermonotonic : countermonotonic.IsRadiallySymmetric := by
  rw [isRadiallySymmetric_iff]
  intro u v
  simp only [cdf_countermonotonic, Matrix.cons_val_zero, Matrix.cons_val_one, unitInterval.coe_symm_eq]
  by_cases h : (u : ℝ) + (v : ℝ) ≤ 1
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    ring

end ProbabilityTheory.Copula
