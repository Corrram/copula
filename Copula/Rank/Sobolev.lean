/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.ChatterjeeMixture
import Copula.Rank.ConditionalDerivative
import Copula.Rank.FGMChatterjee
import Copula.Rearrangement
import Copula.Symmetry
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Sobolev energy and the Siburg–Stoimenov dependence coefficient

The squared modified Sobolev norm is the sum of the two directional conditional
CDF energies. The derivative representation is proved without a density
assumption. Siburg–Stoimenov's coefficient is `sqrt (3 * energy - 2)`; its square
equals the average of the two directional Chatterjee coefficients.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Squared modified Sobolev norm: the integrated squares of both first partials. -/
noncomputable def sobolevNormSq (C : Copula 2) : ℝ :=
  (∫ v : I, ∫ u : I, C.conditionalCDF u v ^ 2) +
    ∫ v : I, ∫ u : I, C.transpose.conditionalCDF u v ^ 2

/-- The modified Sobolev norm of a bivariate copula. -/
noncomputable def sobolevNorm (C : Copula 2) : ℝ := Real.sqrt C.sobolevNormSq

/-- Squared Sobolev distance, using both directional conditional distributions. -/
noncomputable def sobolevDistanceSq (C D : Copula 2) : ℝ :=
  C.conditionalCDFDistanceSq D + C.transpose.conditionalCDFDistanceSq D.transpose

/-- Squared Siburg–Stoimenov dependence coefficient. -/
noncomputable def sobolevDependenceSq (C : Copula 2) : ℝ := 3 * C.sobolevNormSq - 2

/-- Siburg–Stoimenov's normalized Sobolev dependence coefficient `ω`. -/
noncomputable def sobolevDependence (C : Copula 2) : ℝ := Real.sqrt C.sobolevDependenceSq

theorem sobolevNormSq_eq_integral_deriv (C : Copula 2) :
    C.sobolevNormSq = (∫ v : I, ∫ u : I, deriv (C.cdfSection v) (u : ℝ) ^ 2) +
      ∫ v : I, ∫ u : I, deriv (C.transpose.cdfSection v) (u : ℝ) ^ 2 := by
  have h (D : Copula 2) : (∫ v : I, ∫ u : I, D.conditionalCDF u v ^ 2) =
      ∫ v : I, ∫ u : I, deriv (D.cdfSection v) (u : ℝ) ^ 2 := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun v => integral_congr_ae (by
      filter_upwards [D.conditionalCDF_eq_deriv v] with u hu
      rw [hu]))
  exact congrArg₂ (· + ·) (h C) (h C.transpose)

theorem sobolevDependenceSq_eq_chatterjeeXi (C : Copula 2) :
    C.sobolevDependenceSq = (C.chatterjeeXi + C.transpose.chatterjeeXi) / 2 := by
  unfold sobolevDependenceSq sobolevNormSq chatterjeeXi
  ring

theorem sobolevDependenceSq_mem_Icc (C : Copula 2) : C.sobolevDependenceSq ∈ Icc 0 1 := by
  rw [C.sobolevDependenceSq_eq_chatterjeeXi]
  constructor <;> linarith [C.chatterjeeXi_nonneg, C.transpose.chatterjeeXi_nonneg,
    C.chatterjeeXi_le_one, C.transpose.chatterjeeXi_le_one]

theorem sobolevNormSq_mem_Icc (C : Copula 2) : C.sobolevNormSq ∈ Icc (2 / 3) 1 := by
  have h := C.sobolevDependenceSq_mem_Icc
  unfold sobolevDependenceSq at h
  constructor <;> linarith [h.1, h.2]

theorem sobolevDependence_mem_Icc (C : Copula 2) : C.sobolevDependence ∈ Icc 0 1 := by
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  exact (Real.sqrt_le_one).2 C.sobolevDependenceSq_mem_Icc.2

theorem sobolevNorm_sq (C : Copula 2) : C.sobolevNorm ^ 2 = C.sobolevNormSq :=
  Real.sq_sqrt (by linarith [C.sobolevNormSq_mem_Icc.1])

theorem sobolevDependence_sq (C : Copula 2) : C.sobolevDependence ^ 2 = C.sobolevDependenceSq :=
  Real.sq_sqrt C.sobolevDependenceSq_mem_Icc.1

@[simp] theorem sobolevNormSq_transpose (C : Copula 2) : C.transpose.sobolevNormSq = C.sobolevNormSq := by
  simp only [sobolevNormSq, transpose_transpose, add_comm]

@[simp] theorem sobolevDependence_transpose (C : Copula 2) :
    C.transpose.sobolevDependence = C.sobolevDependence := by
  simp only [sobolevDependence, sobolevDependenceSq, sobolevNormSq_transpose]

theorem sobolevDistanceSq_nonneg (C D : Copula 2) : 0 ≤ C.sobolevDistanceSq D :=
  add_nonneg (C.conditionalCDFDistanceSq_nonneg D) (C.transpose.conditionalCDFDistanceSq_nonneg _)

theorem sobolevDistanceSq_comm (C D : Copula 2) : C.sobolevDistanceSq D = D.sobolevDistanceSq C := by
  simp only [sobolevDistanceSq, conditionalCDFDistanceSq_comm]

@[simp] theorem sobolevDistanceSq_self (C : Copula 2) : C.sobolevDistanceSq C = 0 := by
  simp only [sobolevDistanceSq, conditionalCDFDistanceSq_self, add_zero]

theorem sobolevDistanceSq_eq_zero_iff (C D : Copula 2) : C.sobolevDistanceSq D = 0 ↔ C = D := by
  constructor
  · intro h
    apply (C.conditionalCDFDistanceSq_eq_zero_iff D).1
    unfold sobolevDistanceSq at h
    linarith [C.conditionalCDFDistanceSq_nonneg D, C.transpose.conditionalCDFDistanceSq_nonneg D.transpose]
  · rintro rfl
    exact sobolevDistanceSq_self C

theorem sobolevDependenceSq_eq_distance_independence (C : Copula 2) :
    C.sobolevDependenceSq = 3 * C.sobolevDistanceSq (independence 2) := by
  rw [C.sobolevDependenceSq_eq_chatterjeeXi,
    C.chatterjeeXi_eq_distance_independence, C.transpose.chatterjeeXi_eq_distance_independence]
  unfold sobolevDistanceSq
  rw [show (independence 2).transpose = independence 2 from isExchangeable_independence]
  ring

theorem sobolevDependence_eq_zero_iff (C : Copula 2) : C.sobolevDependence = 0 ↔ C = independence 2 := by
  rw [sobolevDependence, Real.sqrt_eq_zero C.sobolevDependenceSq_mem_Icc.1,
    C.sobolevDependenceSq_eq_distance_independence]
  simp [sobolevDistanceSq_eq_zero_iff]

theorem sobolevDependence_eq_one_iff (C : Copula 2) :
    C.sobolevDependence = 1 ↔ C.chatterjeeXi = 1 ∧ C.transpose.chatterjeeXi = 1 := by
  rw [sobolevDependence, Real.sqrt_eq_one, C.sobolevDependenceSq_eq_chatterjeeXi]
  constructor
  · intro h
    constructor <;> linarith [C.chatterjeeXi_le_one, C.transpose.chatterjeeXi_le_one]
  · rintro ⟨hC, ht⟩
    rw [hC, ht]
    norm_num

theorem IsMutuallyCompletelyDependent.sobolevDependence_eq_one {C : Copula 2}
    (h : C.IsMutuallyCompletelyDependent) : C.sobolevDependence = 1 :=
  C.sobolevDependence_eq_one_iff.mpr ⟨h.1.chatterjeeXi_eq_one, h.2.chatterjeeXi_eq_one⟩

@[simp] theorem sobolevDependence_independence : (independence 2).sobolevDependence = 0 :=
  (sobolevDependence_eq_zero_iff _).2 rfl

@[simp] theorem sobolevDependence_comonotonic : (comonotonic 2).sobolevDependence = 1 := by
  apply (sobolevDependence_eq_one_iff _).2
  rw [show (comonotonic 2).transpose = comonotonic 2 from isExchangeable_comonotonic]
  simp

@[simp] theorem sobolevDependence_countermonotonic : countermonotonic.sobolevDependence = 1 := by
  apply (sobolevDependence_eq_one_iff _).2
  rw [show countermonotonic.transpose = countermonotonic from isExchangeable_countermonotonic]
  simp

theorem sobolevDependenceSq_mix_independence (C : Copula 2) (a : I) :
    (C.mix (independence 2) a).sobolevDependenceSq = (a : ℝ) ^ 2 * C.sobolevDependenceSq := by
  simp only [sobolevDependenceSq_eq_chatterjeeXi, transpose_mix,
    show (independence 2).transpose = independence 2 from isExchangeable_independence,
    chatterjeeXi_mix_independence]
  ring

theorem sobolevDependence_mix_independence (C : Copula 2) (a : I) :
    (C.mix (independence 2) a).sobolevDependence = (a : ℝ) * C.sobolevDependence := by
  rw [sobolevDependence, sobolevDependenceSq_mix_independence,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq a.property.1]
  rfl

theorem sobolevDependenceSq_fgm (θ : ℝ) (hθ : |θ| ≤ 1) :
    (fgm θ hθ).sobolevDependenceSq = θ ^ 2 / 15 := by
  rw [sobolevDependenceSq_eq_chatterjeeXi, show (fgm θ hθ).transpose = fgm θ hθ from isExchangeable_fgm θ hθ,
    chatterjeeXi_fgm]
  ring

end ProbabilityTheory.Copula
