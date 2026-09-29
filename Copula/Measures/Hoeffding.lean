/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Measures.Deviation
import Copula.Rank.FGM

/-! # Hoeffding's dependence index

Hoeffding's measure is `Φ²(C) = 90 ∫∫ (C(u,v) - u v)² du dv`
(Nelsen, *An Introduction to Copulas*, 2nd ed., Section 5.3).
We prove `Φ² ≥ 0`, `Φ²(Π) = 0`, invariance under transposition and survival copulas,
`Φ²(C) = 0` if and only if `C = Π`, and `Φ²(FGM θ) = θ² / 10`.

The sharp upper bound `Φ² ≤ 1`, with equality exactly at `M` and `W`, is in `Copula.Measures.Bounds`.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Hoeffding's dependence index `Φ²(C) = 90 ∫∫ (C(u,v) - u v)² du dv`. -/
noncomputable def hoeffdingPhiSq (C : Copula 2) : ℝ :=
  90 * ∫ x, (C.cdf x - (x 0 : ℝ) * (x 1 : ℝ)) ^ 2 ∂(independence 2).toMeasure

theorem hoeffdingPhiSq_nonneg (C : Copula 2) : 0 ≤ C.hoeffdingPhiSq := by
  unfold hoeffdingPhiSq
  exact mul_nonneg (by norm_num) (integral_nonneg fun x => sq_nonneg _)

@[simp] theorem hoeffdingPhiSq_independence : (independence 2).hoeffdingPhiSq = 0 := by
  have hf : ∀ x : Fin 2 → I,
      ((independence 2).cdf x - (x 0 : ℝ) * (x 1 : ℝ)) ^ 2 = 0 := by
    intro x
    rw [cdf_independence_two, sub_self, zero_pow two_ne_zero]
  unfold hoeffdingPhiSq
  simp only [hf, integral_zero, mul_zero]

@[simp] theorem hoeffdingPhiSq_transpose (C : Copula 2) :
    C.transpose.hoeffdingPhiSq = C.hoeffdingPhiSq := by
  unfold hoeffdingPhiSq
  exact congrArg (fun z : ℝ => 90 * z)
    (integral_comp_cdf_sub_transpose (fun t : ℝ => t ^ 2) (by fun_prop) C)

@[simp] theorem hoeffdingPhiSq_survivalCopula (C : Copula 2) :
    C.survivalCopula.hoeffdingPhiSq = C.hoeffdingPhiSq := by
  unfold hoeffdingPhiSq
  exact congrArg (fun z : ℝ => 90 * z)
    (integral_comp_cdf_sub_survival (fun t : ℝ => t ^ 2) (by fun_prop) C)

/-- `Φ²(C) = 0` forces `C` to be the independence copula. -/
theorem eq_independence_of_hoeffdingPhiSq_eq_zero {C : Copula 2} (h : C.hoeffdingPhiSq = 0) :
    C = independence 2 := by
  have h' : (∫ x, (C.cdf x - (x 0 : ℝ) * (x 1 : ℝ)) ^ 2 ∂(independence 2).toMeasure) = 0 := by
    unfold hoeffdingPhiSq at h
    linarith
  exact eq_independence_of_integral_comp_eq_zero (φ := fun t : ℝ => t ^ 2) (C := C)
    (by fun_prop) (fun t => sq_nonneg t) (fun t ht => (pow_eq_zero_iff two_ne_zero).mp ht) h'

/-- Hoeffding's index vanishes exactly at the independence copula. -/
theorem hoeffdingPhiSq_eq_zero_iff (C : Copula 2) :
    C.hoeffdingPhiSq = 0 ↔ C = independence 2 := by
  constructor
  · exact eq_independence_of_hoeffdingPhiSq_eq_zero
  · rintro rfl
    exact hoeffdingPhiSq_independence

/-- Hoeffding's index of the Farlie–Gumbel–Morgenstern copula is `θ² / 10`. -/
theorem hoeffdingPhiSq_fgm (θ : ℝ) (hθ : |θ| ≤ 1) : (fgm θ hθ).hoeffdingPhiSq = θ ^ 2 / 10 := by
  have hf : ∀ x : Fin 2 → I, ((fgm θ hθ).cdf x - (x 0 : ℝ) * (x 1 : ℝ)) ^ 2 =
      θ ^ 2 * (((x 0 : ℝ) ^ 2 * (1 - (x 0 : ℝ)) ^ 2) *
        ((x 1 : ℝ) ^ 2 * (1 - (x 1 : ℝ)) ^ 2)) := by
    intro x
    rw [cdf_fgm]
    unfold fgmCDF
    ring
  unfold hoeffdingPhiSq
  simp only [hf]
  rw [integral_const_mul, integral_independence_mul
    (fun t : I => (t : ℝ) ^ 2 * (1 - (t : ℝ)) ^ 2) (fun t : I => (t : ℝ) ^ 2 * (1 - (t : ℝ)) ^ 2),
    integral_unit_sq_mul_one_sub_sq]
  ring

end ProbabilityTheory.Copula
