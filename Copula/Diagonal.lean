/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Integration
import Copula.CDF.Extensionality

/-! # Diagonal sections of bivariate copulas

Necessary diagonal conditions and the characterization of the upper Fréchet
copula by its diagonal (Nelsen, second edition, §3.2.6 and Exercise 2.8).
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The diagonal section of a bivariate copula. -/
noncomputable def diagonal (C : Copula 2) (t : I) : ℝ := C.cdf ![t, t]

@[simp] theorem diagonal_zero (C : Copula 2) : C.diagonal 0 = 0 := by
  exact C.cdf_eq_zero_of_coord_eq_zero _ 0 rfl

@[simp] theorem diagonal_one (C : Copula 2) : C.diagonal 1 = 1 := by
  have he : ![(1 : I), 1] = fun _ : Fin 2 => (1 : I) := by ext i; fin_cases i <;> rfl
  rw [diagonal, he, C.cdf_one]

theorem diagonal_nonneg (C : Copula 2) (t : I) : 0 ≤ C.diagonal t := C.cdf_nonneg _

theorem diagonal_le (C : Copula 2) (t : I) : C.diagonal t ≤ (t : ℝ) :=
  C.cdf_le_coord _ 0

theorem diagonal_lower_bound (C : Copula 2) (t : I) :
    max 0 (2 * (t : ℝ) - 1) ≤ C.diagonal t := by
  have h := C.sum_sub_dim_add_one_le_cdf ![t, t]
  norm_num [Fin.sum_univ_two] at h
  exact max_le (C.diagonal_nonneg t) (by unfold diagonal; linarith)

theorem monotone_diagonal (C : Copula 2) : Monotone C.diagonal := by
  intro s t h
  apply C.monotone_cdf
  intro i
  fin_cases i <;> exact h

theorem abs_diagonal_sub_le (C : Copula 2) (s t : I) :
    |C.diagonal s - C.diagonal t| ≤ 2 * |(s : ℝ) - (t : ℝ)| := by
  simpa [diagonal, Fin.sum_univ_two, two_mul] using C.abs_cdf_sub_le_sum_abs ![s, s] ![t, t]

theorem lipschitzWith_diagonal (C : Copula 2) : LipschitzWith 2 C.diagonal := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simpa only [Real.dist_eq, Subtype.dist_eq, NNReal.coe_ofNat] using C.abs_diagonal_sub_le s t

@[fun_prop] theorem continuous_diagonal (C : Copula 2) : Continuous C.diagonal :=
  C.lipschitzWith_diagonal.continuous

theorem diagonal_sub_mem_Icc (C : Copula 2) {s t : I} (h : s ≤ t) :
    C.diagonal t - C.diagonal s ∈ Set.Icc 0 (2 * ((t : ℝ) - (s : ℝ))) := by
  have hd := C.monotone_diagonal h
  have hb := C.abs_diagonal_sub_le t s
  rw [abs_of_nonneg (sub_nonneg.mpr hd),
    abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ (t : ℝ) from h))] at hb
  exact ⟨sub_nonneg.mpr hd, hb⟩

@[simp] theorem diagonal_independence (t : I) : (independence 2).diagonal t = (t : ℝ) ^ 2 := by
  simp [diagonal, Fin.prod_univ_two, pow_two]

@[simp] theorem diagonal_comonotonic (t : I) : (comonotonic 2).diagonal t = (t : ℝ) := by
  unfold diagonal
  rw [cdf_comonotonic_two]
  simp

@[simp] theorem diagonal_countermonotonic (t : I) :
    countermonotonic.diagonal t = max 0 (2 * (t : ℝ) - 1) := by
  simp [diagonal, two_mul]

/-- The upper Fréchet copula is determined by its diagonal. -/
theorem diagonal_eq_id_iff (C : Copula 2) :
    (∀ t : I, C.diagonal t = (t : ℝ)) ↔ C = comonotonic 2 := by
  refine ⟨fun h => ?_, fun h => h ▸ diagonal_comonotonic⟩
  apply ext_cdf
  intro u
  rw [cdf_comonotonic_two]
  apply le_antisymm (le_min (C.cdf_le_coord u 0) (C.cdf_le_coord u 1))
  change ((min (u 0) (u 1) : I) : ℝ) ≤ C.cdf u
  rw [← h (min (u 0) (u 1))]
  apply C.monotone_cdf
  intro i
  fin_cases i
  · exact min_le_left _ _
  · exact min_le_right _ _

/-- The diagonal is the distribution function of the maximum of the two coordinates. -/
theorem measureReal_max_le (C : Copula 2) (t : I) :
    C.toMeasure.real {x | max (x 0) (x 1) ≤ t} = C.diagonal t := by
  have he : {x : Fin 2 → I | max (x 0) (x 1) ≤ t} = Iic ![t, t] := by
    ext x
    simp [Pi.le_def, Fin.forall_fin_two]
  rw [he]
  rfl

/-- The complementary diagonal formula gives the distribution function of the minimum. -/
theorem measureReal_min_le (C : Copula 2) (t : I) :
    C.toMeasure.real {x | min (x 0) (x 1) ≤ t} = 2 * (t : ℝ) - C.diagonal t := by
  have hu : {x : Fin 2 → I | x 0 ≤ t} ∪ {x | x 1 ≤ t} =
      {x | min (x 0) (x 1) ≤ t} := by ext x; simp [min_le_iff]
  have hi : {x : Fin 2 → I | x 0 ≤ t} ∩ {x | x 1 ≤ t} = Iic ![t, t] := by
    ext x
    simp [Pi.le_def, Fin.forall_fin_two]
  have h := measureReal_union_add_inter (μ := C.toMeasure)
    (s := {x : Fin 2 → I | x 0 ≤ t}) (t := {x | x 1 ≤ t})
    (measurableSet_le (measurable_pi_apply 1) measurable_const)
  rw [hu, hi, C.measureReal_eval_le, C.measureReal_eval_le] at h
  change C.toMeasure.real {x | min (x 0) (x 1) ≤ t} + C.diagonal t = (t : ℝ) + (t : ℝ) at h
  linarith

end ProbabilityTheory.Copula
