/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Order.Survival
import Copula.Dependence.Transpose

/-! # Bivariate reflections and survival copulas -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem ext_cdf_two {C D : Copula 2} (h : ∀ u v : I, C.cdf ![u, v] = D.cdf ![u, v]) : C = D := by
  apply ext_cdf
  intro x
  have he : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
  simpa only [he] using h (x 0) (x 1)

/-- Transposition exchanges the two coordinates. -/
noncomputable def transpose (C : Copula 2) : Copula 2 := C.reindex ![1, 0]

/-- The survival copula, obtained by reflecting every coordinate. -/
noncomputable def survivalCopula {d : ℕ} (C : Copula d) : Copula d := C.reflect Finset.univ

@[simp] theorem transpose_transpose (C : Copula 2) : C.transpose.transpose = C :=
  reindex_swap_swap C

@[simp] theorem survivalCopula_survivalCopula {d : ℕ} (C : Copula d) :
    C.survivalCopula.survivalCopula = C := C.reflect_reflect _

@[simp] theorem cdf_transpose (C : Copula 2) (u v : I) :
    C.transpose.cdf ![u, v] = C.cdf ![v, u] := cdf_reindex_swap C u v

/-- The usual bivariate survival-copula formula. -/
theorem cdf_survivalCopula (C : Copula 2) (u v : I) :
    C.survivalCopula.cdf ![u, v] =
      (u : ℝ) + (v : ℝ) - 1 + C.cdf ![unitInterval.symm u, unitInterval.symm v] := by
  have h := C.survival_eq_cdf_reflect ![unitInterval.symm u, unitInterval.symm v]
  have he : reflectPoint Finset.univ ![unitInterval.symm u, unitInterval.symm v] = ![u, v] := by
    ext i; fin_cases i <;> simp [reflectPoint]
  rw [he, C.survival_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, unitInterval.coe_symm_eq] at h
  unfold survivalCopula
  linarith

theorem cdf_reflect_first (C : Copula 2) (u v : I) :
    (C.reflect {0}).cdf ![u, v] = (v : ℝ) - C.cdf ![unitInterval.symm u, v] := by
  rw [cdf, toMeasure_reflect, map_measureReal_apply (measurable_reflectPoint _) measurableSet_Iic]
  have ha : reflectPoint {0} ⁻¹' Iic ![u, v] =ᵐ[C.toMeasure]
      {x : Fin 2 → I | x 1 ≤ v} \ Iic ![unitInterval.symm u, v] := by
    filter_upwards [C.ae_eval_ne 0 (unitInterval.symm u)] with x hx
    apply propext
    simp only [mem_preimage, mem_Iic, Pi.le_def, Fin.forall_fin_two,
      reflectPoint, Finset.mem_singleton, Matrix.cons_val_zero, Matrix.cons_val_one,
      ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false, mem_sdiff, mem_ofPred_eq,
      unitInterval.symm_le_comm]
    constructor
    · rintro ⟨h₀, h₁⟩
      exact ⟨h₁, fun h => hx (le_antisymm h.1 h₀)⟩
    · rintro ⟨h₁, h⟩
      exact ⟨le_of_lt (lt_of_not_ge fun h₀ => h ⟨h₀, h₁⟩), h₁⟩
  rw [show C.toMeasure.real (reflectPoint {0} ⁻¹' Iic ![u, v]) =
      C.toMeasure.real ({x : Fin 2 → I | x 1 ≤ v} \ Iic ![unitInterval.symm u, v]) from
    congrArg ENNReal.toReal (measure_congr ha)]
  have hs : Iic ![unitInterval.symm u, v] ⊆ {x : Fin 2 → I | x 1 ≤ v} := fun _ hx => hx 1
  rw [measureReal_sdiff hs measurableSet_Iic, C.measureReal_eval_le]
  rfl

theorem transpose_reflect_first (C : Copula 2) :
    (C.reflect {0}).transpose = C.transpose.reflect {1} := by
  apply ext
  simp only [transpose, toMeasure_reindex, toMeasure_reflect]
  have hm : Measurable (fun x : Fin 2 → I => fun i => x (![1, 0] i)) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  rw [Measure.map_map hm (measurable_reflectPoint _),
    Measure.map_map (measurable_reflectPoint _) hm]
  congr 1
  ext x i
  fin_cases i <;> simp [reflectPoint]

theorem cdf_reflect_second (C : Copula 2) (u v : I) :
    (C.reflect {1}).cdf ![u, v] = (u : ℝ) - C.cdf ![u, unitInterval.symm v] := by
  have h := C.transpose.cdf_reflect_first v u
  rw [← cdf_transpose, transpose_reflect_first, transpose_transpose, cdf_transpose] at h
  exact h

theorem reflect_first_second (C : Copula 2) :
    (C.reflect {0}).reflect {1} = C.survivalCopula := by
  apply ext
  simp only [survivalCopula, toMeasure_reflect]
  rw [Measure.map_map (measurable_reflectPoint _) (measurable_reflectPoint _)]
  congr 1
  ext x i
  fin_cases i <;> simp [reflectPoint]

end ProbabilityTheory.Copula
