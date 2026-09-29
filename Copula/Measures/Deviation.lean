/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Symmetry
import Copula.Rank.SpearmanCDF
import Copula.CDF.Extensionality
import Copula.UnitInterval

/-! # The deviation `C - Π` of a bivariate copula from independence

Scaffolding for the Schweizer–Wolff measure `σ` and Hoeffding's `Φ²`
(Nelsen, *An Introduction to Copulas*, 2nd ed., Section 5.3). Both are integrals of
a continuous function `φ` of the deviation `C(u,v) - u v` against the uniform
measure on `[0,1]²`. This file collects the common facts: continuity, integrability,
invariance under transposition and survival copulas, the vanishing criterion, and
the link `ρ = 12 ∫∫ (C - Π)` with Spearman's rho (Nelsen Section 5.1.2).
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem cdf_independence_two (x : Fin 2 → I) :
    (independence 2).cdf x = (x 0 : ℝ) * (x 1 : ℝ) := by
  rw [cdf_independence, Fin.prod_univ_two]

theorem integral_independence_coord_mul :
    (∫ x, (x 0 : ℝ) * (x 1 : ℝ) ∂(independence 2).toMeasure) = 1 / 4 := by
  rw [integral_independence_mul, integral_unit_id]
  norm_num

/-- The deviation `C(u,v) - u v` from independence is continuous. -/
theorem continuous_cdf_sub_mul (C : Copula 2) :
    Continuous fun x : Fin 2 → I => C.cdf x - (x 0 : ℝ) * (x 1 : ℝ) :=
  C.continuous_cdf.sub (by fun_prop)

theorem integrable_comp_cdf_sub_mul {φ : ℝ → ℝ} (hφ : Continuous φ) (C : Copula 2)
    (μ : Measure (Fin 2 → I)) [IsFiniteMeasure μ] :
    Integrable (fun x : Fin 2 → I => φ (C.cdf x - (x 0 : ℝ) * (x 1 : ℝ))) μ :=
  integrable_continuous_cube μ (hφ.comp (continuous_cdf_sub_mul C))

/-- The uniform measure on `[0,1]²` is invariant under exchanging the coordinates. -/
theorem integral_independence_swap (f : (Fin 2 → I) → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂(independence 2).toMeasure) =
      ∫ x, f ![x 1, x 0] ∂(independence 2).toMeasure := by
  have hp : (independence 2).transpose = independence 2 := isExchangeable_independence
  have h := (independence 2).integral_transpose f hf
  rw [hp] at h
  exact h

/-- The uniform measure on `[0,1]²` is invariant under `x ↦ 1 - x`. -/
theorem integral_independence_reflect (f : (Fin 2 → I) → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂(independence 2).toMeasure) =
      ∫ x, f (reflectPoint Finset.univ x) ∂(independence 2).toMeasure := by
  have hp : (independence 2).reflect Finset.univ = independence 2 :=
    isRadiallySymmetric_independence
  have h := (independence 2).integral_reflect Finset.univ f hf
  rw [hp] at h
  exact h

/-- Functionals of the deviation `C - Π` are invariant under transposition. -/
theorem integral_comp_cdf_sub_transpose (φ : ℝ → ℝ) (hφ : Continuous φ) (C : Copula 2) :
    (∫ x, φ (C.transpose.cdf x - (x 0 : ℝ) * (x 1 : ℝ)) ∂(independence 2).toMeasure) =
      ∫ x, φ (C.cdf x - (x 0 : ℝ) * (x 1 : ℝ)) ∂(independence 2).toMeasure := by
  have hm : Measurable fun x : Fin 2 → I => φ (C.transpose.cdf x - (x 0 : ℝ) * (x 1 : ℝ)) :=
    (hφ.comp (continuous_cdf_sub_mul C.transpose)).measurable
  rw [integral_independence_swap _ hm]
  apply integral_congr_ae
  filter_upwards with x
  have he : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
  rw [cdf_transpose, he]
  show φ (C.cdf x - ((x 1 : I) : ℝ) * ((x 0 : I) : ℝ)) = φ (C.cdf x - ((x 0 : I) : ℝ) * ((x 1 : I) : ℝ))
  rw [mul_comm ((x 1 : I) : ℝ) ((x 0 : I) : ℝ)]

/-- Functionals of the deviation `C - Π` are invariant under passing to the survival copula. -/
theorem integral_comp_cdf_sub_survival (φ : ℝ → ℝ) (hφ : Continuous φ) (C : Copula 2) :
    (∫ x, φ (C.survivalCopula.cdf x - (x 0 : ℝ) * (x 1 : ℝ)) ∂(independence 2).toMeasure) =
      ∫ x, φ (C.cdf x - (x 0 : ℝ) * (x 1 : ℝ)) ∂(independence 2).toMeasure := by
  have hm : Measurable fun x : Fin 2 → I =>
      φ (C.survivalCopula.cdf x - (x 0 : ℝ) * (x 1 : ℝ)) :=
    (hφ.comp (continuous_cdf_sub_mul C.survivalCopula)).measurable
  rw [integral_independence_reflect _ hm]
  apply integral_congr_ae
  filter_upwards with x
  have he : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
  have hr : reflectPoint Finset.univ x =
      ![unitInterval.symm (x 0), unitInterval.symm (x 1)] := by
    ext i; fin_cases i <;> simp [reflectPoint]
  rw [hr, cdf_survivalCopula]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, unitInterval.symm_symm, he,
    unitInterval.coe_symm_eq]
  congr 1
  ring

/-- If a nonnegative continuous function of the deviation `C - Π` integrates to zero, then
`C` is the independence copula (a continuous nonnegative function that integrates to zero
against a measure with full support vanishes identically). -/
theorem eq_independence_of_integral_comp_eq_zero {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hnn : ∀ t, 0 ≤ φ t) (hz : ∀ t, φ t = 0 → t = 0) {C : Copula 2}
    (h : (∫ x, φ (C.cdf x - (x 0 : ℝ) * (x 1 : ℝ)) ∂(independence 2).toMeasure) = 0) :
    C = independence 2 := by
  have : (independence 2).toMeasure.IsOpenPosMeasure := by
    rw [toMeasure_independence]
    infer_instance
  have hc : Continuous fun x : Fin 2 → I => φ (C.cdf x - (x 0 : ℝ) * (x 1 : ℝ)) :=
    hφ.comp (continuous_cdf_sub_mul C)
  have hae := (integral_eq_zero_iff_of_nonneg
    (f := fun x : Fin 2 → I => φ (C.cdf x - (x 0 : ℝ) * (x 1 : ℝ)))
    (fun x => hnn _) (integrable_comp_cdf_sub_mul hφ C (independence 2).toMeasure)).mp h
  have hae' : ∀ᵐ x ∂(independence 2).toMeasure,
      φ (C.cdf x - (x 0 : ℝ) * (x 1 : ℝ)) = 0 := by
    filter_upwards [hae] with x hx
    exact hx
  have heq := (Continuous.ae_eq_iff_eq (independence 2).toMeasure hc
    (continuous_const : Continuous (fun _ : Fin 2 → I => (0 : ℝ)))).mp hae'
  apply ext_cdf
  intro x
  have hx : φ (C.cdf x - (x 0 : ℝ) * (x 1 : ℝ)) = 0 := congrFun heq x
  have hx' := hz _ hx
  rw [cdf_independence_two]
  linarith

/-- Spearman's rho as a multiple of the integral of `C - Π` (Nelsen Section 5.1.2). -/
theorem spearmanRho_eq_twelve_integral_cdf_sub (C : Copula 2) :
    C.spearmanRho =
      12 * ∫ x, (C.cdf x - (x 0 : ℝ) * (x 1 : ℝ)) ∂(independence 2).toMeasure := by
  have hp : Integrable (fun x : Fin 2 → I => (x 0 : ℝ) * (x 1 : ℝ))
      (independence 2).toMeasure := integrable_continuous_cube _ (by fun_prop)
  rw [integral_sub (C.integrable_cdf (independence 2).toMeasure) hp,
    integral_independence_coord_mul, spearmanRho_eq_integral_cdf]
  ring

end ProbabilityTheory.Copula
