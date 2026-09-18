/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Exponential
import Copula.Archimedean.Truncated
import Copula.Dependence.ConditionalMonotonicity
import Copula.Order.Orthant

/-! # Nelsen's seventh family

The parameter runs from countermonotonicity at zero to independence at one.
Its CDF has a zero region, so no positive-density hypothesis is imposed.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem nelsen7_arg_pos (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1)
    (u : I) (hu : u ≠ 0) : 0 < θ * (u : ℝ) + 1 - θ := by
  have hp : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1
    (Ne.symm (fun h => hu (Subtype.ext h)))
  nlinarith [mul_pos hθ hp]

/-- A finite-zero exponential generator, with its linear limiting case handled
separately by `nelsen7`. -/
noncomputable def nelsen7Generator (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    BivariateGenerator where
  toFun t := max 0 ((Real.exp (-t) + θ - 1) / θ)
  invFun u := -Real.log (θ * (u : ℝ) + 1 - θ)
  nonneg _ _ := le_max_left _ _
  antitone _ _ _ _ h := max_le_max le_rfl (div_le_div_of_nonneg_right
    (by linarith [Real.exp_le_exp.mpr (neg_le_neg h)]) hθ.le)
  convex := by
    refine ⟨convex_Ici _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hc := exponentialGenerator.convex.2 hx hy ha hb hab
    change Real.exp (-(a • x + b • y)) ≤ a • Real.exp (-x) + b • Real.exp (-y) at hc
    simp only [smul_eq_mul] at hc ⊢
    apply max_le
    · positivity
    · apply (div_le_iff₀ hθ).mpr
      have hx' := (div_le_iff₀ hθ).mp
        (le_max_right 0 ((Real.exp (-x) + θ - 1) / θ))
      have hy' := (div_le_iff₀ hθ).mp
        (le_max_right 0 ((Real.exp (-y) + θ - 1) / θ))
      nlinarith [mul_le_mul_of_nonneg_left hx' ha, mul_le_mul_of_nonneg_left hy' hb]
  inv_nonneg u hu := by
    apply neg_nonneg.mpr
    apply Real.log_nonpos (nelsen7_arg_pos θ hθ h1 u hu).le
    nlinarith [u.property.2]
  inv_antitone u v hu huv := by
    apply neg_le_neg
    apply Real.log_le_log (nelsen7_arg_pos θ hθ h1 u hu)
    have huv' : (u : ℝ) ≤ (v : ℝ) := huv
    nlinarith
  inv_one := by simp
  right_inv u hu := by
    rw [neg_neg, Real.exp_log (nelsen7_arg_pos θ hθ h1 u hu)]
    have he : (θ * (u : ℝ) + 1 - θ + θ - 1) / θ = (u : ℝ) := by
      field_simp
      ring
    rw [he, max_eq_right u.property.1]

/-- Nelsen 7 on its whole parameter interval. -/
noncomputable def nelsen7 (θ : I) : Copula 2 :=
  if h : θ = 0 then countermonotonic else
    (nelsen7Generator θ (lt_of_le_of_ne θ.property.1
      (Ne.symm (fun hz => h (Subtype.ext hz)))) θ.property.2).copula

theorem isArchimedean_nelsen7 (θ : I) : IsArchimedean (nelsen7 θ) := by
  unfold nelsen7
  split_ifs
  · rw [← truncatedLinearGenerator_copula]
    exact truncatedLinearGenerator.isArchimedean
  · exact BivariateGenerator.isArchimedean _

theorem cdf_nelsen7 (θ u v : I) :
    (nelsen7 θ).cdf ![u, v] =
      max 0 ((θ : ℝ) * (u : ℝ) * (v : ℝ) + (1 - (θ : ℝ)) * ((u : ℝ) + (v : ℝ) - 1)) := by
  by_cases ht : θ = 0
  · simp [nelsen7, ht, cdf_countermonotonic]
  have hp : 0 < (θ : ℝ) := lt_of_le_of_ne θ.property.1
    (Ne.symm (fun hz => ht (Subtype.ext hz)))
  by_cases hu : u = 0
  · rw [hu, cdf_two_zero_left]
    simp only [show ((0 : I) : ℝ) = 0 from rfl, mul_zero, zero_mul, zero_add]
    rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr θ.property.2) (sub_nonpos.mpr v.property.2))]
  by_cases hv : v = 0
  · rw [hv, cdf_eq_zero_of_coord_eq_zero _ _ 1 rfl]
    simp only [show ((0 : I) : ℝ) = 0 from rfl, mul_zero, add_zero, zero_add]
    rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr θ.property.2) (sub_nonpos.mpr u.property.2))]
  simp only [nelsen7, ht, dite_false, BivariateGenerator.cdf_copula,
    BivariateGenerator.cdf, Matrix.cons_val_zero, Matrix.cons_val_one,
    hu, hv, or_self, ite_false]
  change max 0 ((Real.exp (-(-Real.log ((θ : ℝ) * u + 1 - θ) +
    -Real.log ((θ : ℝ) * v + 1 - θ))) + θ - 1) / θ) = _
  rw [neg_add, neg_neg, neg_neg, Real.exp_add,
    Real.exp_log (nelsen7_arg_pos θ hp θ.property.2 u hu),
    Real.exp_log (nelsen7_arg_pos θ hp θ.property.2 v hv)]
  congr 1
  field_simp
  ring

@[simp] theorem nelsen7_zero : nelsen7 0 = countermonotonic := by simp [nelsen7]

@[simp] theorem nelsen7_one : nelsen7 1 = independence 2 := by
  apply ext_cdf_two
  intro u v
  rw [cdf_nelsen7, cdf_independence, Fin.prod_univ_two]
  simp [max_eq_right (mul_nonneg u.property.1 v.property.1)]

theorem isSD_nelsen7 (θ : I) : (nelsen7 θ).IsSD := by
  intro a b c v hab hbc
  have hab' : 0 ≤ (b : ℝ) - (a : ℝ) := sub_nonneg.mpr hab
  have hbc' : 0 ≤ (c : ℝ) - (b : ℝ) := sub_nonneg.mpr hbc
  have hac' : 0 ≤ (c : ℝ) - (a : ℝ) := by linarith
  simp only [cdf_nelsen7]
  rw [mul_max_of_nonneg _ _ hac']
  apply max_le
  · rw [mul_zero]
    positivity
  · have h₁ := mul_le_mul_of_nonneg_left
      (le_max_right 0 ((θ : ℝ) * c * v + (1 - θ) * ((c : ℝ) + v - 1))) hab'
    have h₂ := mul_le_mul_of_nonneg_left
      (le_max_right 0 ((θ : ℝ) * a * v + (1 - θ) * ((a : ℝ) + v - 1))) hbc'
    nlinarith

theorem isCD_nelsen7 (θ : I) : (nelsen7 θ).IsCD :=
  (isArchimedean_nelsen7 θ).isCD_iff.mpr (isSD_nelsen7 θ)

theorem lowerOrthantLE_nelsen7 {θ η : I} (h : θ ≤ η) :
    (nelsen7 θ).LowerOrthantLE (nelsen7 η) := by
  intro u
  have he : u = ![u 0, u 1] := by ext i; fin_cases i <;> rfl
  rw [he, cdf_nelsen7, cdf_nelsen7]
  apply max_le_max le_rfl
  have hn := mul_nonneg (mul_nonneg (sub_nonneg.mpr (show (θ : ℝ) ≤ (η : ℝ) from h))
    (sub_nonneg.mpr (u 0).property.2)) (sub_nonneg.mpr (u 1).property.2)
  nlinarith

end ProbabilityTheory.Copula
