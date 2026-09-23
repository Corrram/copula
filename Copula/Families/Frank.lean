/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Exponential

/-! # Positive-parameter bivariate Frank copulas

The inverse generator is `-log(1-(1-exp(-θ))*exp(-t))/θ`.
This module covers `θ > 0`; the negative bivariate branch is not asserted here.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem frank_p (θ : ℝ) (hθ : 0 < θ) :
    0 < 1 - Real.exp (-θ) ∧ 1 - Real.exp (-θ) < 1 := by
  constructor
  · have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hθ); linarith
  · linarith [Real.exp_pos (-θ)]

private theorem frank_base_pos (θ : ℝ) (hθ : 0 < θ) (t : ℝ) (ht : 0 ≤ t) :
    0 < 1 - (1 - Real.exp (-θ)) * Real.exp (-t) := by
  have hp := frank_p θ hθ
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  have hep := Real.exp_pos (-t)
  nlinarith

private theorem frank_ratio (θ : ℝ) (hθ : 0 < θ) (u : I) (hu : u ≠ 0) :
    0 < (1 - Real.exp (-θ * (u : ℝ))) / (1 - Real.exp (-θ)) ∧
      (1 - Real.exp (-θ * (u : ℝ))) / (1 - Real.exp (-θ)) ≤ 1 := by
  have hup : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (by
    intro h; exact hu (Subtype.ext h)))
  have hp := (frank_p θ hθ).1
  constructor
  · apply div_pos _ hp
    have := Real.exp_lt_one_iff.mpr (by nlinarith : -θ * (u : ℝ) < 0)
    linarith
  · apply (div_le_one hp).mpr
    have := Real.exp_le_exp.mpr (by nlinarith [u.property.2] : -θ ≤ -θ * (u : ℝ))
    linarith

/-- Frank's inverse generator, with positive dependence parameter. -/
noncomputable def frankGenerator (θ : ℝ) (hθ : 0 < θ) : BivariateGenerator where
  toFun t := -Real.log (1 - (1 - Real.exp (-θ)) * Real.exp (-t)) / θ
  invFun u := -Real.log ((1 - Real.exp (-θ * (u : ℝ))) / (1 - Real.exp (-θ)))
  nonneg t ht := by
    apply div_nonneg _ hθ.le
    apply neg_nonneg.mpr
    apply Real.log_nonpos (frank_base_pos θ hθ t ht).le
    have := mul_nonneg (frank_p θ hθ).1.le (Real.exp_pos (-t)).le
    linarith
  antitone x hx y _ hxy := by
    apply div_le_div_of_nonneg_right _ hθ.le
    apply neg_le_neg
    apply Real.log_le_log (frank_base_pos θ hθ x hx)
    have he := Real.exp_le_exp.mpr (neg_le_neg hxy)
    have hp := (frank_p θ hθ).1
    nlinarith
  convex := by
    refine ⟨convex_Ici _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hx0 : 0 ≤ x := hx
    have hy0 : 0 ≤ y := hy
    have hp := (frank_p θ hθ).1
    have hx' := frank_base_pos θ hθ x hx
    have hy' := frank_base_pos θ hθ y hy
    have he := convexOn_exp.2 (mem_univ (-x)) (mem_univ (-y)) ha hb hab
    simp only [smul_eq_mul, mul_neg, ← neg_add] at he
    have hb' : a * (1 - (1 - Real.exp (-θ)) * Real.exp (-x)) +
        b * (1 - (1 - Real.exp (-θ)) * Real.exp (-y)) ≤
        1 - (1 - Real.exp (-θ)) * Real.exp (-(a * x + b * y)) := by
      nlinarith [mul_le_mul_of_nonneg_left he hp.le]
    have hw : 0 < a * (1 - (1 - Real.exp (-θ)) * Real.exp (-x)) +
        b * (1 - (1 - Real.exp (-θ)) * Real.exp (-y)) := by
      rcases lt_or_eq_of_le ha with ha | rfl
      · positivity
      · have hb1 : b = 1 := by linarith
        simpa [hb1] using hy'
    have hl := Real.log_le_log hw hb'
    have hc := strictConcaveOn_log_Ioi.concaveOn.2 hx' hy' ha hb hab
    simp only [smul_eq_mul] at hc ⊢
    convert (div_le_div_of_nonneg_right (neg_le_neg (hc.trans hl)) hθ.le) using 1
    ring
  inv_nonneg u hu := neg_nonneg.mpr (Real.log_nonpos (frank_ratio θ hθ u hu).1.le
    (frank_ratio θ hθ u hu).2)
  inv_antitone u v hu huv := by
    have huv' : (u : ℝ) ≤ (v : ℝ) := huv
    apply neg_le_neg
    apply Real.log_le_log (frank_ratio θ hθ u hu).1
    apply div_le_div_of_nonneg_right _ (frank_p θ hθ).1.le
    have he := Real.exp_le_exp.mpr (by nlinarith : -θ * (v : ℝ) ≤ -θ * (u : ℝ))
    linarith
  inv_one := by simp [(frank_p θ hθ).1.ne']
  right_inv u hu := by
    rw [neg_neg, Real.exp_log (frank_ratio θ hθ u hu).1,
      mul_div_cancel₀ _ (frank_p θ hθ).1.ne', sub_sub_cancel, Real.log_exp]
    field_simp

/-- The positive-parameter bivariate Frank family. -/
noncomputable def frank (θ : ℝ) (hθ : 0 < θ) : Copula 2 := (frankGenerator θ hθ).copula

theorem isArchimedean_frank (θ : ℝ) (hθ : 0 < θ) : IsArchimedean (frank θ hθ) :=
  (frankGenerator θ hθ).isArchimedean

theorem cdf_frank (θ : ℝ) (hθ : 0 < θ) (u : Fin 2 → I) (hu : ∀ i, u i ≠ 0) :
    (frank θ hθ).cdf u =
      -Real.log (1 - (1 - Real.exp (-θ * (u 0 : ℝ))) *
        (1 - Real.exp (-θ * (u 1 : ℝ))) / (1 - Real.exp (-θ))) / θ := by
  rw [frank, BivariateGenerator.cdf_copula, BivariateGenerator.cdf,
    ite_eq_right (not_or.mpr ⟨hu 0, hu 1⟩)]
  change -Real.log (1 - (1 - Real.exp (-θ)) * Real.exp (-(-Real.log _ + -Real.log _))) / θ = _
  rw [neg_add, neg_neg, neg_neg, Real.exp_add,
    Real.exp_log (frank_ratio θ hθ (u 0) (hu 0)).1,
    Real.exp_log (frank_ratio θ hθ (u 1) (hu 1)).1]
  congr 3
  field_simp

/-- The positive-parameter Frank CDF on the entire closed unit square.
The analytic logarithmic formula is used only away from the grounded zero axes. -/
theorem frank_cdf_full (θ : ℝ) (hθ : 0 < θ) (u v : I) :
    (frank θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        -Real.log (1 - (1 - Real.exp (-θ * (u : ℝ))) *
          (1 - Real.exp (-θ * (v : ℝ))) / (1 - Real.exp (-θ))) / θ := by
  by_cases hu : u = 0
  · subst u
    simpa using (frank θ hθ).cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl
  by_cases hv : v = 0
  · subst v
    simpa [hu] using (frank θ hθ).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
  have hp : ∀ i : Fin 2, (![u, v] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using hu
    · simpa using hv
  simpa [hu, hv] using cdf_frank θ hθ ![u, v] hp

end ProbabilityTheory.Copula
