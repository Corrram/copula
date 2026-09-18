/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Power
import Copula.Families.Clayton.CDF
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Clayton's Archimedean generator and the BB1 family -/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem convexOn_one_add_rpow {p : ℝ} (hp : p ≤ 0) :
    ConvexOn ℝ (Ici 0) (fun t : ℝ => (1 + t) ^ p) := by
  refine ⟨convex_Ici _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hx' : 0 < 1 + x := by linarith [show 0 ≤ x from hx]
  have hy' : 0 < 1 + y := by linarith [show 0 ≤ y from hy]
  have hz : 0 < 1 + (a * x + b * y) := by
    have : 0 ≤ a * x + b * y := by positivity
    linarith
  have he : a * (1 + x) + b * (1 + y) = 1 + (a * x + b * y) := by
    nlinarith
  have hl := strictConcaveOn_log_Ioi.concaveOn.2 hx' hy' ha hb hab
  simp only [smul_eq_mul, he] at hl ⊢
  rw [Real.rpow_def_of_pos hz, Real.rpow_def_of_pos hx', Real.rpow_def_of_pos hy']
  calc
    _ ≤ Real.exp (a * (Real.log (1 + x) * p) + b * (Real.log (1 + y) * p)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonpos_right hl hp]
    _ ≤ _ := convexOn_exp.2 (mem_univ _) (mem_univ _) ha hb hab

/-- Clayton's inverse generator `(1+t)^(-1/θ)`, for `θ > 0`. -/
noncomputable def claytonGenerator (θ : ℝ) (hθ : 0 < θ) : BivariateGenerator where
  toFun t := (1 + t) ^ (-θ⁻¹)
  invFun u := (u : ℝ) ^ (-θ) - 1
  nonneg t ht := Real.rpow_nonneg (by linarith) _
  antitone x hx y _ hxy := Real.rpow_le_rpow_of_nonpos (by linarith [show 0 ≤ x from hx])
    (by linarith) (neg_nonpos.mpr (inv_nonneg.mpr hθ.le))
  convex := convexOn_one_add_rpow (neg_nonpos.mpr (inv_nonneg.mpr hθ.le))
  inv_nonneg u hu := by
    apply sub_nonneg.mpr
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      (lt_of_le_of_ne u.property.1 (Ne.symm (by intro h; exact hu (Subtype.ext h))))
      u.property.2 (neg_nonpos.mpr hθ.le)
  inv_antitone u v hu huv := by
    apply sub_le_sub_right
    exact Real.rpow_le_rpow_of_nonpos
      (lt_of_le_of_ne u.property.1 (Ne.symm (by intro h; exact hu (Subtype.ext h))))
      huv (neg_nonpos.mpr hθ.le)
  inv_one := by simp
  right_inv u _ := by
    rw [add_sub_cancel, ← Real.rpow_mul u.property.1, neg_mul_neg,
      mul_inv_cancel₀ hθ.ne', Real.rpow_one]

theorem claytonGenerator_copula (θ : ℝ) (hθ : 0 < θ) :
    (claytonGenerator θ hθ).copula = clayton 2 θ hθ := by
  apply ext_cdf
  intro u
  by_cases hu : ∀ i, u i ≠ 0
  · rw [BivariateGenerator.cdf_copula, BivariateGenerator.cdf,
      ite_eq_right (not_or.mpr ⟨hu 0, hu 1⟩)]
    rw [cdf_clayton_of_pos θ hθ u (fun i =>
      lt_of_le_of_ne (u i).property.1 (Ne.symm (by intro h; exact hu i (Subtype.ext h)))),
      Fin.sum_univ_two]
    change (1 + ((u 0 : ℝ) ^ (-θ) - 1 + ((u 1 : ℝ) ^ (-θ) - 1))) ^ (-θ⁻¹) = _
    rfl
  · push Not at hu
    obtain ⟨i, hi⟩ := hu
    rw [cdf_eq_zero_of_coord_eq_zero _ u i hi, cdf_eq_zero_of_coord_eq_zero _ u i hi]

theorem hasArchimedeanGenerator_clayton (d : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    HasArchimedeanGenerator (clayton d θ hθ) (claytonGenerator θ hθ) := by
  intro u hu
  exact cdf_clayton_of_pos θ hθ u (fun i =>
    lt_of_le_of_ne (u i).property.1 (Ne.symm (by intro h; exact hu i (Subtype.ext h))))

theorem isArchimedean_clayton (d : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    IsArchimedean (clayton d θ hθ) := ⟨_, hasArchimedeanGenerator_clayton d θ hθ⟩

/-- BB1 (Clayton–Gumbel), with `θ > 0` and outer-power parameter `δ ≥ 1`. -/
noncomputable def bb1 (θ : ℝ) (hθ : 0 < θ) (δ : ℝ) (hδ : 1 ≤ δ) : Copula 2 :=
  ((claytonGenerator θ hθ).outerPower δ hδ).copula

theorem isArchimedean_bb1 (θ : ℝ) (hθ : 0 < θ) (δ : ℝ) (hδ : 1 ≤ δ) :
    IsArchimedean (bb1 θ hθ δ hδ) := ((claytonGenerator θ hθ).outerPower δ hδ).isArchimedean

@[simp] theorem bb1_one (θ : ℝ) (hθ : 0 < θ) : bb1 θ hθ 1 le_rfl = clayton 2 θ hθ := by
  simp [bb1, claytonGenerator_copula]

theorem cdf_bb1 (θ : ℝ) (hθ : 0 < θ) (δ : ℝ) (hδ : 1 ≤ δ) (u : Fin 2 → I)
    (hu : ∀ i, u i ≠ 0) :
    (bb1 θ hθ δ hδ).cdf u =
      (1 + (((u 0 : ℝ) ^ (-θ) - 1) ^ δ + ((u 1 : ℝ) ^ (-θ) - 1) ^ δ) ^ δ⁻¹) ^ (-θ⁻¹) := by
  rw [bb1, BivariateGenerator.cdf_copula, BivariateGenerator.cdf,
    ite_eq_right (not_or.mpr ⟨hu 0, hu 1⟩)]
  rfl

end ProbabilityTheory.Copula
