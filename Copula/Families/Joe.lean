/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Exponential
import Copula.Archimedean.Power

/-! # Bivariate Joe and BB6 (Joe–Gumbel) copulas -/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem joe_inner_pos (θ : ℝ) (hθ : 1 ≤ θ) (u : I) (hu : u ≠ 0) :
    0 < 1 - (1 - (u : ℝ)) ^ θ := by
  have hup : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (by
    intro h; exact hu (Subtype.ext h)))
  have h := Real.rpow_lt_one (by linarith [u.property.2] : 0 ≤ 1 - (u : ℝ))
    (by linarith : 1 - (u : ℝ) < 1) (by linarith : 0 < θ)
  linarith

/-- Joe's inverse generator `1-(1-exp(-t))^(1/θ)`, for `θ ≥ 1`. -/
noncomputable def joeGenerator (θ : ℝ) (hθ : 1 ≤ θ) : BivariateGenerator where
  toFun t := 1 - (1 - Real.exp (-t)) ^ θ⁻¹
  invFun u := -Real.log (1 - (1 - (u : ℝ)) ^ θ)
  nonneg t ht := by
    apply sub_nonneg.mpr
    exact Real.rpow_le_one (by have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht); linarith)
      (by linarith [Real.exp_pos (-t)]) (inv_nonneg.mpr (by linarith))
  antitone x hx y _ hxy := by
    apply sub_le_sub_left
    apply Real.rpow_le_rpow
    · have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
      linarith
    · have := Real.exp_le_exp.mpr (neg_le_neg hxy)
      linarith
    · exact inv_nonneg.mpr (by linarith)
  convex := by
    refine ⟨convex_Ici _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hp : 0 ≤ θ⁻¹ := inv_nonneg.mpr (by linarith)
    have hple : θ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hθ
    have hx' : 0 ≤ 1 - Real.exp (-x) := by
      have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx); linarith
    have hy' : 0 ≤ 1 - Real.exp (-y) := by
      have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy); linarith
    have he := convexOn_exp.2 (mem_univ (-x)) (mem_univ (-y)) ha hb hab
    simp only [smul_eq_mul, mul_neg, ← neg_add] at he
    have hbase : a * (1 - Real.exp (-x)) + b * (1 - Real.exp (-y)) ≤
        1 - Real.exp (-(a * x + b * y)) := by nlinarith
    have hr := Real.rpow_le_rpow (by positivity :
      0 ≤ a * (1 - Real.exp (-x)) + b * (1 - Real.exp (-y))) hbase hp
    have hc := (Real.concaveOn_rpow hp hple).2 hx' hy' ha hb hab
    simp only [smul_eq_mul] at hc ⊢
    nlinarith
  inv_nonneg u hu := by
    apply neg_nonneg.mpr
    exact Real.log_nonpos (joe_inner_pos θ hθ u hu).le
      (by have := Real.rpow_nonneg (by linarith [u.property.2] : 0 ≤ 1 - (u : ℝ)) θ; linarith)
  inv_antitone u v hu huv := by
    apply neg_le_neg
    apply Real.log_le_log (joe_inner_pos θ hθ u hu)
    have hp := Real.rpow_le_rpow (by linarith [v.property.2] : 0 ≤ 1 - (v : ℝ))
      (sub_le_sub_left (show (u : ℝ) ≤ (v : ℝ) from huv) 1) (by linarith : 0 ≤ θ)
    linarith
  inv_one := by simp [Real.zero_rpow (by linarith : θ ≠ 0)]
  right_inv u hu := by
    rw [neg_neg, Real.exp_log (joe_inner_pos θ hθ u hu), sub_sub_cancel,
      Real.rpow_rpow_inv (by linarith [u.property.2] : 0 ≤ 1 - (u : ℝ))
        (by linarith : θ ≠ 0)]
    ring

/-- The bivariate Joe family. -/
noncomputable def joe (θ : ℝ) (hθ : 1 ≤ θ) : Copula 2 := (joeGenerator θ hθ).copula

theorem isArchimedean_joe (θ : ℝ) (hθ : 1 ≤ θ) : IsArchimedean (joe θ hθ) :=
  (joeGenerator θ hθ).isArchimedean

theorem cdf_joe (θ : ℝ) (hθ : 1 ≤ θ) (u : Fin 2 → I) (hu : ∀ i, u i ≠ 0) :
    (joe θ hθ).cdf u =
      1 - (1 - (1 - (1 - (u 0 : ℝ)) ^ θ) * (1 - (1 - (u 1 : ℝ)) ^ θ)) ^ θ⁻¹ := by
  rw [joe, BivariateGenerator.cdf_copula, BivariateGenerator.cdf,
    ite_eq_right (not_or.mpr ⟨hu 0, hu 1⟩)]
  change 1 - (1 - Real.exp (-(-Real.log _ + -Real.log _))) ^ θ⁻¹ = _
  rw [neg_add, neg_neg, neg_neg, Real.exp_add,
    Real.exp_log (joe_inner_pos θ hθ (u 0) (hu 0)),
    Real.exp_log (joe_inner_pos θ hθ (u 1) (hu 1))]

/-- BB6 (Joe–Gumbel), including Joe when the outer-power parameter is one. -/
noncomputable def bb6 (θ : ℝ) (hθ : 1 ≤ θ) (δ : ℝ) (hδ : 1 ≤ δ) : Copula 2 :=
  ((joeGenerator θ hθ).outerPower δ hδ).copula

theorem isArchimedean_bb6 (θ : ℝ) (hθ : 1 ≤ θ) (δ : ℝ) (hδ : 1 ≤ δ) :
    IsArchimedean (bb6 θ hθ δ hδ) := ((joeGenerator θ hθ).outerPower δ hδ).isArchimedean

@[simp] theorem bb6_one (θ : ℝ) (hθ : 1 ≤ θ) : bb6 θ hθ 1 le_rfl = joe θ hθ := by
  simp [bb6, joe]

@[simp] theorem joe_one : joe 1 le_rfl = independence 2 := by
  apply ext_cdf
  intro u
  by_cases hu : ∀ i, u i ≠ 0
  · rw [cdf_joe 1 le_rfl u hu, cdf_independence, Fin.prod_univ_two]
    simp
  · push Not at hu
    obtain ⟨i, hi⟩ := hu
    rw [cdf_eq_zero_of_coord_eq_zero _ u i hi, cdf_eq_zero_of_coord_eq_zero _ u i hi]

theorem cdf_bb6 (θ : ℝ) (hθ : 1 ≤ θ) (δ : ℝ) (hδ : 1 ≤ δ)
    (u : Fin 2 → I) (hu : ∀ i, u i ≠ 0) :
    (bb6 θ hθ δ hδ).cdf u = 1 - (1 - Real.exp (-((
      (-Real.log (1 - (1 - (u 0 : ℝ)) ^ θ)) ^ δ +
      (-Real.log (1 - (1 - (u 1 : ℝ)) ^ θ)) ^ δ) ^ δ⁻¹))) ^ θ⁻¹ := by
  rw [bb6, BivariateGenerator.cdf_copula, BivariateGenerator.cdf,
    ite_eq_right (not_or.mpr ⟨hu 0, hu 1⟩)]
  rfl

end ProbabilityTheory.Copula
