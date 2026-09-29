/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Convexity lemmas for inverse generators of Nelsen's Table 4.1

Several families of Nelsen (*An Introduction to Copulas*, second edition, Table 4.1,
families 19 and 20) have an inverse generator of the form `c / f t` or `(f t) ^ p`
with `f t = log (t + c')` concave and positive and `p ≤ 0`. Such a composite of a
convex decreasing power with a concave function is convex. These elementary
lemmas isolate that argument.
-/

open Set

namespace ProbabilityTheory.Copula

/-- The power `z ↦ z ^ p` is convex on `(0, ∞)` for every nonpositive exponent `p`. -/
theorem convexOn_rpow_Ioi_of_nonpos {p : ℝ} (hp : p ≤ 0) :
    ConvexOn ℝ (Ioi 0) (fun z : ℝ => z ^ p) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hconv : Convex ℝ (Ioi (0 : ℝ)) := convex_Ioi 0
  have hz : 0 < a • x + b • y := mem_Ioi.mp (hconv hx hy ha hb hab)
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  have hl := strictConcaveOn_log_Ioi.concaveOn.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hz hl ⊢
  rw [Real.rpow_def_of_pos hz, Real.rpow_def_of_pos hx', Real.rpow_def_of_pos hy']
  calc
    _ ≤ Real.exp (a * (Real.log x * p) + b * (Real.log y * p)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonpos_right hl hp]
    _ ≤ _ := by
      have h := convexOn_exp.2 (mem_univ (Real.log x * p)) (mem_univ (Real.log y * p)) ha hb hab
      simpa only [smul_eq_mul] using h

/-- A positive concave function raised to a nonpositive power is convex. -/
theorem convexOn_rpow_comp_nonpos {f : ℝ → ℝ} {p : ℝ} (hp : p ≤ 0)
    (hf : ConcaveOn ℝ (Ici 0) f) (hpos : ∀ x ∈ Ici (0 : ℝ), 0 < f x) :
    ConvexOn ℝ (Ici 0) (fun x => f x ^ p) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hc := hf.2 hx hy ha hb hab
  have hconv : Convex ℝ (Ioi (0 : ℝ)) := convex_Ioi 0
  have hw : 0 < a • f x + b • f y :=
    mem_Ioi.mp (hconv (mem_Ioi.mpr (hpos x hx)) (mem_Ioi.mpr (hpos y hy)) ha hb hab)
  have h1 : f (a • x + b • y) ^ p ≤ (a • f x + b • f y) ^ p :=
    Real.rpow_le_rpow_of_nonpos hw hc hp
  have h2 := (convexOn_rpow_Ioi_of_nonpos hp).2 (mem_Ioi.mpr (hpos x hx))
    (mem_Ioi.mpr (hpos y hy)) ha hb hab
  exact le_trans h1 h2

/-- A nonnegative constant divided by a positive concave function is convex. -/
theorem convexOn_div_comp {f : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : ConcaveOn ℝ (Ici 0) f) (hpos : ∀ x ∈ Ici (0 : ℝ), 0 < f x) :
    ConvexOn ℝ (Ici 0) (fun x => c / f x) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hfx := hpos x hx
  have hfy := hpos y hy
  have hcc : a * f x + b * f y ≤ f (a * x + b * y) := by
    simpa only [smul_eq_mul] using hf.2 hx hy ha hb hab
  have hconv : Convex ℝ (Ioi (0 : ℝ)) := convex_Ioi 0
  have hw : 0 < a * f x + b * f y := by
    simpa only [smul_eq_mul, mem_Ioi] using
      hconv (mem_Ioi.mpr hfx) (mem_Ioi.mpr hfy) ha hb hab
  have h1 : c / f (a * x + b * y) ≤ c / (a * f x + b * f y) :=
    div_le_div_of_nonneg_left hc hw hcc
  have hz : ConvexOn ℝ (Ioi 0) (fun z : ℝ => z ^ (-1 : ℤ)) := convexOn_zpow (-1)
  have h2 : (a * f x + b * f y)⁻¹ ≤ a * (f x)⁻¹ + b * (f y)⁻¹ := by
    simpa only [smul_eq_mul, zpow_neg_one] using
      hz.2 (mem_Ioi.mpr hfx) (mem_Ioi.mpr hfy) ha hb hab
  simp only [smul_eq_mul]
  calc
    c / f (a * x + b * y) ≤ c / (a * f x + b * f y) := h1
    _ = c * (a * f x + b * f y)⁻¹ := div_eq_mul_inv _ _
    _ ≤ c * (a * (f x)⁻¹ + b * (f y)⁻¹) := mul_le_mul_of_nonneg_left h2 hc
    _ = a * (c / f x) + b * (c / f y) := by ring

/-- The logarithm of a positive translate is concave on `[0, ∞)`. -/
theorem concaveOn_log_add {c : ℝ} (hc : 0 < c) :
    ConcaveOn ℝ (Ici 0) (fun s : ℝ => Real.log (s + c)) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hx' : 0 < x + c := by linarith
  have hy' : 0 < y + c := by linarith
  have hl := strictConcaveOn_log_Ioi.concaveOn.2 (mem_Ioi.mpr hx') (mem_Ioi.mpr hy') ha hb hab
  have he : a • (x + c) + b • (y + c) = a • x + b • y + c := by
    simp only [smul_eq_mul]
    linear_combination c * hab
  rw [he] at hl
  exact hl

/-- `c ≤ log (t + exp c)` for nonnegative `t`. -/
theorem le_log_add_exp {t : ℝ} (ht : 0 ≤ t) (c : ℝ) : c ≤ Real.log (t + Real.exp c) := by
  have h : Real.exp c ≤ t + Real.exp c := by linarith
  have h2 := Real.log_le_log (Real.exp_pos c) h
  rwa [Real.log_exp] at h2

end ProbabilityTheory.Copula
