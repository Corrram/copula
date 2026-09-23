/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Clayton
import Copula.Dependence.TotalPositivity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! # TP2 of Archimedean CDFs with log-convex inverse generators -/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.BivariateGenerator

/-- A positive log-convex inverse generator yields a TP2 bivariate CDF. -/
theorem isTP2CDF_of_logConvex (g : BivariateGenerator)
    (hpos : ∀ t, 0 ≤ t → 0 < g.toFun t)
    (hconv : ConvexOn ℝ (Ici 0) (fun t => Real.log (g.toFun t))) :
    g.copula.IsTP2CDF := by
  intro a b c d hab hcd
  simp only [BivariateGenerator.cdf_copula]
  by_cases ha : a = 0
  · simp [ha]
  by_cases hc : c = 0
  · simp [hc]
  have hb : b ≠ 0 := fun hz => ha (le_antisymm (hz ▸ hab) unitInterval.nonneg')
  have hd : d ≠ 0 := fun hz => hc (le_antisymm (hz ▸ hcd) unitInterval.nonneg')
  let x := g.invFun b
  let y := g.invFun a
  let z := g.invFun d
  let w := g.invFun c
  have hx : 0 ≤ x := g.inv_nonneg b hb
  have hz : 0 ≤ z := g.inv_nonneg d hd
  have hxy : x ≤ y := g.inv_antitone a b ha hab
  have hzw : z ≤ w := g.inv_antitone c d hc hcd
  have hi := convex_increment hconv hx hz hxy hzw
  have hlog : Real.log (g.toFun (y + z)) + Real.log (g.toFun (x + w)) ≤
      Real.log (g.toFun (y + w)) + Real.log (g.toFun (x + z)) := by
    linarith
  have hp_yz := hpos (y + z) (by linarith)
  have hp_xw := hpos (x + w) (by linarith)
  have hp_yw := hpos (y + w) (by linarith)
  have hp_xz := hpos (x + z) (by linarith)
  have he := Real.exp_le_exp.mpr hlog
  simp only [Real.exp_add, Real.exp_log hp_yz, Real.exp_log hp_xw,
    Real.exp_log hp_yw, Real.exp_log hp_xz] at he
  simpa [BivariateGenerator.cdf, ha, hb, hc, hd, x, y, z, w, mul_comm] using he

end ProbabilityTheory.Copula.BivariateGenerator

namespace ProbabilityTheory.Copula

/-- The negative logarithm of one plus a concave power is convex. -/
private theorem convexOn_neg_log_one_add_rpow {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ConvexOn ℝ (Ici 0) (fun t : ℝ => -Real.log (1 + t ^ α)) := by
  refine ⟨convex_Ici _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hx' : 0 < 1 + x ^ α := by
    have hp := Real.rpow_nonneg hx0 α
    linarith
  have hy' : 0 < 1 + y ^ α := by
    have hp := Real.rpow_nonneg hy0 α
    linarith
  have hp := (Real.concaveOn_rpow hα0 hα1).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hp ⊢
  have he : a * (1 + x ^ α) + b * (1 + y ^ α) =
      1 + (a * x ^ α + b * y ^ α) := by nlinarith
  have hsumpos : 0 < a * (1 + x ^ α) + b * (1 + y ^ α) := by
    rw [he]
    have hn : 0 ≤ a * x ^ α + b * y ^ α := by positivity
    linarith
  have hbound : a * (1 + x ^ α) + b * (1 + y ^ α) ≤
      1 + (a * x + b * y) ^ α := by
    rw [he]
    linarith
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at hlog
  have hmono := Real.log_le_log hsumpos hbound
  nlinarith

/-- Every bivariate BB1 copula has a TP2 CDF at positive Clayton parameter
and outer-power parameter at least one. This is a CDF property, not an MTP2
density claim. -/
theorem isTP2CDF_bb1 (θ : ℝ) (hθ : 0 < θ) (δ : ℝ) (hδ : 1 ≤ δ) :
    (bb1 θ hθ δ hδ).IsTP2CDF := by
  let g := (claytonGenerator θ hθ).outerPower δ hδ
  have hα0 : 0 ≤ δ⁻¹ := inv_nonneg.mpr (by linarith)
  have hα1 : δ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hδ
  have hθinv : 0 ≤ θ⁻¹ := inv_nonneg.mpr hθ.le
  have hscaled : ConvexOn ℝ (Ici 0)
      (fun t : ℝ => θ⁻¹ • (-Real.log (1 + t ^ δ⁻¹))) :=
    ConvexOn.smul hθinv (convexOn_neg_log_one_add_rpow hα0 hα1)
  have hconv : ConvexOn ℝ (Ici 0) (fun t => Real.log (g.toFun t)) := by
    apply hscaled.congr
    intro t ht
    change θ⁻¹ • (-Real.log (1 + t ^ δ⁻¹)) =
      Real.log ((1 + t ^ δ⁻¹) ^ (-θ⁻¹))
    have ht0 : 0 ≤ t := ht
    have hb : 0 < 1 + t ^ δ⁻¹ := by
      have hp := Real.rpow_nonneg ht0 δ⁻¹
      linarith
    rw [smul_eq_mul, Real.log_rpow hb]
    ring
  have hpos : ∀ t, 0 ≤ t → 0 < g.toFun t := by
    intro t ht
    change 0 < (1 + t ^ δ⁻¹) ^ (-θ⁻¹)
    positivity
  change g.copula.IsTP2CDF
  exact g.isTP2CDF_of_logConvex hpos hconv

end ProbabilityTheory.Copula
