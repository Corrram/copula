/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Basic
import Copula.Transform.Power
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # The outer-power transformation of an Archimedean generator -/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.BivariateGenerator

/-- The outer-power generator `t ↦ ψ(t^(1/θ))`, for `θ ≥ 1`.
Applied to exponential and Clayton generators this gives Gumbel and BB1. -/
noncomputable def outerPower (g : BivariateGenerator) (θ : ℝ) (hθ : 1 ≤ θ) :
    BivariateGenerator where
  toFun t := g.toFun (t ^ θ⁻¹)
  invFun u := (g.invFun u) ^ θ
  nonneg t ht := g.nonneg _ (Real.rpow_nonneg ht _)
  antitone x hx y hy hxy := g.antitone (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _)
    (Real.rpow_le_rpow hx hxy (_root_.inv_nonneg.mpr (by linarith)))
  convex := by
    refine ⟨convex_Ici _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hx0 : 0 ≤ x := hx
    have hy0 : 0 ≤ y := hy
    have hp : 0 ≤ θ⁻¹ := _root_.inv_nonneg.mpr (by linarith)
    have hple : θ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hθ
    have hc := (Real.concaveOn_rpow hp hple).2 hx hy ha hb hab
    simp only [smul_eq_mul] at hc ⊢
    calc
      _ ≤ g.toFun (a * x ^ θ⁻¹ + b * y ^ θ⁻¹) :=
        g.antitone
          (show 0 ≤ a * x ^ θ⁻¹ + b * y ^ θ⁻¹ from by positivity)
          (show 0 ≤ (a * x + b * y) ^ θ⁻¹ from by positivity) hc
      _ ≤ _ := g.convex.2 (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _) ha hb hab
  inv_nonneg u hu := Real.rpow_nonneg (g.inv_nonneg u hu) _
  inv_antitone u v hu huv := by
    have hv : v ≠ 0 := fun h => hu (le_antisymm (h ▸ huv) unitInterval.nonneg')
    exact Real.rpow_le_rpow (g.inv_nonneg v hv) (g.inv_antitone u v hu huv) (by linarith)
  inv_one := by rw [g.inv_one, Real.zero_rpow (by linarith : θ ≠ 0)]
  right_inv u hu := by
    rw [Real.rpow_rpow_inv (g.inv_nonneg u hu) (by linarith : θ ≠ 0), g.right_inv u hu]

@[simp] theorem outerPower_one (g : BivariateGenerator) : g.outerPower 1 le_rfl = g := by
  cases g
  simp [outerPower]

/-- Raising the inverse generator to a power at least one preserves bivariate
admissibility, including generators with a finite zero. -/
noncomputable def innerPower (g : BivariateGenerator) (θ : ℝ) (hθ : 1 ≤ θ) :
    BivariateGenerator where
  toFun t := g.toFun t ^ θ
  invFun u := g.invFun (unitPower u θ⁻¹ (_root_.inv_nonneg.mpr (by linarith)))
  nonneg t ht := Real.rpow_nonneg (g.nonneg t ht) _
  antitone x hx y hy hxy := Real.rpow_le_rpow (g.nonneg y hy)
    (g.antitone hx hy hxy) (by linarith)
  convex := by
    refine ⟨convex_Ici _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hc := g.convex.2 hx hy ha hb hab
    have hx0 : 0 ≤ x := hx
    have hy0 : 0 ≤ y := hy
    simp only [smul_eq_mul] at hc ⊢
    calc
      _ ≤ (a * g.toFun x + b * g.toFun y) ^ θ :=
        Real.rpow_le_rpow (g.nonneg _ (by positivity)) hc (by linarith)
      _ ≤ _ := (convexOn_rpow hθ).2 (g.nonneg x hx) (g.nonneg y hy) ha hb hab
  inv_nonneg u hu := by
    apply g.inv_nonneg
    intro hz
    have hp : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1
      (Ne.symm (fun h => hu (Subtype.ext h)))
    exact (Real.rpow_pos_of_pos hp θ⁻¹).ne' (congrArg (fun v : I => (v : ℝ)) hz)
  inv_antitone u v hu huv := by
    apply g.inv_antitone
    · intro hz
      have hp : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1
        (Ne.symm (fun h => hu (Subtype.ext h)))
      exact (Real.rpow_pos_of_pos hp θ⁻¹).ne' (congrArg (fun v : I => (v : ℝ)) hz)
    · exact Real.rpow_le_rpow u.property.1 huv (_root_.inv_nonneg.mpr (by linarith))
  inv_one := by rw [unitPower_top, g.inv_one]
  right_inv u hu := by
    have hp : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1
      (Ne.symm (fun h => hu (Subtype.ext h)))
    have hz : unitPower u θ⁻¹ (_root_.inv_nonneg.mpr (by linarith : 0 ≤ θ)) ≠ 0 := by
      intro h
      exact (Real.rpow_pos_of_pos hp θ⁻¹).ne' (congrArg (fun v : I => (v : ℝ)) h)
    rw [g.right_inv _ hz, coe_unitPower, Real.rpow_inv_rpow u.property.1 (by linarith : θ ≠ 0)]

@[simp] theorem innerPower_one (g : BivariateGenerator) : g.innerPower 1 le_rfl = g := by
  cases g
  simp [innerPower]

end ProbabilityTheory.Copula.BivariateGenerator
