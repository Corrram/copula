/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Nonnegative real powers on the unit interval -/

open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Real powers as maps of the closed unit interval. In particular `0^0 = 1`. -/
noncomputable def unitPower (u : I) (r : ℝ) (hr : 0 ≤ r) : I :=
  ⟨(u : ℝ) ^ r, Real.rpow_nonneg u.property.1 _, Real.rpow_le_one u.property.1 u.property.2 hr⟩

@[simp] theorem coe_unitPower (u : I) (r : ℝ) (hr : 0 ≤ r) :
    (unitPower u r hr : ℝ) = (u : ℝ) ^ r := rfl

@[simp] theorem unitPower_one (u : I) : unitPower u 1 zero_le_one = u := by
  ext; simp [unitPower]

@[simp] theorem unitPower_zero (u : I) : unitPower u 0 le_rfl = 1 := by
  ext; simp [unitPower]

@[simp] theorem unitPower_top (r : ℝ) (hr : 0 ≤ r) : unitPower 1 r hr = 1 := by
  ext; simp [unitPower]

theorem unitPower_mul (u : I) (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    unitPower (unitPower u r hr) t ht = unitPower u (r * t) (mul_nonneg hr ht) := by
  ext; exact (Real.rpow_mul u.property.1 r t).symm

@[fun_prop] theorem measurable_unitPower (r : ℝ) (hr : 0 ≤ r) :
    Measurable (fun u : I => unitPower u r hr) := by
  exact (measurable_subtype_coe.pow_const r).subtype_mk

/-- The sampling map for a power marginal; exponent zero gives a point mass at zero. -/
noncomputable def powerSample (a : I) (u : I) : I :=
  if a = 0 then 0 else unitPower u (a : ℝ)⁻¹ (inv_nonneg.mpr a.property.1)

@[fun_prop] theorem measurable_powerSample (a : I) : Measurable (powerSample a) := by
  unfold powerSample
  split_ifs <;> fun_prop

theorem powerSample_le_iff (a u v : I) :
    powerSample a u ≤ v ↔ u ≤ unitPower v a a.property.1 := by
  by_cases ha : a = 0
  · simp [powerSample, ha, unitInterval.le_one']
  have hap : 0 < (a : ℝ) := lt_of_le_of_ne a.property.1 (Ne.symm (by
    intro h; exact ha (Subtype.ext h)))
  change (if a = 0 then 0 else unitPower u (a : ℝ)⁻¹ _) ≤ v ↔ _
  rw [ite_eq_right ha]
  exact Real.rpow_inv_le_iff_of_pos u.property.1 v.property.1 hap

end ProbabilityTheory.Copula
