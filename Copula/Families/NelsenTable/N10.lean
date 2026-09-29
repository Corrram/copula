/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Ite
import Copula.Families.AMH
import Copula.Archimedean.Power

/-! # Nelsen's family 10

Nelsen, *An Introduction to Copulas*, second edition, Table 4.1, number 10 (Section 4.2):
generator `φ(t) = ln (2 t^(-θ) - 1)` and copula
`C(u, v) = u v / (1 + (1 - u^θ) (1 - v^θ))^(1/θ)`, for `0 < θ ≤ 1`.

No new convexity argument is needed: the inverse generator is
`ψ(s) = (2 / (exp s + 1))^(1/θ)`, the `1/θ`-th power of the inverse generator of the
Ali--Mikhail--Haq family at parameter `-1`, so the family is `innerPower` of
`amhGenerator (-1)` with exponent `1/θ ≥ 1`. This is the full parameter range of
Nelsen's table (the limiting case `θ = 0`, independence, is not a member of the family in
this module).
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem nelsen10_one_le_inv (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) : 1 ≤ θ⁻¹ :=
  (one_le_inv₀ hθ).mpr h1

/-- The inverse generator `s ↦ (2 / (exp s + 1))^(1/θ)` of Nelsen's family 10, for
`0 < θ ≤ 1`: the `1/θ`-th inner power of the Ali--Mikhail--Haq generator at `-1`. -/
noncomputable def nelsen10Generator (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) : BivariateGenerator :=
  (amhGenerator (-1) le_rfl (by norm_num)).innerPower θ⁻¹ (nelsen10_one_le_inv θ hθ h1)

/-- Nelsen's family 10 for `0 < θ ≤ 1`. -/
noncomputable def nelsen10 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) : Copula 2 :=
  (nelsen10Generator θ hθ h1).copula

theorem isArchimedean_nelsen10 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    IsArchimedean (nelsen10 θ hθ h1) :=
  (nelsen10Generator θ hθ h1).isArchimedean

/-- The generator of Nelsen's family 10 is `u ↦ ln (2 u^(-θ) - 1)`. -/
theorem nelsen10Generator_invFun (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) (u : I) :
    (nelsen10Generator θ hθ h1).invFun u = Real.log (2 * (u : ℝ) ^ (-θ) - 1) := by
  have hup : 0 ≤ (u : ℝ) := u.property.1
  show Real.log (-1 + (1 - -1) / (u : ℝ) ^ (θ⁻¹)⁻¹) = Real.log (2 * (u : ℝ) ^ (-θ) - 1)
  rw [inv_inv, Real.rpow_neg hup]
  congr 1
  ring

/-- Positive-coordinate CDF of a `1/θ`-th inner power, in terms of the CDF of the base. -/
private theorem innerPower_cdf (g : BivariateGenerator) (q : ℝ) (hq : 1 ≤ q)
    (h0 : 0 ≤ q⁻¹) (u v : I) (hu : u ≠ 0) (hv : v ≠ 0) :
    (g.innerPower q hq).cdf u v = (g.cdf (unitPower u q⁻¹ h0) (unitPower v q⁻¹ h0)) ^ q := by
  have hup : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))
  have hvp : 0 < (v : ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
  have huq : unitPower u q⁻¹ h0 ≠ 0 := by
    intro h
    exact (Real.rpow_pos_of_pos hup q⁻¹).ne' (congrArg (fun w : I => (w : ℝ)) h)
  have hvq : unitPower v q⁻¹ h0 ≠ 0 := by
    intro h
    exact (Real.rpow_pos_of_pos hvp q⁻¹).ne' (congrArg (fun w : I => (w : ℝ)) h)
  rw [BivariateGenerator.cdf, BivariateGenerator.cdf, ite_or_of_not (hu) (hv) _ _,
    ite_or_of_not (huq) (hvq) _ _]
  rfl

/-- Nelsen's family 10: `C(u,v) = u v / (1 + (1 - u^θ)(1 - v^θ))^(1/θ)` on positive
coordinates. -/
theorem cdf_nelsen10 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) (u v : I) (hu : u ≠ 0) (hv : v ≠ 0) :
    (nelsen10 θ hθ h1).cdf ![u, v] =
      (u : ℝ) * (v : ℝ) / (1 + (1 - (u : ℝ) ^ θ) * (1 - (v : ℝ) ^ θ)) ^ θ⁻¹ := by
  have hup : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))
  have hvp : 0 < (v : ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
  have hq : 1 ≤ θ⁻¹ := nelsen10_one_le_inv θ hθ h1
  have h0 : 0 ≤ (θ⁻¹)⁻¹ := inv_nonneg.mpr (inv_nonneg.mpr hθ.le)
  have hcdf : (nelsen10 θ hθ h1).cdf ![u, v] = (nelsen10Generator θ hθ h1).cdf u v :=
    BivariateGenerator.cdf_copula (nelsen10Generator θ hθ h1) ![u, v]
  rw [hcdf]
  have h := innerPower_cdf (amhGenerator (-1) le_rfl (by norm_num)) θ⁻¹ hq h0 u v hu hv
  refine h.trans ?_
  have hua : ((unitPower u (θ⁻¹)⁻¹ h0 : I) : ℝ) = (u : ℝ) ^ θ := by
    rw [coe_unitPower, inv_inv]
  have hvb : ((unitPower v (θ⁻¹)⁻¹ h0 : I) : ℝ) = (v : ℝ) ^ θ := by
    rw [coe_unitPower, inv_inv]
  have huaN : unitPower u (θ⁻¹)⁻¹ h0 ≠ 0 := by
    intro h'
    have h'' : ((unitPower u (θ⁻¹)⁻¹ h0 : I) : ℝ) = 0 := congrArg (fun w : I => (w : ℝ)) h'
    rw [hua] at h''
    exact (Real.rpow_pos_of_pos hup θ).ne' h''
  have hvbN : unitPower v (θ⁻¹)⁻¹ h0 ≠ 0 := by
    intro h'
    have h'' : ((unitPower v (θ⁻¹)⁻¹ h0 : I) : ℝ) = 0 := congrArg (fun w : I => (w : ℝ)) h'
    rw [hvb] at h''
    exact (Real.rpow_pos_of_pos hvp θ).ne' h''
  rw [amhGenerator_cdf (-1) le_rfl (by norm_num) _ _ huaN hvbN, hua, hvb]
  have hD : 1 - (-1 : ℝ) * (1 - (u : ℝ) ^ θ) * (1 - (v : ℝ) ^ θ) =
      1 + (1 - (u : ℝ) ^ θ) * (1 - (v : ℝ) ^ θ) := by ring
  have hu1 : (u : ℝ) ^ θ ≤ 1 := Real.rpow_le_one hup.le u.property.2 hθ.le
  have hv1 : (v : ℝ) ^ θ ≤ 1 := Real.rpow_le_one hvp.le v.property.2 hθ.le
  have hDnn : 0 ≤ 1 + (1 - (u : ℝ) ^ θ) * (1 - (v : ℝ) ^ θ) :=
    add_nonneg zero_le_one (mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hv1))
  rw [hD, Real.div_rpow (mul_nonneg (Real.rpow_nonneg hup.le θ) (Real.rpow_nonneg hvp.le θ))
    hDnn, Real.mul_rpow (Real.rpow_nonneg hup.le θ) (Real.rpow_nonneg hvp.le θ),
    Real.rpow_rpow_inv hup.le hθ.ne', Real.rpow_rpow_inv hvp.le hθ.ne']

/-- Nelsen's family 10 on the whole closed unit square, with grounded zero axes. -/
theorem nelsen10_cdf_full (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) (u v : I) :
    (nelsen10 θ hθ h1).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        (u : ℝ) * (v : ℝ) / (1 + (1 - (u : ℝ) ^ θ) * (1 - (v : ℝ) ^ θ)) ^ θ⁻¹ := by
  by_cases hu : u = 0
  · subst u
    rw [ite_or_of_left rfl _ _]
    exact (nelsen10 θ hθ h1).cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl
  by_cases hv : v = 0
  · subst v
    rw [ite_or_of_right rfl _ _]
    exact (nelsen10 θ hθ h1).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
  rw [ite_or_of_not (hu) (hv) _ _]
  exact cdf_nelsen10 θ hθ h1 u v hu hv

end ProbabilityTheory.Copula
