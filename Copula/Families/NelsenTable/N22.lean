/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Ite
import Copula.Archimedean.Clamp
import Copula.Archimedean.Power
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # Nelsen's family 22

Nelsen, *An Introduction to Copulas*, second edition, Table 4.1, number 22 (Section 4.2):
generator `φ(t) = arcsin (1 - t^θ)` for `0 < θ ≤ 1`.

The generator is non-strict (`φ(0) = π/2`). At `θ = 1` the pseudo-inverse is
`ψ₁(s) = 1 - sin (min s (π/2))`, convex because `sin` is concave on `[0, π]`; it is built with
`BivariateGenerator.ofClamp`. For general `θ` the pseudo-inverse is `ψ₁^(1/θ)`, the inner power
`BivariateGenerator.innerPower` with exponent `1/θ ≥ 1`, so no further convexity argument is
needed.

**Correction of the printed formula.** With `a = 1 - u^θ` and `b = 1 - v^θ`, Table 4.1 prints
`C(u, v) = max ((1 - a √(1 - b²) - b √(1 - a²))^(1/θ)) 0`. This is only correct where
`φ(u) + φ(v) = arcsin a + arcsin b ≤ π/2`, which is equivalent to `a² + b² ≤ 1`. Beyond that
region the copula vanishes, while the printed expression is positive (for small `u = v` it
tends to `1`, exceeding `min(u, v)`). The theorem `cdf_nelsen22` states the correct formula:
`C(u, v) = (1 - a √(1 - b²) - b √(1 - a²))^(1/θ)` if `a² + b² ≤ 1`, and `0` otherwise.
-/

open Set Real
open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem nelsen22_u_pos (u : I) (hu : u ≠ 0) : 0 < (u : ℝ) :=
  lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))

private theorem nelsen22_convexOn :
    ConvexOn ℝ (Icc 0 (π / 2)) (fun s => 1 - Real.sin s) := by
  have hc := strictConcaveOn_sin_Icc.concaveOn.subset
    (Icc_subset_Icc_right (by linarith [Real.pi_pos])) (convex_Icc 0 (π / 2))
  refine ⟨convex_Icc 0 (π / 2), ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hc.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  nlinarith

private theorem nelsen22_antitoneOn :
    AntitoneOn (fun s => 1 - Real.sin s) (Icc 0 (π / 2)) := by
  intro x hx y hy hxy
  have := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hx.1, Real.pi_pos]) hy.2 hxy
  show 1 - Real.sin y ≤ 1 - Real.sin x
  linarith

/-- The clamped pseudo-inverse `s ↦ 1 - sin (min s (π/2))` of Nelsen's family 22 at `θ = 1`.
Its generator is `u ↦ arcsin (1 - u)`. -/
noncomputable def nelsen22BaseGenerator : BivariateGenerator :=
  BivariateGenerator.ofClamp (fun s => 1 - Real.sin s) (π / 2) (by linarith [Real.pi_pos])
    nelsen22_convexOn nelsen22_antitoneOn (by simp) (fun u => Real.arcsin (1 - (u : ℝ)))
    (fun u _ => ⟨Real.arcsin_nonneg.mpr (sub_nonneg.mpr u.property.2),
      Real.arcsin_le_pi_div_two _⟩)
    (fun u v _ huv => Real.arcsin_le_arcsin (sub_le_sub_left (show (u : ℝ) ≤ v from huv) _))
    (by simp)
    (by
      intro u _
      show 1 - Real.sin (Real.arcsin (1 - (u : ℝ))) = (u : ℝ)
      rw [Real.sin_arcsin (by linarith [u.property.2]) (by linarith [u.property.1])]
      ring)

private theorem nelsen22_one_le_inv (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) : 1 ≤ θ⁻¹ :=
  (one_le_inv₀ hθ).mpr h1

/-- The pseudo-inverse `s ↦ (1 - sin (min s (π/2)))^(1/θ)` of Nelsen's family 22, for
`0 < θ ≤ 1`: the `1/θ`-th inner power of `nelsen22BaseGenerator`. -/
noncomputable def nelsen22Generator (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) : BivariateGenerator :=
  nelsen22BaseGenerator.innerPower θ⁻¹ (nelsen22_one_le_inv θ hθ h1)

/-- Nelsen's family 22 for `0 < θ ≤ 1`. -/
noncomputable def nelsen22 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) : Copula 2 :=
  (nelsen22Generator θ hθ h1).copula

theorem isArchimedean_nelsen22 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    IsArchimedean (nelsen22 θ hθ h1) :=
  (nelsen22Generator θ hθ h1).isArchimedean

/-- The generator of Nelsen's family 22 is `u ↦ arcsin (1 - u^θ)`. -/
theorem nelsen22Generator_invFun (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) (u : I) :
    (nelsen22Generator θ hθ h1).invFun u = Real.arcsin (1 - (u : ℝ) ^ θ) := by
  show Real.arcsin (1 - (u : ℝ) ^ (θ⁻¹)⁻¹) = _
  rw [inv_inv]

/-- The pseudo-inverse of family 22 is `s ↦ (1 - sin (min s (π/2)))^(1/θ)`. -/
theorem nelsen22Generator_toFun (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) (s : ℝ) :
    (nelsen22Generator θ hθ h1).toFun s = (1 - Real.sin (min s (π / 2))) ^ θ⁻¹ := rfl

/-- For `a, b ∈ [0, 1]`: `arcsin a + arcsin b ≤ π/2 ↔ a² + b² ≤ 1`. -/
theorem arcsin_add_arcsin_le_pi_div_two_iff {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) : Real.arcsin a + Real.arcsin b ≤ π / 2 ↔ a ^ 2 + b ^ 2 ≤ 1 := by
  have h1 : Real.arcsin a + Real.arcsin b ≤ π / 2 ↔ Real.arcsin a ≤ Real.arccos b := by
    rw [Real.arccos_eq_pi_div_two_sub_arcsin]
    constructor <;> intro h <;> linarith
  have hmemA : Real.arcsin a ∈ Icc (-(π / 2)) (π / 2) :=
    ⟨Real.neg_pi_div_two_le_arcsin a, Real.arcsin_le_pi_div_two a⟩
  have hmemB : Real.arccos b ∈ Icc (-(π / 2)) (π / 2) :=
    ⟨by linarith [Real.arccos_nonneg b, Real.pi_pos], Real.arccos_le_pi_div_two.mpr hb0⟩
  rw [h1, ← Real.strictMonoOn_sin.le_iff_le hmemA hmemB, Real.sin_arcsin (by linarith) ha1,
    Real.sin_arccos, Real.le_sqrt ha0 (by nlinarith)]
  constructor <;> intro h <;> linarith

/-- The CDF of Nelsen's family 22 on positive coordinates, with `a = 1 - u^θ`, `b = 1 - v^θ`:
`C(u, v) = (1 - a √(1 - b²) - b √(1 - a²))^(1/θ)` if `a² + b² ≤ 1` and `0` otherwise.
(Nelsen's printed formula omits the case distinction; see the module docstring.) -/
theorem cdf_nelsen22 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) (u v : I) (hu : u ≠ 0) (hv : v ≠ 0) :
    (nelsen22 θ hθ h1).cdf ![u, v] =
      if (1 - (u : ℝ) ^ θ) ^ 2 + (1 - (v : ℝ) ^ θ) ^ 2 ≤ 1 then
        (1 - (1 - (u : ℝ) ^ θ) * √(1 - (1 - (v : ℝ) ^ θ) ^ 2) -
          (1 - (v : ℝ) ^ θ) * √(1 - (1 - (u : ℝ) ^ θ) ^ 2)) ^ θ⁻¹
      else 0 := by
  have hup := nelsen22_u_pos u hu
  have hvp := nelsen22_u_pos v hv
  have hu1 : (u : ℝ) ^ θ ≤ 1 := Real.rpow_le_one hup.le u.property.2 hθ.le
  have hv1 : (v : ℝ) ^ θ ≤ 1 := Real.rpow_le_one hvp.le v.property.2 hθ.le
  have hu0 := Real.rpow_pos_of_pos hup θ
  have hv0 := Real.rpow_pos_of_pos hvp θ
  have hcdf : (nelsen22 θ hθ h1).cdf ![u, v] = (nelsen22Generator θ hθ h1).cdf u v :=
    BivariateGenerator.cdf_copula _ ![u, v]
  rw [hcdf, BivariateGenerator.cdf, ite_or_of_not hu hv _ _, nelsen22Generator_toFun,
    nelsen22Generator_invFun, nelsen22Generator_invFun]
  set a := 1 - (u : ℝ) ^ θ with ha
  set b := 1 - (v : ℝ) ^ θ with hb
  have ha0 : 0 ≤ a := by linarith
  have ha1 : a ≤ 1 := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hb1 : b ≤ 1 := by linarith
  split_ifs with h
  · have hle := (arcsin_add_arcsin_le_pi_div_two_iff ha0 ha1 hb0 hb1).mpr h
    rw [min_eq_left hle, Real.sin_add, Real.sin_arcsin (by linarith) ha1,
      Real.sin_arcsin (by linarith) hb1, Real.cos_arcsin, Real.cos_arcsin]
    congr 1
    ring
  · have hlt : π / 2 < Real.arcsin a + Real.arcsin b :=
      lt_of_not_ge (fun hle => h ((arcsin_add_arcsin_le_pi_div_two_iff ha0 ha1 hb0 hb1).mp hle))
    rw [min_eq_right hlt.le, Real.sin_pi_div_two, sub_self,
      Real.zero_rpow (inv_ne_zero hθ.ne')]

/-- Nelsen's family 22 on the whole closed unit square, with grounded zero axes. -/
theorem nelsen22_cdf_full (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) (u v : I) :
    (nelsen22 θ hθ h1).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        if (1 - (u : ℝ) ^ θ) ^ 2 + (1 - (v : ℝ) ^ θ) ^ 2 ≤ 1 then
          (1 - (1 - (u : ℝ) ^ θ) * √(1 - (1 - (v : ℝ) ^ θ) ^ 2) -
            (1 - (v : ℝ) ^ θ) * √(1 - (1 - (u : ℝ) ^ θ) ^ 2)) ^ θ⁻¹
        else 0 := by
  by_cases hu : u = 0
  · subst u
    rw [ite_or_of_left rfl _ _]
    exact (nelsen22 θ hθ h1).cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl
  by_cases hv : v = 0
  · subst v
    rw [ite_or_of_right rfl _ _]
    exact (nelsen22 θ hθ h1).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
  rw [ite_or_of_not hu hv _ _]
  exact cdf_nelsen22 θ hθ h1 u v hu hv

end ProbabilityTheory.Copula
