/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Plackett.Basic
import Copula.TailDependence.Derivative

/-! # Tail independence of the Plackett family

The diagonal `δ(t) = C_θ(t,t)` of a Plackett copula has derivative `0` at `t = 0` (the
discriminant equals `1` there), so `λ_L = 0`; radial symmetry then gives `λ_U = 0`
(Nelsen 2006, §5.4: the Plackett copulas are tail independent for every `θ > 0`).
-/

open Set Filter Topology
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem hasDerivAt_plackettCDF_diagonal_zero (θ : ℝ) :
    HasDerivAt (fun t : ℝ => plackettCDF θ t t) 0 0 := by
  by_cases h1 : θ = 1
  · have h : HasDerivAt (fun t : ℝ => t * t) (1 * 0 + 0 * 1) 0 :=
      (hasDerivAt_id' 0).mul (hasDerivAt_id' 0)
    simp only [mul_zero, zero_mul, add_zero] at h
    convert h using 1
    funext t; simp [plackettCDF, h1]
  · have hL : HasDerivAt (fun t : ℝ => 1 + (θ - 1) * (t + t)) ((θ - 1) * (1 + 1)) 0 :=
      (((hasDerivAt_id' 0).add (hasDerivAt_id' 0)).const_mul (θ - 1)).const_add 1
    have hD : HasDerivAt (fun t : ℝ => (1 + (θ - 1) * (t + t)) ^ 2 - 4 * θ * (θ - 1) * t * t)
        ((2 : ℕ) * (1 + (θ - 1) * (0 + 0)) ^ (2 - 1) * ((θ - 1) * (1 + 1)) -
          (4 * θ * (θ - 1) * 0 * 1 + 4 * θ * (θ - 1) * 1 * 0)) 0 := by
      have h2 := ((hasDerivAt_id' (0 : ℝ)).const_mul (4 * θ * (θ - 1))).mul (hasDerivAt_id' 0)
      have := (hL.pow 2).sub h2
      convert this using 1
      ring
    have hD0 : (1 + (θ - 1) * (0 + 0)) ^ 2 - 4 * θ * (θ - 1) * 0 * 0 = (1 : ℝ) := by ring
    have hs := hD.sqrt (by rw [hD0]; norm_num)
    have h := (hL.sub hs).div_const (2 * (θ - 1))
    have hfun : (fun t : ℝ => plackettCDF θ t t) = fun t =>
        ((1 + (θ - 1) * (t + t)) - √((1 + (θ - 1) * (t + t)) ^ 2 - 4 * θ * (θ - 1) * t * t)) /
          (2 * (θ - 1)) := by
      funext t; rw [plackettCDF_eq_of_ne h1]; rfl
    rw [hfun]
    convert h using 1
    rw [hD0, Real.sqrt_one]
    push_cast
    ring

/-- The Plackett copulas have no lower tail dependence. -/
theorem hasLowerTailDependence_plackett (θ : ℝ) (hθ : 0 < θ) :
    (plackett θ hθ).HasLowerTailDependence 0 :=
  hasLowerTailDependence_of_hasDerivWithinAt (f := fun t : ℝ => plackettCDF θ t t)
    (fun t => by rw [diagonal, cdf_plackett_two])
    (hasDerivAt_plackettCDF_diagonal_zero θ).hasDerivWithinAt

/-- The Plackett copulas have no upper tail dependence. -/
theorem hasUpperTailDependence_plackett (θ : ℝ) (hθ : 0 < θ) :
    (plackett θ hθ).HasUpperTailDependence 0 :=
  ((isRadiallySymmetric_plackett θ hθ).hasUpperTailDependence_iff 0).mpr
    (hasLowerTailDependence_plackett θ hθ)

end ProbabilityTheory.Copula
