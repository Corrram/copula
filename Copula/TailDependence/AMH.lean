/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.AMH
import Copula.TailDependence.Derivative
import Copula.TailDependence.Clayton

/-! # Exact lower and upper tail dependence of Ali–Mikhail–Haq copulas -/

open Filter Set
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

private theorem amh_diagonal (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1)
    (t : I) :
    (t : ℝ) ^ 2 / (1 - θ * (1 - (t : ℝ)) ^ 2) =
      (amh θ hmin hmax).diagonal t := by
  simpa only [diagonal, pow_two, mul_assoc] using (cdf_amh θ hmin hmax t t).symm

private theorem amh_diagonal_hasDerivAt_zero (θ : ℝ) (hθ : θ < 1) :
    HasDerivAt (fun t : ℝ => t ^ 2 / (1 - θ * (1 - t) ^ 2)) 0 0 := by
  have hn : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
    convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1
    · funext t; rfl
    · norm_num
  have hi := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (0 : ℝ))
  have hd : HasDerivAt (fun t : ℝ => 1 - θ * (1 - t) ^ 2) (2 * θ) 0 := by
    convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
      ((hasDerivAt_const (0 : ℝ) θ).mul (hi.pow 2)) using 1
    · funext t; rfl
    · norm_num; ring
  have hden : 1 - θ * (1 - (0 : ℝ)) ^ 2 ≠ 0 := by
    norm_num
    linarith
  convert hn.div hd hden using 1; norm_num

private theorem amh_diagonal_hasDerivAt_one (θ : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2 / (1 - θ * (1 - t) ^ 2)) 2 1 := by
  have hn : HasDerivAt (fun t : ℝ => t ^ 2) 2 1 := by
    convert (hasDerivAt_id (1 : ℝ)).pow 2 using 1
    · funext t; rfl
    · norm_num
  have hi := (hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (1 : ℝ))
  have hd : HasDerivAt (fun t : ℝ => 1 - θ * (1 - t) ^ 2) 0 1 := by
    convert (hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub
      ((hasDerivAt_const (1 : ℝ) θ).mul (hi.pow 2)) using 1
    · funext t; rfl
    · norm_num
  have hden : 1 - θ * (1 - (1 : ℝ)) ^ 2 ≠ 0 := by norm_num
  convert hn.div hd hden using 1; norm_num

/-- AMH has zero lower-tail dependence for every parameter below one. -/
theorem hasLowerTailDependence_amh_lt_one (θ : ℝ) (hmin : -1 ≤ θ)
    (hmax : θ ≤ 1) (hθ : θ < 1) :
    (amh θ hmin hmax).HasLowerTailDependence 0 :=
  hasLowerTailDependence_of_hasDerivWithinAt
    (amh_diagonal θ hmin hmax)
    (amh_diagonal_hasDerivAt_zero θ hθ).hasDerivWithinAt

/-- The θ=1 AMH endpoint is Clayton(1), with lower-tail coefficient 1/2. -/
theorem hasLowerTailDependence_amh_one :
    (amh 1 (by norm_num) le_rfl).HasLowerTailDependence (1 / 2) := by
  simpa [amh, Real.rpow_neg_one] using
    hasLowerTailDependence_clayton_positive 1 zero_lt_one

/-- Every admissible AMH parameter has zero upper-tail dependence. -/
theorem hasUpperTailDependence_amh (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) :
    (amh θ hmin hmax).HasUpperTailDependence 0 := by
  have h := hasUpperTailDependence_of_hasDerivWithinAt
    (amh_diagonal θ hmin hmax)
    (amh_diagonal_hasDerivAt_one θ).hasDerivWithinAt
  simpa using h

end ProbabilityTheory.Copula
