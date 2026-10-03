/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.ExtremeValue.PickandsConverse
import Copula.Rank.PowerDiagonal

/-! # Tail coefficients, Blomqvist's beta and Spearman's footrule of extreme-value copulas

The diagonal of a Pickands copula is `t ^ (2 A(1/2))`, so all diagonal-based quantities are
explicit in `A(1/2)`:

* upper tail dependence `λ_U = 2 (1 - A(1/2))` (`hasUpperTailDependence_pickandsCopula`);
* lower tail dependence `λ_L = 0`, unless `A(1/2) = 1/2` (i.e. `C_A = M`), where it is `1`
  (`hasLowerTailDependence_pickandsCopula`);
* Blomqvist's beta `β = 2 ^ (2 (1 - A(1/2))) - 1` (`blomqvistBeta_pickandsCopula`);
* Spearman's footrule `φ = 6 / (2 A(1/2) + 1) - 2` (`spearmanFootrule_pickandsCopula`).

The same statements for an arbitrary bivariate extreme-value copula, in terms of its Pickands
function `pickandsOf C`, are the `IsExtremeValue.*_pickandsOf` versions.

References: G. Gudendorf and J. Segers, *Extreme-value copulas* (2010); H. Joe,
*Dependence Modeling with Copulas* (2014).
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {A : ℝ → ℝ}

/-- Upper tail dependence of a Pickands copula: `λ_U = 2 (1 - A(1/2))`. -/
theorem hasUpperTailDependence_pickandsCopula (hA : IsPickandsFunction A) :
    (pickandsCopula A hA).HasUpperTailDependence (2 * (1 - A (1 / 2))) := by
  have h := (hasPowerDiagonal_pickandsCopula hA).hasUpperTailDependence
  convert h using 1
  ring

/-- Lower tail dependence of a Pickands copula: `λ_L = 0` unless `A(1/2) = 1/2` (`C_A = M`). -/
theorem hasLowerTailDependence_pickandsCopula (hA : IsPickandsFunction A) :
    (pickandsCopula A hA).HasLowerTailDependence (if A (1 / 2) = 1 / 2 then 1 else 0) := by
  have h := (hasPowerDiagonal_pickandsCopula hA).hasLowerTailDependence
  have he : (2 * A (1 / 2) = 1) ↔ A (1 / 2) = 1 / 2 := by
    constructor <;> intro h' <;> linarith
  simpa only [he] using h

/-- Blomqvist's beta of a Pickands copula: `β = 2 ^ (2 (1 - A(1/2))) - 1`. -/
theorem blomqvistBeta_pickandsCopula (hA : IsPickandsFunction A) :
    (pickandsCopula A hA).blomqvistBeta = (2 : ℝ) ^ (2 * (1 - A (1 / 2))) - 1 := by
  rw [(hasPowerDiagonal_pickandsCopula hA).blomqvistBeta]
  congr 2
  ring

/-- Spearman's footrule of a Pickands copula: `φ = 6 / (2 A(1/2) + 1) - 2`. -/
theorem spearmanFootrule_pickandsCopula (hA : IsPickandsFunction A) :
    (pickandsCopula A hA).spearmanFootrule = 6 / (2 * A (1 / 2) + 1) - 2 :=
  (hasPowerDiagonal_pickandsCopula hA).spearmanFootrule

namespace IsExtremeValue

variable {C : Copula 2}

private theorem transfer (hC : C.IsExtremeValue) {P : Copula 2 → Prop}
    (h : P (pickandsCopula (pickandsOf C) hC.isPickandsFunction_pickandsOf)) : P C := by
  rwa [← hC.eq_pickandsCopula] at h

/-- The extremal coefficient of an extreme-value copula is `2 A_C(1/2)`. -/
theorem extremalCoefficient_eq_pickandsOf (hC : C.IsExtremeValue) :
    C.extremalCoefficient = 2 * pickandsOf C (1 / 2) :=
  hC.transfer (P := fun D => D.extremalCoefficient = 2 * pickandsOf C (1 / 2))
    (extremalCoefficient_pickandsCopula _)

/-- `λ_U = 2 (1 - A_C(1/2))` for every bivariate extreme-value copula. -/
theorem hasUpperTailDependence_pickandsOf (hC : C.IsExtremeValue) :
    C.HasUpperTailDependence (2 * (1 - pickandsOf C (1 / 2))) :=
  hC.transfer (P := fun D => D.HasUpperTailDependence (2 * (1 - pickandsOf C (1 / 2))))
    (hasUpperTailDependence_pickandsCopula _)

/-- `β = 2 ^ (2 (1 - A_C(1/2))) - 1` for every bivariate extreme-value copula. -/
theorem blomqvistBeta_pickandsOf (hC : C.IsExtremeValue) :
    C.blomqvistBeta = (2 : ℝ) ^ (2 * (1 - pickandsOf C (1 / 2))) - 1 :=
  hC.transfer (P := fun D => D.blomqvistBeta = (2 : ℝ) ^ (2 * (1 - pickandsOf C (1 / 2))) - 1)
    (blomqvistBeta_pickandsCopula _)

/-- `φ = 6 / (2 A_C(1/2) + 1) - 2` for every bivariate extreme-value copula. -/
theorem spearmanFootrule_pickandsOf (hC : C.IsExtremeValue) :
    C.spearmanFootrule = 6 / (2 * pickandsOf C (1 / 2) + 1) - 2 :=
  hC.transfer (P := fun D => D.spearmanFootrule = 6 / (2 * pickandsOf C (1 / 2) + 1) - 2)
    (spearmanFootrule_pickandsCopula _)

/-- An extreme-value copula is `M` iff `A_C(1/2) = 1/2`. -/
theorem eq_comonotonic_iff_pickandsOf (hC : C.IsExtremeValue) :
    C = comonotonic 2 ↔ pickandsOf C (1 / 2) = 1 / 2 :=
  hC.transfer (P := fun D => D = comonotonic 2 ↔ pickandsOf C (1 / 2) = 1 / 2)
    (pickandsCopula_eq_comonotonic_iff _)

end IsExtremeValue

end ProbabilityTheory.Copula
