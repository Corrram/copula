/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Transform.MaxProduct
import Copula.Independence
import Copula.Comonotonic
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! # Extreme-value copulas and closure under power products

The defining identity is max-stability: `C(u₁^t,...,u_d^t) = C(u)^t` for
every positive real `t`. All coordinates of the closed cube are included.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- The max-stability characterization of an extreme-value copula. -/
def IsExtremeValue (C : Copula d) : Prop :=
  ∀ (u : Fin d → I) (t : ℝ) (ht : 0 < t),
    C.cdf (fun i => unitPower (u i) t ht.le) = (C.cdf u) ^ t

theorem isExtremeValue_independence (d : ℕ) : IsExtremeValue (independence d) := by
  intro u t ht
  simp only [cdf_independence, coe_unitPower]
  exact Real.finsetProd_rpow _ _ (fun i _ => (u i).property.1) t

theorem isExtremeValue_comonotonic (d : ℕ) : IsExtremeValue (comonotonic d) := by
  intro u t ht
  simp only [cdf_comonotonic]
  cases d with
  | zero => simp
  | succ n =>
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := u)
    have he : (⨅ i, unitPower (u i) t ht.le) = unitPower (u j) t ht.le := by
      apply le_antisymm (iInf_le _ j)
      apply le_iInf
      intro i
      exact Real.rpow_le_rpow (u j).property.1 (hj.trans_le (iInf_le u i)) ht.le
    rw [he, ← hj]
    rfl

theorem IsExtremeValue.maxProduct {C D : Copula d} (hC : IsExtremeValue C)
    (hD : IsExtremeValue D) (a : Fin d → I) : IsExtremeValue (maxProduct C D a) := by
  intro u t ht
  rw [cdf_maxProduct, cdf_maxProduct]
  have he (w : Fin d → I) :
      (fun i => unitPower (unitPower (u i) t ht.le) (w i) (w i).property.1) =
      (fun i => unitPower (unitPower (u i) (w i) (w i).property.1) t ht.le) := by
    funext i
    simp only [unitPower_mul, mul_comm]
  rw [he a, he (fun i => unitInterval.symm (a i)), hC _ t ht, hD _ t ht,
    Real.mul_rpow (C.cdf_nonneg _) (D.cdf_nonneg _)]

end ProbabilityTheory.Copula
