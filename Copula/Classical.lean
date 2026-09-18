/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rectangle
import Copula.CDF.Extensionality

/-! # The classical copula conditions

This module states the classical boundary and rectangle conditions and proves
them for the CDF of every bundled copula. Normalization is explicit so that
dimension zero is covered. The converse measure construction is separate work.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- The classical conditions on a copula function. Continuity is not assumed. -/
structure IsClassical (F : (Fin d → I) → ℝ) : Prop where
  /-- The top corner has mass one, including in dimension zero. -/
  normalized : F (fun _ => 1) = 1
  /-- A zero coordinate makes the function vanish. -/
  grounded : ∀ (u : Fin d → I) (i : Fin d), u i = 0 → F u = 0
  /-- The one-coordinate boundary faces are uniform. -/
  marginal : ∀ (i : Fin d) (u : I), F (Function.update (fun _ => 1) i u) = (u : ℝ)
  /-- Every ordered rectangle has a nonnegative increment. -/
  increasing : ∀ a b, a ≤ b → 0 ≤ rectangleIncrement F a b

/-- Every measure-based copula satisfies the classical copula conditions. -/
theorem isClassical_cdf (C : Copula d) : IsClassical C.cdf where
  normalized := C.cdf_one
  grounded := C.cdf_eq_zero_of_coord_eq_zero
  marginal := C.cdf_update_one
  increasing := C.rectangleIncrement_cdf_nonneg

/-- There can be at most one copula measure representing a given function. -/
theorem unique_representation (F : (Fin d → I) → ℝ) {C D : Copula d}
    (hC : C.cdf = F) (hD : D.cdf = F) : C = D :=
  cdf_injective (hC.trans hD.symm)

end ProbabilityTheory.Copula
