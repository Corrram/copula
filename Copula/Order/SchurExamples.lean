/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Order.Schur
import Copula.Order.Rank
import Copula.Rank.ConditionalDistance

/-! # Minimality and contrasting examples for Schur order -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The least Schur equivalence class contains only independence. -/
theorem schurLE_independence_iff (C : Copula 2) :
    C.SchurLE (independence 2) ↔ C = independence 2 := by
  refine ⟨fun h => ?_, fun h => h ▸ SchurLE.refl _⟩
  apply C.chatterjeeXi_eq_zero_iff.1
  have hs := h.chatterjeeXi_le
  rw [chatterjeeXi_independence] at hs
  exact le_antisymm hs C.chatterjeeXi_nonneg

theorem schurLE_not_antisymmetric :
    ¬ ∀ C D : Copula 2, C.SchurLE D → D.SchurLE C → C = D := by
  intro h
  have he := congrArg blomqvistBeta
    (h (comonotonic 2) countermonotonic (schurLE_countermonotonic _) (schurLE_comonotonic _))
  norm_num at he

/-- Concordance comparison does not imply Schur comparison. -/
theorem not_schurLE_countermonotonic_independence :
    ¬ countermonotonic.SchurLE (independence 2) := by
  intro h
  have hi := h.chatterjeeXi_le
  norm_num at hi

/-- Schur comparison does not imply concordance comparison. -/
theorem not_lowerOrthantLE_comonotonic_countermonotonic :
    ¬ (comonotonic 2).LowerOrthantLE countermonotonic := by
  intro h
  have hi := h.blomqvistBeta_le
  norm_num at hi

end ProbabilityTheory.Copula
