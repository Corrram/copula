/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Order.Schur
import Copula.Archimedean.Symmetry

/-! # Schur comparison in both coordinate directions

This distinguishes the paper's two-direction comparison from the directional
`SchurLE` used for Chatterjee's xi.
-/

namespace ProbabilityTheory.Copula

/-- Schur comparison of both conditional distributions. -/
def SchurBothLE (C D : Copula 2) : Prop := C.SchurLE D ∧ C.transpose.SchurLE D.transpose

@[refl] theorem SchurBothLE.refl (C : Copula 2) : C.SchurBothLE C :=
  ⟨SchurLE.refl _, SchurLE.refl _⟩

@[trans] theorem SchurBothLE.trans {C D E : Copula 2} (h : C.SchurBothLE D)
    (k : D.SchurBothLE E) : C.SchurBothLE E := ⟨h.1.trans k.1, h.2.trans k.2⟩

@[simp] theorem schurBothLE_transpose_iff (C D : Copula 2) :
    C.transpose.SchurBothLE D.transpose ↔ C.SchurBothLE D := by
  simp only [SchurBothLE, transpose_transpose, and_comm]

theorem schurBothLE_iff_of_exchangeable {C D : Copula 2}
    (hC : C.IsExchangeable) (hD : D.IsExchangeable) : C.SchurBothLE D ↔ C.SchurLE D := by
  change C.transpose = C at hC
  change D.transpose = D at hD
  simp only [SchurBothLE, hC, hD, and_self]

theorem schurBothLE_iff_of_archimedean {C D : Copula 2}
    (hC : C.IsArchimedean) (hD : D.IsArchimedean) : C.SchurBothLE D ↔ C.SchurLE D :=
  schurBothLE_iff_of_exchangeable hC.isExchangeable hD.isExchangeable

end ProbabilityTheory.Copula
