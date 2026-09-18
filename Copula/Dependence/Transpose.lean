/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.TotalPositivity
import Copula.Transform

/-! # Coordinate direction and symmetric dependence properties -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

@[simp] theorem cdf_reindex_swap (C : Copula 2) (u v : I) :
    (C.reindex ![1, 0]).cdf ![u, v] = C.cdf ![v, u] := by
  rw [cdf, toMeasure_reindex, map_measureReal_apply
    (Measurable.of_eval fun i => measurable_pi_apply _) measurableSet_Iic]
  congr 1
  ext x
  simp [Pi.le_def, Fin.forall_fin_two, and_comm]

theorem reindex_swap_swap (C : Copula 2) : (C.reindex ![1, 0]).reindex ![1, 0] = C := by
  rw [reindex_reindex]
  have he : (![1, 0] : Fin 2 → Fin 2) ∘ ![1, 0] = id := by
    ext i; fin_cases i <;> rfl
  rw [he, reindex_id]

theorem IsPQD.reindex_swap {C : Copula 2} (h : C.IsPQD) : (C.reindex ![1, 0]).IsPQD := by
  intro u v
  simpa [mul_comm] using h v u

theorem isPQD_reindex_swap_iff (C : Copula 2) : (C.reindex ![1, 0]).IsPQD ↔ C.IsPQD :=
  ⟨fun h => by simpa only [reindex_swap_swap] using h.reindex_swap, IsPQD.reindex_swap⟩

theorem IsTP2CDF.reindex_swap {C : Copula 2} (h : C.IsTP2CDF) :
    (C.reindex ![1, 0]).IsTP2CDF := by
  intro a b c d hab hcd
  simpa using h.swap a b c d hab hcd

theorem isTP2CDF_reindex_swap_iff (C : Copula 2) :
    (C.reindex ![1, 0]).IsTP2CDF ↔ C.IsTP2CDF :=
  ⟨fun h => by simpa only [reindex_swap_swap] using h.reindex_swap, IsTP2CDF.reindex_swap⟩

/-- CDF-TP2 also implies LTD in the opposite coordinate direction. -/
theorem IsTP2CDF.isLTD_swap {C : Copula 2} (h : C.IsTP2CDF) :
    (C.reindex ![1, 0]).IsLTD := h.reindex_swap.isLTD

end ProbabilityTheory.Copula
