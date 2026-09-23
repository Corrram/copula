/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.TailDependence.Basic

/-! # Quadrant dependence and tail coefficients -/

open Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

theorem isNQD_hasLowerTailDependence_zero {C : Copula 2} (hC : C.IsNQD) :
    C.HasLowerTailDependence 0 := by
  have hcoe : Tendsto (fun t : I => (t : ℝ)) (𝓝[>] (0 : I)) (𝓝 (0 : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Filter.Eventually.of_forall fun t => (C.lowerTailRatio_mem_Icc t).1) ?_ hcoe
  filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < t)] with t ht
  have ht0 : 0 < (t : ℝ) := ht
  exact (div_le_iff₀ ht0).mpr (hC t t)
theorem isNQD_survivalCopula {C : Copula 2} (hC : C.IsNQD) :
    C.survivalCopula.IsNQD := by
  intro u v
  rw [C.cdf_survivalCopula]
  have h := hC (unitInterval.symm u) (unitInterval.symm v)
  simp only [unitInterval.coe_symm_eq] at h
  nlinarith

theorem isNQD_hasUpperTailDependence_zero {C : Copula 2}
    (hC : C.IsNQD) : C.HasUpperTailDependence 0 :=
  isNQD_hasLowerTailDependence_zero (isNQD_survivalCopula hC)


end ProbabilityTheory.Copula
