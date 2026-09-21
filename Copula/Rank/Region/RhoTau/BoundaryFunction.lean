/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.ArcOrder

open scoped Topology

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

abbrev CoefficientInterval := Set.Icc (-1 : ℝ) 1

noncomputable def parameterAtTau (t : CoefficientInterval) : LowerParameter :=
  (lowerParameter_tau_exists t.property).choose

theorem parameterAtTau_tau (t : CoefficientInterval) : (parameterAtTau t).tau = t :=
  (lowerParameter_tau_exists t.property).choose_spec

/-- The SPT lower boundary, as an order isomorphism of the coefficient interval. -/
noncomputable def boundaryMap (t : CoefficientInterval) : CoefficientInterval :=
  ⟨(parameterAtTau t).rho, (parameterAtTau t).rho_mem⟩

theorem boundaryMap_parameter (p : LowerParameter) :
    (boundaryMap ⟨p.tau, p.tau_mem⟩ : ℝ) = p.rho :=
  ((parameterAtTau ⟨p.tau, p.tau_mem⟩).tau_eq_iff p).mp (parameterAtTau_tau _)

theorem boundaryMap_le_iff (s t : CoefficientInterval) : boundaryMap s ≤ boundaryMap t ↔ s ≤ t := by
  change (parameterAtTau s).rho ≤ (parameterAtTau t).rho ↔ (s : ℝ) ≤ t
  rw [← LowerParameter.order_iff, parameterAtTau_tau, parameterAtTau_tau]

theorem boundaryMap_injective : Function.Injective boundaryMap := by
  intro s t h
  exact le_antisymm ((boundaryMap_le_iff s t).mp h.le) ((boundaryMap_le_iff t s).mp h.ge)

theorem boundaryMap_surjective : Function.Surjective boundaryMap := by
  intro r
  obtain ⟨p, hp⟩ := lowerParameter_rho_exists r.property
  refine ⟨⟨p.tau, p.tau_mem⟩, Subtype.ext ?_⟩
  exact (boundaryMap_parameter p).trans hp

noncomputable def boundaryOrderIso : CoefficientInterval ≃o CoefficientInterval where
  toEquiv := Equiv.ofBijective boundaryMap ⟨boundaryMap_injective, boundaryMap_surjective⟩
  map_rel_iff' := boundaryMap_le_iff _ _

theorem continuous_boundaryMap : Continuous boundaryMap := boundaryOrderIso.continuous

theorem boundaryMap_mono : Monotone boundaryMap := fun s t h => (boundaryMap_le_iff s t).mpr h

end ProbabilityTheory.Copula.RankRegion.RhoTau
