/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.GridCollisions
import Copula.Rank.Region.RhoTau.FiniteReduction
import Copula.Rank.Region.RhoTau.BoundaryFunction

open Filter
open scoped Topology BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

noncomputable def gridTau (C : Copula 2) (n : ℕ) : ℝ :=
  1 - 4 * (permutationSigns (gridSwap n)).a (gridWeights C n)

noncomputable def gridRho (C : Copula 2) (n : ℕ) : ℝ :=
  1 - 6 * (permutationSigns (gridSwap n)).a (gridWeights C n) +
    6 * (permutationSigns (gridSwap n)).b (gridWeights C n)

theorem tendsto_gridTau (C : Copula 2) : Tendsto (gridTau C) atTop (𝓝 C.kendallTau) := by
  have ht := (tendsto_grid_squares C).add (tendsto_grid_pair_moment C)
  simp only [zero_add, grid_pair_moment_eq] at ht
  convert ht using 1
  funext n
  exact finite_tau_moment (gridSwap n) (gridWeights C n) (gridWeights_sum C n)

theorem tendsto_gridRho (C : Copula 2) : Tendsto (gridRho C) atTop (𝓝 C.spearmanRho) := by
  have ht := (tendsto_grid_cubes C).add ((tendsto_grid_rank_moment C).const_mul 3)
  simp only [zero_add, integral_rank_product, grid_rank_moment_eq] at ht
  convert ht using 1
  funext n
  exact finite_rho_moment (gridSwap n) (gridWeights C n) (gridWeights_sum C n)

theorem grid_prototype (C : Copula 2) (n : ℕ) :
    ∃ p : LowerParameter, p.tau = gridTau C n ∧ p.rho ≤ gridRho C n := by
  obtain ⟨m, s, ht, hr⟩ := finite_sharp_bound _ (gridSwap n) (gridWeights C n)
    (gridWeights_nonneg C n) (gridWeights_sum C n)
  exact ⟨.arc m s, ht, hr⟩

theorem gridTau_mem (C : Copula 2) (n : ℕ) : gridTau C n ∈ Set.Icc (-1) 1 := by
  obtain ⟨p, hp, _⟩ := grid_prototype C n
  exact hp ▸ p.tau_mem

theorem boundaryMap_grid_le (C : Copula 2) (n : ℕ) :
    (boundaryMap ⟨gridTau C n, gridTau_mem C n⟩ : ℝ) ≤ gridRho C n := by
  obtain ⟨p, hp, hr⟩ := grid_prototype C n
  convert hr using 1
  rw [show (⟨gridTau C n, gridTau_mem C n⟩ : CoefficientInterval) =
    ⟨p.tau, p.tau_mem⟩ from Subtype.ext hp.symm, boundaryMap_parameter]

/-- The universal sharp Schreyer–Paulin–Trutschnig lower bound. -/
theorem boundaryMap_le_rho (C : Copula 2) :
    (boundaryMap ⟨C.kendallTau, C.kendallTau_mem_Icc⟩ : ℝ) ≤ C.spearmanRho := by
  have ht : Tendsto (fun n => (⟨gridTau C n, gridTau_mem C n⟩ : CoefficientInterval)) atTop
      (𝓝 ⟨C.kendallTau, C.kendallTau_mem_Icc⟩) :=
    tendsto_subtype_rng.mpr (tendsto_gridTau C)
  have hb := (continuous_subtype_val.comp continuous_boundaryMap).continuousAt.tendsto.comp ht
  exact le_of_tendsto_of_tendsto hb (tendsto_gridRho C) (Eventually.of_forall (boundaryMap_grid_le C))

theorem universal_lower (C : Copula 2) :
    ∃ p : LowerParameter, p.tau = C.kendallTau ∧ p.rho ≤ C.spearmanRho :=
  ⟨parameterAtTau ⟨C.kendallTau, C.kendallTau_mem_Icc⟩,
    parameterAtTau_tau _, boundaryMap_le_rho C⟩

end ProbabilityTheory.Copula.RankRegion.RhoTau
