/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.AdjacentSwap
import Copula.Rank.Region.RhoTau.SmallInversion

open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

theorem nonendpoint_improvement {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin (n + 2)))
    (u : Fin (n + 2) → ℝ) (hu : ∀ i, 0 < u i)
    (h123 : NoIncreasingTriple π) (h3412 : No3412 π)
    (hfirst : π 0 ≠ Fin.last (n + 1)) (hlast : π (Fin.last (n + 1)) ≠ 0) :
    ∃ σ : Equiv.Perm (Fin (n + 2)), ∃ w : Fin (n + 2) → ℝ,
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = ∑ i, u i ∧
      (permutationSigns σ).a w = (permutationSigns π).a u ∧
      (permutationSigns σ).b w < (permutationSigns π).b u := by
  rcases extrema_orientation π h3412 hfirst hlast with hforward | hinverse
  · exact adjacent_extremal_improvement π u hu (extremal_entries_adjacent π h123 hforward)
      (π.apply_symm_apply _) (π.apply_symm_apply _) (exists_third_index (by omega) _ _)
  · have ho : π.symm.symm 0 < π.symm.symm (Fin.last (n + 1)) := by simpa using hinverse
    obtain ⟨σ, w, hw, hs, ha, hb⟩ := adjacent_extremal_improvement π.symm (u ∘ π.symm)
      (fun i => hu (π.symm i)) (extremal_entries_adjacent π.symm h123.inverse ho)
      (π.symm.apply_symm_apply _) (π.symm.apply_symm_apply _)
      (exists_third_index (by omega) _ _)
    obtain ⟨ha', hb'⟩ := inverse_coefficients π u
    refine ⟨σ, w, hw, ?_, ha.trans ha', ?_⟩
    · rw [hs]
      exact Equiv.sum_comp π.symm u
    · rwa [hb'] at hb

theorem first_maximum_edges {n : ℕ} (π : Equiv.Perm (Fin (n + 1)))
    (h : π 0 = Fin.last n) : ∀ j, j ≠ 0 → (permutationSigns π).edge 0 j = 1 := by
  intro j hj
  have hjpos : 0 < j := Fin.pos_iff_ne_zero.mpr hj
  have hmax : π j ≠ Fin.last n := fun he => hj (π.injective (he.trans h.symm))
  have hjmax : π j < π 0 := by rw [h]; exact Fin.lt_last_iff_ne_last.mpr hmax
  exact edge_of_inversion_one _ (inversion_of_decreasing π hjpos hjmax)

theorem last_minimum_edges {n : ℕ} (π : Equiv.Perm (Fin (n + 1)))
    (h : π (Fin.last n) = 0) :
    ∀ j, j ≠ Fin.last n → (permutationSigns π).edge (Fin.last n) j = 1 := by
  intro j hj
  have hjlt := Fin.lt_last_iff_ne_last.mpr hj
  have hj0 : π j ≠ 0 := fun he => hj (π.injective (he.trans h.symm))
  have hjpos : π (Fin.last n) < π j := by rw [h]; exact Fin.pos_iff_ne_zero.mpr hj0
  rw [(permutationSigns π).symmetric]
  exact edge_of_inversion_one _ (inversion_of_decreasing π hjlt hjpos)

end ProbabilityTheory.Copula.RankRegion.RhoTau
