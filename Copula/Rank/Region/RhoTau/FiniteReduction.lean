/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.Nonendpoint
import Copula.Rank.Region.RhoTau.Replacement

open scoped BigOperators unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

theorem finite_boundary_or_endpoint {n : ℕ} (hn : 3 ≤ n)
    (π : Equiv.Perm (Fin n)) (u : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hs : ∑ i, u i = 1) :
    ∃ perm : Equiv.Perm (Fin n), ∃ v : Fin n → ℝ,
      (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1 ∧
      (permutationSigns perm).a v = (permutationSigns π).a u ∧
      (permutationSigns perm).b v ≤ (permutationSigns π).b u ∧
      ((∃ i, v i = 0) ∨ ((∀ i, 0 < v i) ∧
        ∃ i, ∀ j, j ≠ i → (permutationSigns perm).edge i j = 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  obtain ⟨perm, v, hv, hb, hmin⟩ := exists_finite_minimizer π u hu hs
  by_cases hz : ∃ i, v i = 0
  · exact ⟨perm, v, hv.1, hv.2.1, hv.2.2, hb, Or.inl hz⟩
  have hpos (i : Fin (k + 3)) : 0 < v i :=
    lt_of_le_of_ne (hv.1 i) (Ne.symm (fun he => hz ⟨i, he⟩))
  by_cases hfirst : perm 0 = Fin.last (k + 2)
  · exact ⟨perm, v, hv.1, hv.2.1, hv.2.2, hb,
      Or.inr ⟨hpos, 0, first_maximum_edges perm hfirst⟩⟩
  by_cases hlast : perm (Fin.last (k + 2)) = 0
  · exact ⟨perm, v, hv.1, hv.2.1, hv.2.2, hb,
      Or.inr ⟨hpos, Fin.last (k + 2), last_minimum_edges perm hlast⟩⟩
  by_cases h123 : NoIncreasingTriple perm
  · by_cases h3412 : No3412 perm
    · obtain ⟨θ, w, hw, hwSum, ha', hb'⟩ := nonendpoint_improvement
        (n := k + 1) (by omega) perm v hpos h123 h3412 hfirst hlast
      have hh := hmin θ w ⟨hw, hwSum.trans hv.2.1, ha'.trans hv.2.2⟩
      exact False.elim ((not_lt_of_ge hh) hb')
    · unfold No3412 at h3412
      push Not at h3412
      obtain ⟨p, q, r, s, hpq, hqr, hrs, hπrs, hπsp, hπpq⟩ := h3412
      obtain ⟨w, hw, hwSum, hwZero, ha', hb'⟩ :=
        permutation_four_reduction perm v hpos hpq hqr hrs hπrs hπsp hπpq
      exact ⟨perm, w, hw, hwSum.trans hv.2.1, ha'.trans hv.2.2, hb'.trans hb, Or.inl hwZero⟩
  · unfold NoIncreasingTriple at h123
    push Not at h123
    obtain ⟨p, q, r, hpq, hqr, hπpq, hπqr⟩ := h123
    obtain ⟨w, hw, hwSum, hwZero, ha', hb'⟩ :=
      permutation_increasing_reduction perm v hpos hpq hqr hπpq hπqr
    exact ⟨perm, w, hw, hwSum.trans hv.2.1, ha'.trans hv.2.2, hb'.trans hb, Or.inl hwZero⟩

/-- The finite minimization theorem: decreasing permutations suffice. -/
theorem permutation_complete_replacement (n : ℕ) (π : Equiv.Perm (Fin n))
    (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) (hs : ∑ i, u i = 1) :
    CompleteReplacement (permutationSigns π) u := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases ha : (permutationSigns π).a u ≤ 1 / 4
    · exact completeReplacement_small _ _ hu ha
    have hn : 3 ≤ n := by
      by_contra h
      exact ha (a_le_quarter_of_card_le_two (by omega) _ _ hu hs)
    obtain ⟨perm, v, hv, hvSum, hva, hvb, hreduce⟩ := finite_boundary_or_endpoint hn π u hu hs
    apply CompleteReplacement.transport (S := permutationSigns π) (u := u)
      (T := permutationSigns perm) (v := v) _ hva hvb
    cases n with
    | zero => omega
    | succ N =>
      rcases hreduce with hzero | ⟨hpos, i, he⟩
      · obtain ⟨i, hi⟩ := hzero
        obtain ⟨hs', ha', hb'⟩ := delete_zero_weight perm v i hi
        have hrep := ih N (by omega) (deletePermutation perm i) (v ∘ i.succAbove)
          (fun j => hv _) (hs'.trans hvSum)
        exact hrep.transport ha' hb'.le
      · have hrem : 0 < ∑ j, v (i.succAbove j) := by
          have hN : 0 < N := by omega
          let j : Fin N := ⟨0, hN⟩
          exact (hpos (i.succAbove j)).trans_le
            (Finset.single_le_sum (fun l _ => hv _) (Finset.mem_univ j))
        have hi : v i < 1 := by
          have hh := Fin.sum_univ_succAbove v i
          rw [hvSum] at hh
          linarith
        obtain ⟨hw, hwSum⟩ := normalized_remainder v hv hvSum i hi
        exact completeReplacement_endpoint perm v hv hvSum i hi he
          (ih N (by omega) (deletePermutation perm i)
            (fun j => v (i.succAbove j) / (1 - v i)) hw hwSum)

/-- The sharp lower prototype dominates every finite weighted permutation. -/
theorem finite_sharp_bound (n : ℕ) (π : Equiv.Perm (Fin n))
    (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) (hs : ∑ i, u i = 1) :
    ∃ m : ℕ, ∃ s : I,
      arcTau m s = 1 - 4 * (permutationSigns π).a u ∧
      arcRho m s ≤ 1 - 6 * (permutationSigns π).a u + 6 * (permutationSigns π).b u := by
  obtain ⟨m, v, hv, hvSum, ha, hb⟩ := permutation_complete_replacement n π u hu hs
  obtain ⟨k, s, ht, hr⟩ := complete_minimum_prototype v hv hvSum
  rw [ha] at ht hr
  exact ⟨k, s, by linarith, by linarith⟩

end ProbabilityTheory.Copula.RankRegion.RhoTau
