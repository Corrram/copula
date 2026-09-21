/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.CycleMoments

open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

variable {n : ℕ}

theorem weighted_inversion_sign (π : Equiv.Perm (Fin n)) (u : Fin n → ℝ)
    (hs : ∑ i, u i = 1) :
    weighted2 u (fun i j => orderSign i j * orderSign (π i) (π j)) =
      1 - ∑ i, (u i) ^ 2 - 4 * (permutationSigns π).a u := by
  have he (i j : Fin n) : u i * u j * (orderSign i j * orderSign (π i) (π j)) =
      completeSigns.inversion i j * u i * u j -
        2 * ((permutationSigns π).inversion i j * u i * u j) := by
    rw [permutation_inversion_sign, complete_inversion]
    ring
  simp only [weighted2, he, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hc := complete_a u
  rw [hs] at hc
  dsimp only [SignData.a, SignData.bilinear] at hc ⊢
  linarith

/-- Spearman's finite permutation statistic, including the diagonal correction. -/
theorem finite_rho_moment (π : Equiv.Perm (Fin n)) (u : Fin n → ℝ)
    (hs : ∑ i, u i = 1) :
    1 - 6 * (permutationSigns π).a u + 6 * (permutationSigns π).b u =
      (∑ i, (u i) ^ 3) +
        3 * ∑ i, u i * (∑ j, orderSign i j * u j) *
          (∑ k, orderSign (π i) (π k) * u k) := by
  have hcycle := weighted_cycle_product u hs orderSign
    (fun i j => orderSign (π i) (π j)) orderSign_skew
    (fun i j => orderSign_skew (π i) (π j))
  rw [weighted_inversion_sign π u hs] at hcycle
  have htriple : 12 * (permutationSigns π).b u =
      6 * completeSigns.b u -
        weighted3 u (fun i j k =>
          (orderSign i j - orderSign i k + orderSign j k) *
          (orderSign (π i) (π j) - orderSign (π i) (π k) + orderSign (π j) (π k))) := by
    have he (i j k : Fin n) :
        2 * ((permutationSigns π).triple i j k * u i * u j * u k) =
          completeSigns.triple i j k * u i * u j * u k -
            u i * u j * u k *
              ((orderSign i j - orderSign i k + orderSign j k) *
              (orderSign (π i) (π j) - orderSign (π i) (π k) + orderSign (π j) (π k))) := by
      rw [permutation_triple_sign]
      ring
    have hh := congrArg (fun f : Fin n → Fin n → Fin n → ℝ => ∑ i, ∑ j, ∑ k, f i j k)
      (funext fun i => funext fun j => funext fun k => he i j k)
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hh
    dsimp only [SignData.b, SignData.trilinear, weighted3]
    linarith
  rw [complete_b, hs] at htriple
  linarith

theorem finite_tau_moment (π : Equiv.Perm (Fin n)) (u : Fin n → ℝ)
    (hs : ∑ i, u i = 1) :
    1 - 4 * (permutationSigns π).a u = (∑ i, (u i) ^ 2) +
      weighted2 u (fun i j => orderSign i j * orderSign (π i) (π j)) := by
  rw [weighted_inversion_sign π u hs]
  ring

end ProbabilityTheory.Copula.RankRegion.RhoTau
