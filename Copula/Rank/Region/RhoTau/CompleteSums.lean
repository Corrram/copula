/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.Multilinear
import Copula.Rank.Region.RhoTau.SymmetricMinimum

open scoped BigOperators unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def completeSigns : SignData ι where
  edge i j := if i = j then -1 else 1
  symmetric i j := by simp [eq_comm]
  diagonal i := by simp
  values i j := by split <;> simp

omit [Fintype ι] in
theorem complete_inversion (i j : ι) :
    (completeSigns : SignData ι).inversion i j = if i = j then 0 else 1 := by
  by_cases h : i = j <;> simp [SignData.inversion, completeSigns, h]

omit [Fintype ι] in
theorem complete_triple (i j k : ι) :
    (completeSigns : SignData ι).triple i j k =
      if i = j ∨ i = k ∨ j = k then 0 else 1 := by
  by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hjk : j = k <;>
    simp_all [SignData.triple, completeSigns]

theorem complete_a (u : ι → ℝ) :
    completeSigns.a u = ((∑ i, u i) ^ 2 - ∑ i, (u i) ^ 2) / 2 := by
  have ht (i j : ι) : completeSigns.inversion i j * u i * u j =
      u i * u j - if j = i then (u i) ^ 2 else 0 := by
    rw [complete_inversion]
    by_cases h : j = i
    · subst j; simp; ring
    · simp [h, Ne.symm h]
  simp only [SignData.a, SignData.bilinear, ht, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.mul_sum,
    ← Finset.sum_mul]
  ring

theorem complete_b (u : ι → ℝ) :
    completeSigns.b u = ((∑ i, u i) ^ 3 - 3 * (∑ i, u i) * (∑ i, (u i) ^ 2) +
      2 * ∑ i, (u i) ^ 3) / 6 := by
  have ht (i j k : ι) : completeSigns.triple i j k * u i * u j * u k =
      u i * u j * u k - (if j = i then (u i) ^ 2 * u k else 0) -
        (if k = i then (u i) ^ 2 * u j else 0) -
        (if k = j then u i * (u j) ^ 2 else 0) +
        (if j = i then if k = i then 2 * (u i) ^ 3 else 0 else 0) := by
    rw [complete_triple]
    by_cases hij : j = i
    · subst j
      by_cases hik : k = i
      · subst k; simp; ring
      · simp [hik]; ring
    by_cases hik : k = i
    · subst k; simp [hij, Ne.symm hij]; ring
    by_cases hjk : k = j
    · subst k; simp [hij, Ne.symm hij]; ring
    simp [hij, Ne.symm hij, hik, Ne.symm hik, hjk, Ne.symm hjk]
  simp only [SignData.b, SignData.trilinear, ht, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- The symmetric minimization lemma in the inversion and triple coordinates. -/
theorem complete_minimum_prototype (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hs : ∑ i, u i = 1) :
    ∃ n : ℕ, ∃ s : I,
      (1 - arcTau n s) / 4 = completeSigns.a u ∧
      (arcRho n s - 1 + 6 * completeSigns.a u) / 6 ≤ completeSigns.b u := by
  obtain ⟨n, s, ht, hr⟩ := decreasing_permutation_bound u hu hs
  refine ⟨n, s, ?_, ?_⟩
  · rw [complete_a, hs, ht]
    ring
  · rw [complete_a, complete_b, hs]
    linarith

end ProbabilityTheory.Copula.RankRegion.RhoTau
