/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.PermutationSums
import Copula.Rank.Region.RhoTau.CompleteSums

/-! # Order signs and the finite Spearman moment identity -/

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

variable {α : Type*} [LinearOrder α]

def orderSign (i j : α) : ℝ := if i < j then 1 else if j < i then -1 else 0

@[simp] theorem orderSign_self (i : α) : orderSign i i = 0 := by simp [orderSign]

theorem orderSign_skew (i j : α) : orderSign j i = -orderSign i j := by
  rcases lt_trichotomy i j with h | h | h
  · simp [orderSign, h, not_lt_of_ge h.le]
  · subst j; simp
  · simp [orderSign, h, not_lt_of_ge h.le]

theorem orderSign_sq {i j : α} (h : i ≠ j) : (orderSign i j) ^ 2 = 1 := by
  rcases lt_or_gt_of_ne h with h | h <;> simp [orderSign, h, not_lt_of_ge h.le]

theorem orderSign_cycle (i j k : α) :
    orderSign i j - orderSign i k + orderSign j k =
      orderSign i j * orderSign i k * orderSign j k := by
  unfold orderSign
  split_ifs <;> norm_num
  all_goals order

theorem orderSign_mem (i j : α) : orderSign i j ∈ Set.Icc (-1) 1 := by
  unfold orderSign
  split_ifs <;> norm_num

variable {n : ℕ}

theorem permutation_edge_sign (π : Equiv.Perm (Fin n)) {i j : Fin n} (hij : i ≠ j) :
    (permutationSigns π).edge i j = -orderSign i j * orderSign (π i) (π j) := by
  have hπ : π i ≠ π j := fun h => hij (π.injective h)
  rcases lt_or_gt_of_ne hij with h | h <;> rcases lt_or_gt_of_ne hπ with h' | h' <;>
    simp [permutationSigns, IsInversion, orderSign, h, h',
      not_lt_of_ge h.le, not_lt_of_ge h'.le]

theorem permutation_inversion_sign (π : Equiv.Perm (Fin n)) (i j : Fin n) :
    orderSign i j * orderSign (π i) (π j) =
      (if i = j then 0 else 1) - 2 * (permutationSigns π).inversion i j := by
  by_cases h : i = j
  · subst j; simp
  · simp only [h, ite_false, SignData.inversion, permutation_edge_sign π h]
    ring

theorem permutation_triple_sign (π : Equiv.Perm (Fin n)) (i j k : Fin n) :
    (permutationSigns π).triple i j k =
      ((completeSigns : SignData (Fin n)).triple i j k -
        (orderSign i j - orderSign i k + orderSign j k) *
          (orderSign (π i) (π j) - orderSign (π i) (π k) + orderSign (π j) (π k))) / 2 := by
  by_cases hij : i = j
  · subst j
    simp
  by_cases hik : i = k
  · subst k
    simp [orderSign_skew i j, orderSign_skew (π i) (π j)]
  by_cases hjk : j = k
  · subst k
    simp
  rw [complete_triple]
  simp only [hij, hik, hjk, or_self, ite_false]
  rw [orderSign_cycle, orderSign_cycle, SignData.triple,
    permutation_edge_sign π hij, permutation_edge_sign π hik, permutation_edge_sign π hjk]
  ring

end ProbabilityTheory.Copula.RankRegion.RhoTau
