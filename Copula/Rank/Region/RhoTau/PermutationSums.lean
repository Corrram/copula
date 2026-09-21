/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.FourVariations
import Copula.Rank.Region.RhoTau.PermutationPatterns

open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

variable {n : ℕ}

def IsInversion (π : Equiv.Perm (Fin n)) (i j : Fin n) : Prop :=
  (i < j ∧ π j < π i) ∨ (j < i ∧ π i < π j)

instance (π : Equiv.Perm (Fin n)) (i j : Fin n) : Decidable (IsInversion π i j) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

def permutationSigns (π : Equiv.Perm (Fin n)) : SignData (Fin n) where
  edge i j := if IsInversion π i j then 1 else -1
  symmetric i j := by simp only [IsInversion, or_comm]; rfl
  diagonal i := by simp [IsInversion]
  values i j := by split <;> simp

theorem permutation_inversion (π : Equiv.Perm (Fin n)) (i j : Fin n) :
    (permutationSigns π).inversion i j = if IsInversion π i j then 1 else 0 := by
  simp only [SignData.inversion, permutationSigns]
  split <;> norm_num

theorem inversion_of_increasing (π : Equiv.Perm (Fin n)) {i j : Fin n}
    (hij : i < j) (hπ : π i < π j) : (permutationSigns π).inversion i j = 0 := by
  rw [permutation_inversion]
  simp [IsInversion, hij, hπ, not_lt_of_ge hij.le, not_lt_of_ge hπ.le]

theorem inversion_of_decreasing (π : Equiv.Perm (Fin n)) {i j : Fin n}
    (hij : i < j) (hπ : π j < π i) : (permutationSigns π).inversion i j = 1 := by
  rw [permutation_inversion]
  simp [IsInversion, hij, hπ]

theorem edge_of_inversion_zero (S : SignData (Fin n)) {i j : Fin n}
    (h : S.inversion i j = 0) : S.edge i j = -1 := by
  dsimp [SignData.inversion] at h
  linarith

theorem edge_of_inversion_one (S : SignData (Fin n)) {i j : Fin n}
    (h : S.inversion i j = 1) : S.edge i j = 1 := by
  dsimp [SignData.inversion] at h
  linarith

theorem triple_of_increasing (π : Equiv.Perm (Fin n)) {i j k : Fin n}
    (hij : i < j) (hjk : j < k) (hpij : π i < π j) (hpjk : π j < π k) :
    (permutationSigns π).triple i j k = 0 := by
  have h₁ := edge_of_inversion_zero _ (inversion_of_increasing π hij hpij)
  have h₂ := edge_of_inversion_zero _ (inversion_of_increasing π (hij.trans hjk) (hpij.trans hpjk))
  have h₃ := edge_of_inversion_zero _ (inversion_of_increasing π hjk hpjk)
  norm_num [SignData.triple, h₁, h₂, h₃]

theorem permutation_increasing_reduction (π : Equiv.Perm (Fin n))
    (u : Fin n → ℝ) (hu : ∀ i, 0 < u i) {p q r : Fin n}
    (hpq : p < q) (hqr : q < r) (hπpq : π p < π q) (hπqr : π q < π r) :
    ∃ v : Fin n → ℝ, (∀ i, 0 ≤ v i) ∧ (∑ i, v i) = ∑ i, u i ∧
      (∃ i, v i = 0) ∧ (permutationSigns π).a v = (permutationSigns π).a u ∧
      (permutationSigns π).b v ≤ (permutationSigns π).b u :=
  (permutationSigns π).increasing_triple_reduction u hu p q r
    (ne_of_lt hpq) (ne_of_lt (hpq.trans hqr)) (ne_of_lt hqr)
    (inversion_of_increasing π hpq hπpq)
    (inversion_of_increasing π (hpq.trans hqr) (hπpq.trans hπqr))
    (inversion_of_increasing π hqr hπqr)
    (triple_of_increasing π hpq hqr hπpq hπqr)

theorem permutation_four_reduction (π : Equiv.Perm (Fin n))
    (u : Fin n → ℝ) (hu : ∀ i, 0 < u i) {p q r s : Fin n}
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (hπrs : π r < π s) (hπsp : π s < π p) (hπpq : π p < π q) :
    ∃ v : Fin n → ℝ, (∀ i, 0 ≤ v i) ∧ (∑ i, v i) = ∑ i, u i ∧
      (∃ i, v i = 0) ∧ (permutationSigns π).a v = (permutationSigns π).a u ∧
      (permutationSigns π).b v ≤ (permutationSigns π).b u := by
  let S := permutationSigns π
  have h₁ : S.inversion p q = 0 := inversion_of_increasing π hpq hπpq
  have h₂ : S.inversion r s = 0 := inversion_of_increasing π hrs hπrs
  have h₃ : S.inversion p r = 1 := inversion_of_decreasing π (hpq.trans hqr) (hπrs.trans hπsp)
  have h₄ : S.inversion p s = 1 := inversion_of_decreasing π ((hpq.trans hqr).trans hrs) hπsp
  have h₅ : S.inversion q r = 1 := inversion_of_decreasing π hqr ((hπrs.trans hπsp).trans hπpq)
  have h₆ : S.inversion q s = 1 := inversion_of_decreasing π (hqr.trans hrs) (hπsp.trans hπpq)
  apply S.four_pattern_reduction u hu p q r s
    (ne_of_lt hpq) (ne_of_lt (hpq.trans hqr)) (ne_of_lt ((hpq.trans hqr).trans hrs))
    (ne_of_lt hqr) (ne_of_lt (hqr.trans hrs)) (ne_of_lt hrs) h₁ h₂ h₃ h₄ h₅ h₆
  all_goals
    simp only [SignData.triple, edge_of_inversion_zero S h₁, edge_of_inversion_zero S h₂,
      edge_of_inversion_one S h₃, edge_of_inversion_one S h₄,
      edge_of_inversion_one S h₅, edge_of_inversion_one S h₆]
    norm_num

end ProbabilityTheory.Copula.RankRegion.RhoTau
