/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.PermutationSums
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Removing a zero-weight strip from a permutation -/

open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

variable {n : ℕ}

def deletePermutation (π : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    Equiv.Perm (Fin n) :=
  ((finSuccAboveEquiv i).trans
    (π.subtypeEquiv (p := fun j => j ≠ i) (q := fun j => j ≠ π i)
      (fun _j => not_congr π.injective.eq_iff.symm))).trans (finSuccAboveEquiv (π i)).symm

theorem deletePermutation_commute (π : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1))
    (j : Fin n) : π (i.succAbove j) = (π i).succAbove (deletePermutation π i j) := by
  let a : {k : Fin (n + 1) // k ≠ π i} :=
    ⟨π (i.succAbove j), fun h => i.succAbove_ne j (π.injective h)⟩
  exact (congrArg Subtype.val ((finSuccAboveEquiv (π i)).apply_symm_apply a)).symm

theorem delete_inversion (π : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) (j k : Fin n) :
    (permutationSigns π).inversion (i.succAbove j) (i.succAbove k) =
      (permutationSigns (deletePermutation π i)).inversion j k := by
  simp only [permutation_inversion, IsInversion, deletePermutation_commute,
    Fin.succAbove_lt_succAbove_iff]
  rfl

theorem delete_edge (π : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) (j k : Fin n) :
    (permutationSigns π).edge (i.succAbove j) (i.succAbove k) =
      (permutationSigns (deletePermutation π i)).edge j k := by
  have h := delete_inversion π i j k
  dsimp [SignData.inversion] at h
  linarith

theorem delete_triple (π : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) (j k l : Fin n) :
    (permutationSigns π).triple (i.succAbove j) (i.succAbove k) (i.succAbove l) =
      (permutationSigns (deletePermutation π i)).triple j k l := by
  simp only [SignData.triple, delete_edge]

theorem delete_zero_weight (π : Equiv.Perm (Fin (n + 1))) (u : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (hi : u i = 0) :
    (∑ j, u (i.succAbove j)) = ∑ j, u j ∧
      (permutationSigns (deletePermutation π i)).a (u ∘ i.succAbove) = (permutationSigns π).a u ∧
      (permutationSigns (deletePermutation π i)).b (u ∘ i.succAbove) = (permutationSigns π).b u := by
  have hs (f : Fin (n + 1) → ℝ) (hf : f i = 0) :
      (∑ j, f j) = ∑ j, f (i.succAbove j) := by
    rw [Fin.sum_univ_succAbove f i, hf, zero_add]
  refine ⟨(hs u hi).symm, ?_, ?_⟩
  · simp only [SignData.a, SignData.bilinear, Function.comp_apply]
    symm
    congr 1
    rw [hs _ (by simp [hi])]
    apply Finset.sum_congr rfl
    intro j _
    rw [hs _ (by simp [hi])]
    simp only [delete_inversion]
  · simp only [SignData.b, SignData.trilinear, Function.comp_apply]
    symm
    congr 1
    rw [hs _ (by simp [hi])]
    apply Finset.sum_congr rfl
    intro j _
    rw [hs _ (by simp [hi])]
    apply Finset.sum_congr rfl
    intro k _
    rw [hs _ (by simp [hi])]
    simp only [delete_triple]

end ProbabilityTheory.Copula.RankRegion.RhoTau
