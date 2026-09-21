/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.Deletion
import Copula.Rank.Region.RhoTau.PairExpansion
import Copula.Rank.Region.RhoTau.CompleteSums

open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

namespace SignData

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (S : SignData ι)

omit [DecidableEq ι] in
theorem a_smul (u : ι → ℝ) (r : ℝ) : S.a (r • u) = r ^ 2 * S.a u := by
  simp only [a, S.bilinear_smul_left, S.bilinear_smul_right]
  ring

omit [DecidableEq ι] in
theorem b_smul (u : ι → ℝ) (r : ℝ) : S.b (r • u) = r ^ 3 * S.b u := by
  simp only [b, S.trilinear_smul_left, S.trilinear_smul_middle, S.trilinear_smul_right]
  ring

theorem bilinear_spike (i : ι) (v : ι → ℝ) :
    S.bilinear (spike i) v = (∑ j, S.inversion i j * v j) / 2 := by
  simp [bilinear, spike, mul_ite, ite_mul]

theorem trilinear_spike (i : ι) (u v : ι → ℝ) :
    S.trilinear (spike i) u v = (∑ j, ∑ k, S.triple i j k * u j * v k) / 6 := by
  simp [trilinear, spike, mul_ite, ite_mul]

theorem endpoint_expansion (i : ι) (v : ι → ℝ) (hvi : v i = 0)
    (he : ∀ j, j ≠ i → S.edge i j = 1) (x : ℝ) :
    S.a (v + x • spike i) = x * (∑ j, v j) + S.a v ∧
      S.b (v + x • spike i) = x * S.a v + S.b v := by
  have hB : S.bilinear (spike i) v = (∑ j, v j) / 2 := by
    rw [S.bilinear_spike]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j = i
    · subst j; simp [hvi]
    · simp [inversion, he j hji]
  have hT : S.trilinear (spike i) v v = S.a v / 3 := by
    rw [S.trilinear_spike]
    have ht (j k : ι) : S.triple i j k * v j * v k = S.inversion j k * v j * v k := by
      by_cases hji : j = i
      · subst j; simp [hvi]
      by_cases hki : k = i
      · subst k; simp [hvi]
      simp only [triple, inversion, he j hji, he k hki, one_mul]
    simp only [ht, a, bilinear]
    ring
  have ha := S.a_add_pair v i i x 0
  have hb := S.b_add_pair v i i x 0
  simp only [zero_smul, add_zero, mul_zero, hB, hT] at ha hb
  constructor <;> linarith

end SignData

theorem endpoint_coefficients {n : ℕ} (π : Equiv.Perm (Fin (n + 1)))
    (u : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (he : ∀ j, j ≠ i → (permutationSigns π).edge i j = 1) :
    (permutationSigns π).a u = u i * (∑ j, u (i.succAbove j)) +
      (permutationSigns (deletePermutation π i)).a (u ∘ i.succAbove) ∧
    (permutationSigns π).b u = u i *
      (permutationSigns (deletePermutation π i)).a (u ∘ i.succAbove) +
      (permutationSigns (deletePermutation π i)).b (u ∘ i.succAbove) := by
  let v := Function.update u i 0
  have hvi : v i = 0 := by simp [v]
  have hvu : v ∘ i.succAbove = u ∘ i.succAbove := by
    funext j
    simp [v, i.succAbove_ne j]
  have hform : v + u i • spike i = u := by
    funext j
    by_cases hji : j = i <;> simp [v, spike, hji]
  obtain ⟨hs, ha, hb⟩ := delete_zero_weight π v i hvi
  rw [hvu] at ha hb
  have hs' : (∑ j, v j) = ∑ j, u (i.succAbove j) := by
    rw [← hs]
    apply Finset.sum_congr rfl
    intro j _
    exact congrFun hvu j
  obtain ⟨h₁, h₂⟩ := (permutationSigns π).endpoint_expansion i v hvi he (u i)
  rw [hform, hs', ← ha] at h₁
  rw [hform, ← ha, ← hb] at h₂
  exact ⟨h₁, h₂⟩

theorem complete_cons {m : ℕ} (v : Fin m → ℝ) (x : ℝ) :
    completeSigns.a (Fin.cons x v) = x * (∑ j, v j) + completeSigns.a v ∧
      completeSigns.b (Fin.cons x v) = x * completeSigns.a v + completeSigns.b v := by
  rw [complete_a, complete_a, complete_b, complete_b]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  constructor <;> ring

end ProbabilityTheory.Copula.RankRegion.RhoTau
