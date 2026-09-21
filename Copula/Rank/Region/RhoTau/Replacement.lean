/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.Endpoint
import Copula.Rank.Region.RhoTau.SmallInversion

open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

def CompleteReplacement {ι : Type*} [Fintype ι] (S : SignData ι) (u : ι → ℝ) : Prop :=
  ∃ m : ℕ, ∃ v : Fin m → ℝ, (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1 ∧
    completeSigns.a v = S.a u ∧ completeSigns.b v ≤ S.b u

theorem CompleteReplacement.transport {ι κ : Type*} [Fintype ι] [Fintype κ]
    {S : SignData ι} {T : SignData κ} {u : ι → ℝ} {v : κ → ℝ}
    (h : CompleteReplacement T v) (ha : T.a v = S.a u) (hb : T.b v ≤ S.b u) :
    CompleteReplacement S u := by
  obtain ⟨m, w, hw, hs, hwa, hwb⟩ := h
  exact ⟨m, w, hw, hs, hwa.trans ha, hwb.trans hb⟩

theorem completeReplacement_small {ι : Type*} [Fintype ι]
    (S : SignData ι) (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (ha : S.a u ≤ 1 / 4) :
    CompleteReplacement S u := by
  obtain ⟨v, hv, hs, he, hb⟩ := small_inversion_complete S u hu ha
  exact ⟨2, v, hv, hs, he, hb⟩

theorem normalized_remainder {n : ℕ} (u : Fin (n + 1) → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hs : ∑ i, u i = 1) (i : Fin (n + 1)) (hi : u i < 1) :
    (∀ j, 0 ≤ u (i.succAbove j) / (1 - u i)) ∧
      (∑ j, u (i.succAbove j) / (1 - u i)) = 1 := by
  have hr : 0 < 1 - u i := sub_pos.mpr hi
  refine ⟨fun j => div_nonneg (hu _) hr.le, ?_⟩
  have he := Fin.sum_univ_succAbove u i
  rw [hs] at he
  rw [← Finset.sum_div]
  apply (div_eq_one_iff_eq (ne_of_gt hr)).mpr
  linarith

/-- Reinsert a stripped endpoint into a complete replacement of the normalized remainder. -/
theorem completeReplacement_endpoint {n : ℕ} (π : Equiv.Perm (Fin (n + 1)))
    (u : Fin (n + 1) → ℝ) (hu : ∀ i, 0 ≤ u i) (hs : ∑ i, u i = 1)
    (i : Fin (n + 1)) (hi : u i < 1)
    (he : ∀ j, j ≠ i → (permutationSigns π).edge i j = 1)
    (hrep : CompleteReplacement (permutationSigns (deletePermutation π i))
      (fun j => u (i.succAbove j) / (1 - u i))) :
    CompleteReplacement (permutationSigns π) u := by
  let r := 1 - u i
  have hr : 0 < r := sub_pos.mpr hi
  let w : Fin n → ℝ := fun j => u (i.succAbove j) / r
  have hwform : r • w = u ∘ i.succAbove := by
    funext j
    dsimp [w]
    field_simp
  have hsum : (∑ j, u (i.succAbove j)) = r := by
    have hh := Fin.sum_univ_succAbove u i
    rw [hs] at hh
    dsimp [r]
    linarith
  obtain ⟨m, v, hv, hvsum, hva, hvb⟩ := hrep
  let V : Fin (m + 1) → ℝ := Fin.cons (u i) (r • v)
  have hVsum : ∑ j, V j = 1 := by
    simp only [V, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hvsum, mul_one]
    dsimp [r]
    ring
  refine ⟨m + 1, V, ?_, hVsum, ?_, ?_⟩
  · intro j
    refine Fin.cases (hu i) (fun k => ?_) j
    exact mul_nonneg hr.le (hv k)
  · have hVa := (complete_cons (r • v) (u i)).1
    have hua := (endpoint_coefficients π u i he).1
    rw [hsum, ← hwform, SignData.a_smul] at hua
    rw [SignData.a_smul, hva] at hVa
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hvsum, mul_one] at hVa
    exact hVa.trans hua.symm
  · have hVb := (complete_cons (r • v) (u i)).2
    have hub := (endpoint_coefficients π u i he).2
    rw [← hwform, SignData.a_smul, SignData.b_smul] at hub
    rw [SignData.a_smul, SignData.b_smul, hva] at hVb
    have hmul := mul_le_mul_of_nonneg_left hvb (show 0 ≤ r ^ 3 by positivity)
    change completeSigns.b V ≤ _
    rw [hVb, hub]
    exact add_le_add_right hmul _

end ProbabilityTheory.Copula.RankRegion.RhoTau
