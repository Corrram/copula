/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.SparseVariations

open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau.SignData

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (S : SignData ι)

omit [Fintype ι] [DecidableEq ι] in
theorem triple_zero_permutations (p q r : ι) (h : S.triple p q r = 0) :
    S.triple p r q = 0 ∧ S.triple q p r = 0 ∧ S.triple q r p = 0 ∧
      S.triple r p q = 0 ∧ S.triple r q p = 0 := by
  have h₁ : S.triple p r q = 0 := by rw [S.triple_swap_right]; exact h
  have h₂ : S.triple q p r = 0 := by rw [S.triple_swap_left]; exact h
  have h₃ : S.triple q r p = 0 := by rw [S.triple_swap_right]; exact h₂
  have h₄ : S.triple r p q = 0 := by rw [S.triple_swap_left]; exact h₁
  have h₅ : S.triple r q p = 0 := by rw [S.triple_swap_left]; exact h₃
  exact ⟨h₁, h₂, h₃, h₄, h₅⟩

theorem a_four_pattern (p q r s : ι) (x y : ℝ)
    (hpq : S.inversion p q = 0) (hrs : S.inversion r s = 0)
    (hpr : S.inversion p r = 1) (hps : S.inversion p s = 1)
    (hqr : S.inversion q r = 1) (hqs : S.inversion q s = 1) :
    S.a (x • spike p + (-x) • spike q + y • spike r + (-y) • spike s) = 0 := by
  simp only [a, S.bilinear_add_left, S.bilinear_add_right,
    S.bilinear_smul_left, S.bilinear_smul_right, S.bilinear_spikes, S.inversion_diagonal]
  rw [S.inversion_symmetric q p, S.inversion_symmetric r p, S.inversion_symmetric s p,
    S.inversion_symmetric r q, S.inversion_symmetric s q, S.inversion_symmetric s r]
  rw [hpq, hrs, hpr, hps, hqr, hqs]
  ring

theorem b_four_zero (p q r s : ι) (x y z w : ℝ)
    (hpqr : S.triple p q r = 0) (hpqs : S.triple p q s = 0)
    (hprs : S.triple p r s = 0) (hqrs : S.triple q r s = 0) :
    S.b (x • spike p + y • spike q + z • spike r + w • spike s) = 0 := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := S.triple_zero_permutations p q r hpqr
  obtain ⟨h₆, h₇, h₈, h₉, h₁₀⟩ := S.triple_zero_permutations p q s hpqs
  obtain ⟨h₁₁, h₁₂, h₁₃, h₁₄, h₁₅⟩ := S.triple_zero_permutations p r s hprs
  obtain ⟨h₁₆, h₁₇, h₁₈, h₁₉, h₂₀⟩ := S.triple_zero_permutations q r s hqrs
  simp only [b, S.trilinear_add_left, S.trilinear_add_middle, S.trilinear_add_right,
    S.trilinear_smul_left, S.trilinear_smul_middle, S.trilinear_smul_right,
    S.trilinear_spikes, S.triple_repeat, S.triple_repeat_right, S.triple_repeat_outer,
    hpqr, hpqs, hprs, hqrs, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
    h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀]
  ring

theorem second_four (p q r s : ι) (x y : ℝ) (u : ι → ℝ) :
    3 * S.trilinear (x • spike p + (-x) • spike q + y • spike r + (-y) • spike s)
      (x • spike p + (-x) • spike q + y • spike r + (-y) • spike s) u =
      -S.pairCoefficient u p q * x ^ 2 +
        (S.pairCoefficient u p r + S.pairCoefficient u q s -
          S.pairCoefficient u p s - S.pairCoefficient u q r) * x * y -
        S.pairCoefficient u r s * y ^ 2 := by
  simp only [S.trilinear_add_left, S.trilinear_add_middle,
    S.trilinear_smul_left, S.trilinear_smul_middle,
    S.trilinear_two_spikes, S.pairCoefficient_diagonal]
  rw [S.pairCoefficient_symmetric u q p, S.pairCoefficient_symmetric u r p,
    S.pairCoefficient_symmetric u s p, S.pairCoefficient_symmetric u r q,
    S.pairCoefficient_symmetric u s q, S.pairCoefficient_symmetric u s r]
  ring

omit [DecidableEq ι] in
theorem four_coefficient_bounds (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (p q r s : ι)
    (hpqr : S.triple p q r = 0) (hpqs : S.triple p q s = 0)
    (hprs : S.triple p r s = 0) (hqrs : S.triple q r s = 0) :
    |S.pairCoefficient u p r + S.pairCoefficient u q s -
      S.pairCoefficient u p s - S.pairCoefficient u q r| ≤ 2 * S.pairCoefficient u p q ∧
    |S.pairCoefficient u p r + S.pairCoefficient u q s -
      S.pairCoefficient u p s - S.pairCoefficient u q r| ≤ 2 * S.pairCoefficient u r s := by
  have hpr := S.pairCoefficient_triangle u hu p r q
    (by rw [S.triple_swap_right]; exact hpqr)
  have hqr := S.pairCoefficient_triangle u hu q r p
    (by rw [S.triple_swap_right, S.triple_swap_left]; exact hpqr)
  have hps := S.pairCoefficient_triangle u hu p s q
    (by rw [S.triple_swap_right]; exact hpqs)
  have hqs := S.pairCoefficient_triangle u hu q s p
    (by rw [S.triple_swap_right, S.triple_swap_left]; exact hpqs)
  have hpr' := S.pairCoefficient_triangle u hu p r s hprs
  have hps' := S.pairCoefficient_triangle u hu p s r
    (by rw [S.triple_swap_right]; exact hprs)
  have hqr' := S.pairCoefficient_triangle u hu q r s hqrs
  have hqs' := S.pairCoefficient_triangle u hu q s r
    (by rw [S.triple_swap_right]; exact hqrs)
  simp only [S.pairCoefficient_symmetric u r q, S.pairCoefficient_symmetric u q p,
    S.pairCoefficient_symmetric u r p, S.pairCoefficient_symmetric u s q,
    S.pairCoefficient_symmetric u s p, S.pairCoefficient_symmetric u s r] at *
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith


/-- The second forbidden pattern also admits a boundary reduction preserving a. -/
theorem four_pattern_reduction (u : ι → ℝ) (hu : ∀ i, 0 < u i)
    (p q r s : ι) (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (_hqs : q ≠ s) (hrs : r ≠ s)
    (hpq' : S.inversion p q = 0) (hrs' : S.inversion r s = 0)
    (hpr' : S.inversion p r = 1) (hps' : S.inversion p s = 1)
    (hqr' : S.inversion q r = 1) (hqs' : S.inversion q s = 1)
    (hpqr : S.triple p q r = 0) (hpqs : S.triple p q s = 0)
    (hprs : S.triple p r s = 0) (hqrs : S.triple q r s = 0) :
    ∃ v : ι → ℝ, (∀ i, 0 ≤ v i) ∧ (∑ i, v i) = ∑ i, u i ∧
      (∃ i, v i = 0) ∧ S.a v = S.a u ∧ S.b v ≤ S.b u := by
  obtain ⟨x, y, hne, hlin⟩ := exists_four_direction
    (S.bilinear (spike p) u) (S.bilinear (spike q) u)
    (S.bilinear (spike r) u) (S.bilinear (spike s) u)
  let δ := x • spike p + (-x) • spike q + y • spike r + (-y) • spike s
  have hδsum : ∑ i, δ i = 0 := by
    simp [δ, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hδne : ∃ i, δ i ≠ 0 := by
    rcases hne with hx | hy
    · exact ⟨p, by simpa [δ, spike, hpq, hpr, hps] using hx⟩
    · exact ⟨r, by simpa [δ, spike, Ne.symm hpr, Ne.symm hqr, hrs] using hy⟩
  have halin : S.bilinear δ u = 0 := by
    dsimp only [δ]
    simp only [S.bilinear_add_left, S.bilinear_smul_left]
    nlinarith only [hlin]
  have haquad : S.a δ = 0 := S.a_four_pattern p q r s x y hpq' hrs' hpr' hps' hqr' hqs'
  have hbcube : S.b δ = 0 := S.b_four_zero p q r s x (-x) y (-y) hpqr hpqs hprs hqrs
  have hsec : 3 * S.trilinear δ δ u ≤ 0 := by
    dsimp only [δ]
    rw [S.second_four]
    obtain ⟨h₁, h₂⟩ := S.four_coefficient_bounds u (fun i => (hu i).le) p q r s
      hpqr hpqs hprs hqrs
    exact four_quadratic_nonpos h₁ h₂
  obtain ⟨t, _, hnonneg, hzero, hle⟩ := exists_quadratic_boundary_step u δ hu hδsum hδne
    (3 * S.trilinear δ u u) (3 * S.trilinear δ δ u) hsec
  refine ⟨u + t • δ, hnonneg, ?_, hzero, ?_, ?_⟩
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hδsum]
  · rw [S.a_variation, halin, haquad]; ring
  · rw [S.b_variation, hbcube]
    nlinarith only [hle]

end ProbabilityTheory.Copula.RankRegion.RhoTau.SignData
