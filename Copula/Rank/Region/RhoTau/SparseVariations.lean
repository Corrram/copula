/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.Multilinear
import Copula.Rank.Region.RhoTau.Perturbation

open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def spike (i : ι) : ι → ℝ := fun j => if j = i then 1 else 0

@[simp] theorem sum_spike (i : ι) : ∑ j, spike i j = 1 := by simp [spike]

namespace SignData

variable (S : SignData ι)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem triple_repeat_right (i j : ι) : S.triple i j j = 0 := by
  rw [S.triple_swap_left, S.triple_swap_right, S.triple_repeat]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem triple_repeat_outer (i j : ι) : S.triple i j i = 0 := by
  rw [S.triple_swap_right, S.triple_repeat]

theorem bilinear_spikes (i j : ι) : S.bilinear (spike i) (spike j) = S.inversion i j / 2 := by
  simp [bilinear, spike, mul_ite]

theorem trilinear_spikes (i j k : ι) :
    S.trilinear (spike i) (spike j) (spike k) = S.triple i j k / 6 := by
  simp [trilinear, spike, mul_ite]

theorem trilinear_two_spikes (i j : ι) (u : ι → ℝ) :
    S.trilinear (spike i) (spike j) u = S.pairCoefficient u i j / 6 := by
  simp [trilinear, spike, mul_ite, ite_mul, pairCoefficient]

omit [DecidableEq ι] in
@[simp] theorem pairCoefficient_diagonal (i : ι) (u : ι → ℝ) :
    S.pairCoefficient u i i = 0 := by simp [pairCoefficient]

theorem a_three (p q r : ι) (x y z : ℝ) :
    S.a (x • spike p + y • spike q + z • spike r) =
      S.inversion p q * x * y + S.inversion p r * x * z + S.inversion q r * y * z := by
  simp only [a, S.bilinear_add_left, S.bilinear_add_right,
    S.bilinear_smul_left, S.bilinear_smul_right, S.bilinear_spikes, S.inversion_diagonal]
  rw [S.inversion_symmetric q p, S.inversion_symmetric r p, S.inversion_symmetric r q]
  ring

theorem b_three (p q r : ι) (x y z : ℝ) :
    S.b (x • spike p + y • spike q + z • spike r) = S.triple p q r * x * y * z := by
  simp only [b, S.trilinear_add_left, S.trilinear_add_middle, S.trilinear_add_right,
    S.trilinear_smul_left, S.trilinear_smul_middle, S.trilinear_smul_right,
    S.trilinear_spikes, S.triple_repeat, S.triple_repeat_right, S.triple_repeat_outer]
  rw [S.triple_swap_right p r q, S.triple_swap_left q p r,
    S.triple_swap_right q r p, S.triple_swap_left q p r,
    S.triple_swap_left r p q, S.triple_swap_right p r q,
    S.triple_swap_left r q p, S.triple_swap_right q r p, S.triple_swap_left q p r]
  ring

theorem second_three (p q r : ι) (x y z : ℝ) (u : ι → ℝ) :
    3 * S.trilinear (x • spike p + y • spike q + z • spike r)
      (x • spike p + y • spike q + z • spike r) u =
      S.pairCoefficient u p q * x * y + S.pairCoefficient u p r * x * z +
        S.pairCoefficient u q r * y * z := by
  simp only [S.trilinear_add_left, S.trilinear_add_middle,
    S.trilinear_smul_left, S.trilinear_smul_middle,
    S.trilinear_two_spikes, S.pairCoefficient_diagonal]
  rw [S.pairCoefficient_symmetric u q p, S.pairCoefficient_symmetric u r p,
    S.pairCoefficient_symmetric u r q]
  ring

/-- The increasing-triple direction preserves the quadratic and decreases
the cubic at a simplex boundary, as in Lemmas 4.6(i) and 4.7. -/
theorem increasing_triple_reduction (u : ι → ℝ) (hu : ∀ i, 0 < u i)
    (p q r : ι) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpq' : S.inversion p q = 0) (hpr' : S.inversion p r = 0)
    (hqr' : S.inversion q r = 0) (ht : S.triple p q r = 0) :
    ∃ v : ι → ℝ, (∀ i, 0 ≤ v i) ∧ (∑ i, v i) = ∑ i, u i ∧
      (∃ i, v i = 0) ∧ S.a v = S.a u ∧ S.b v ≤ S.b u := by
  obtain ⟨x, y, z, hne, hsum, hlin⟩ := exists_three_direction
    (S.bilinear (spike p) u) (S.bilinear (spike q) u) (S.bilinear (spike r) u)
  let δ := x • spike p + y • spike q + z • spike r
  have hδsum : ∑ i, δ i = 0 := by
    simpa [δ, Finset.sum_add_distrib, ← Finset.mul_sum] using hsum
  have hδne : ∃ i, δ i ≠ 0 := by
    rcases hne with hx | hy | hz
    · exact ⟨p, by simpa [δ, spike, hpq, hpr] using hx⟩
    · exact ⟨q, by simpa [δ, spike, Ne.symm hpq, hqr] using hy⟩
    · exact ⟨r, by simpa [δ, spike, Ne.symm hpr, Ne.symm hqr] using hz⟩
  have halin : S.bilinear δ u = 0 := by
    simpa [δ, S.bilinear_add_left, S.bilinear_smul_left, mul_comm] using hlin
  have haquad : S.a δ = 0 := by dsimp only [δ]; rw [S.a_three, hpq', hpr', hqr']; ring
  have hbcube : S.b δ = 0 := by dsimp only [δ]; rw [S.b_three, ht]; ring
  have hsec : 3 * S.trilinear δ δ u ≤ 0 := by
    dsimp only [δ]
    rw [S.second_three]
    apply triple_quadratic_nonpos
      (S.pairCoefficient_nonneg u (fun i => (hu i).le) p q)
      (S.pairCoefficient_nonneg u (fun i => (hu i).le) p r)
      (S.pairCoefficient_nonneg u (fun i => (hu i).le) q r)
      (S.pairCoefficient_triangle u (fun i => (hu i).le) p q r ht)
    · have hh := S.pairCoefficient_triangle u (fun i => (hu i).le) p r q
        (by rw [S.triple_swap_right]; exact ht)
      simpa only [S.pairCoefficient_symmetric u r q] using hh
    · have hh := S.pairCoefficient_triangle u (fun i => (hu i).le) q r p
        (by rw [S.triple_swap_right, S.triple_swap_left]; exact ht)
      simpa only [S.pairCoefficient_symmetric u q p, S.pairCoefficient_symmetric u r p] using hh
    · exact hsum
  obtain ⟨t, _, hnonneg, hzero, hle⟩ := exists_quadratic_boundary_step u δ hu hδsum hδne
    (3 * S.trilinear δ u u) (3 * S.trilinear δ δ u) hsec
  refine ⟨u + t • δ, hnonneg, ?_, hzero, ?_, ?_⟩
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hδsum]
  · rw [S.a_variation, halin, haquad]; ring
  · rw [S.b_variation, hbcube]
    nlinarith only [hle]

end SignData
end ProbabilityTheory.Copula.RankRegion.RhoTau
