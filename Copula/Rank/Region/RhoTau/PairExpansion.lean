/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.SparseVariations

open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau.SignData

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (S : SignData ι)

theorem a_add_pair (u : ι → ℝ) (p q : ι) (x y : ℝ) :
    S.a (u + (x • spike p + y • spike q)) = S.a u +
      2 * x * S.bilinear (spike p) u + 2 * y * S.bilinear (spike q) u +
      S.inversion p q * x * y := by
  have h := S.a_variation u (x • spike p + y • spike q) 1
  simp only [one_smul, one_pow, mul_one] at h
  rw [h]
  simp only [a, S.bilinear_add_left, S.bilinear_add_right,
    S.bilinear_smul_left, S.bilinear_smul_right, S.bilinear_spikes, S.inversion_diagonal]
  rw [S.inversion_symmetric q p]
  ring

theorem b_add_pair (u : ι → ℝ) (p q : ι) (x y : ℝ) :
    S.b (u + (x • spike p + y • spike q)) = S.b u +
      3 * x * S.trilinear (spike p) u u + 3 * y * S.trilinear (spike q) u u +
      S.pairCoefficient u p q * x * y := by
  have h := S.b_variation u (x • spike p + y • spike q) 1
  simp only [one_smul, one_pow, mul_one, one_mul] at h
  rw [h]
  simp only [b, S.trilinear_add_left, S.trilinear_add_middle, S.trilinear_add_right,
    S.trilinear_smul_left, S.trilinear_smul_middle, S.trilinear_smul_right,
    S.trilinear_spikes, S.trilinear_two_spikes, S.triple_repeat, S.triple_repeat_right,
    S.triple_repeat_outer, S.pairCoefficient_diagonal]
  rw [S.pairCoefficient_symmetric u q p]
  ring

end ProbabilityTheory.Copula.RankRegion.RhoTau.SignData
