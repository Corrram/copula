/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.Combinatorics

/-! # Polynomial variations of inversion and triple sums

Ordered sums carry the factors 1/2 and 1/6. This avoids choosing an
enumeration of the index set when coordinates vanish during induction.
-/

open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau.SignData

variable {ι : Type*} [Fintype ι] (S : SignData ι)

noncomputable def inversion (i j : ι) : ℝ := (1 + S.edge i j) / 2

noncomputable def bilinear (u v : ι → ℝ) : ℝ :=
  (∑ i, ∑ j, S.inversion i j * u i * v j) / 2

noncomputable def trilinear (u v w : ι → ℝ) : ℝ :=
  (∑ i, ∑ j, ∑ k, S.triple i j k * u i * v j * w k) / 6

noncomputable def a (u : ι → ℝ) : ℝ := S.bilinear u u
noncomputable def b (u : ι → ℝ) : ℝ := S.trilinear u u u

omit [Fintype ι] in
theorem inversion_symmetric (i j : ι) : S.inversion i j = S.inversion j i := by
  simp only [inversion, S.symmetric i j]

omit [Fintype ι] in
@[simp] theorem inversion_diagonal (i : ι) : S.inversion i i = 0 := by
  simp [inversion, S.diagonal]

theorem bilinear_symm (u v : ι → ℝ) : S.bilinear u v = S.bilinear v u := by
  unfold bilinear
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [S.inversion_symmetric i j]
  ring

theorem trilinear_swap_left (u v w : ι → ℝ) :
    S.trilinear u v w = S.trilinear v u w := by
  unfold trilinear
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [S.triple_swap_left i j k]
  ring

theorem trilinear_swap_right (u v w : ι → ℝ) :
    S.trilinear u v w = S.trilinear u w v := by
  unfold trilinear
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  rw [S.triple_swap_right i j k]
  ring

theorem bilinear_add_left (u v w : ι → ℝ) :
    S.bilinear (u + v) w = S.bilinear u w + S.bilinear v w := by
  simp only [bilinear, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  ring

theorem bilinear_smul_left (r : ℝ) (u v : ι → ℝ) :
    S.bilinear (r • u) v = r * S.bilinear u v := by
  simp only [bilinear, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ i j, S.inversion i j * (r * u i) * v j =
    r * (S.inversion i j * u i * v j) by intros; ring]
  simp only [← Finset.mul_sum]
  ring

theorem trilinear_add_left (u v w z : ι → ℝ) :
    S.trilinear (u + v) w z = S.trilinear u w z + S.trilinear v w z := by
  simp only [trilinear, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  ring

theorem trilinear_smul_left (r : ℝ) (u v w : ι → ℝ) :
    S.trilinear (r • u) v w = r * S.trilinear u v w := by
  simp only [trilinear, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ i j k, S.triple i j k * (r * u i) * v j * w k =
    r * (S.triple i j k * u i * v j * w k) by intros; ring]
  simp only [← Finset.mul_sum]
  ring

theorem bilinear_add_right (u v w : ι → ℝ) :
    S.bilinear u (v + w) = S.bilinear u v + S.bilinear u w := by
  rw [S.bilinear_symm, S.bilinear_add_left, S.bilinear_symm v, S.bilinear_symm w]

theorem bilinear_smul_right (r : ℝ) (u v : ι → ℝ) :
    S.bilinear u (r • v) = r * S.bilinear u v := by
  rw [S.bilinear_symm, S.bilinear_smul_left, S.bilinear_symm v]

theorem trilinear_add_middle (u v w z : ι → ℝ) :
    S.trilinear u (v + w) z = S.trilinear u v z + S.trilinear u w z := by
  rw [S.trilinear_swap_left, S.trilinear_add_left, S.trilinear_swap_left v,
    S.trilinear_swap_left w]

theorem trilinear_add_right (u v w z : ι → ℝ) :
    S.trilinear u v (w + z) = S.trilinear u v w + S.trilinear u v z := by
  rw [S.trilinear_swap_right, S.trilinear_add_middle, S.trilinear_swap_right u w,
    S.trilinear_swap_right u z]

theorem trilinear_smul_middle (r : ℝ) (u v w : ι → ℝ) :
    S.trilinear u (r • v) w = r * S.trilinear u v w := by
  rw [S.trilinear_swap_left, S.trilinear_smul_left, S.trilinear_swap_left v]

theorem trilinear_smul_right (r : ℝ) (u v w : ι → ℝ) :
    S.trilinear u v (r • w) = r * S.trilinear u v w := by
  rw [S.trilinear_swap_right, S.trilinear_smul_middle, S.trilinear_swap_right u w]

theorem a_variation (u δ : ι → ℝ) (t : ℝ) :
    S.a (u + t • δ) = S.a u + 2 * t * S.bilinear δ u + t ^ 2 * S.a δ := by
  simp only [a, S.bilinear_add_left, S.bilinear_add_right,
    S.bilinear_smul_left, S.bilinear_smul_right]
  rw [S.bilinear_symm u δ]
  ring

theorem b_variation (u δ : ι → ℝ) (t : ℝ) :
    S.b (u + t • δ) = S.b u + 3 * t * S.trilinear δ u u +
      3 * t ^ 2 * S.trilinear δ δ u + t ^ 3 * S.b δ := by
  simp only [b, S.trilinear_add_left, S.trilinear_add_middle, S.trilinear_add_right,
    S.trilinear_smul_left, S.trilinear_smul_middle, S.trilinear_smul_right]
  rw [S.trilinear_swap_left u δ u, S.trilinear_swap_right u u δ,
    S.trilinear_swap_left u δ u, S.trilinear_swap_left u δ δ,
    S.trilinear_swap_right δ u δ]
  ring

end ProbabilityTheory.Copula.RankRegion.RhoTau.SignData
