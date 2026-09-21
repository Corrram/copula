/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-! # The signed triple combinatorics of Schreyer–Paulin–Trutschnig

The parity representation in Lemma 4.5 makes the weighted triple
coefficients satisfy triangle inequalities whenever the indexing triple
has even inversion parity. Diagonal signs are negative, so repeated
indices contribute zero without separate restrictions in the sums.
-/

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

open scoped BigOperators

structure SignData (ι : Type*) where
  edge : ι → ι → ℝ
  symmetric : ∀ i j, edge i j = edge j i
  diagonal : ∀ i, edge i i = -1
  values : ∀ i j, edge i j = -1 ∨ edge i j = 1

namespace SignData

variable {ι : Type*} (S : SignData ι)

noncomputable def triple (i j k : ι) : ℝ := (1 + S.edge i j * S.edge i k * S.edge j k) / 2

theorem triple_values (i j k : ι) : S.triple i j k = 0 ∨ S.triple i j k = 1 := by
  rcases S.values i j with h₁ | h₁ <;>
    rcases S.values i k with h₂ | h₂ <;>
    rcases S.values j k with h₃ | h₃ <;> norm_num [triple, h₁, h₂, h₃]

theorem triple_nonneg (i j k : ι) : 0 ≤ S.triple i j k := by
  rcases S.triple_values i j k with h | h <;> simp [h]

theorem triple_swap_left (i j k : ι) : S.triple i j k = S.triple j i k := by
  dsimp [triple]
  rw [S.symmetric j i]
  ring

theorem triple_swap_right (i j k : ι) : S.triple i j k = S.triple i k j := by
  dsimp [triple]
  rw [S.symmetric k j]
  ring

@[simp] theorem triple_repeat (i j : ι) : S.triple i i j = 0 := by
  rcases S.values i j with h | h <;> norm_num [triple, S.diagonal, h]

/-- The pointwise parity identity underlying Lemma 4.5. -/
theorem triple_triangle (p q r i : ι) (h : S.triple p q r = 0) :
    S.triple p q i ≤ S.triple p r i + S.triple q r i := by
  rcases S.values p q with h₁ | h₁ <;>
    rcases S.values p r with h₂ | h₂ <;>
    rcases S.values q r with h₃ | h₃ <;>
    rcases S.values p i with h₄ | h₄ <;>
    rcases S.values q i with h₅ | h₅ <;>
    rcases S.values r i with h₆ | h₆ <;>
    simp_all [triple]

variable [Fintype ι]

noncomputable def pairCoefficient (u : ι → ℝ) (i j : ι) : ℝ := ∑ k, S.triple i j k * u k

theorem pairCoefficient_symmetric (u : ι → ℝ) (i j : ι) :
    S.pairCoefficient u i j = S.pairCoefficient u j i := by
  simp only [pairCoefficient, S.triple_swap_left i j]

theorem pairCoefficient_nonneg (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (i j : ι) :
    0 ≤ S.pairCoefficient u i j :=
  Finset.sum_nonneg fun k _ => mul_nonneg (S.triple_nonneg i j k) (hu k)

theorem pairCoefficient_triangle (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i)
    (p q r : ι) (h : S.triple p q r = 0) :
    S.pairCoefficient u p q ≤ S.pairCoefficient u p r + S.pairCoefficient u q r := by
  simp only [pairCoefficient, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [add_mul] using mul_le_mul_of_nonneg_right (S.triple_triangle p q r i h) (hu i)

end SignData

/-- The three-coordinate quadratic form from Lemma 4.6(i). -/
theorem triple_quadratic_nonpos {a b c x y z : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : a ≤ b + c) (hbc : b ≤ a + c) (hca : c ≤ a + b)
    (hxyz : x + y + z = 0) : a * x * y + b * x * z + c * y * z ≤ 0 := by
  have hz : z = -x - y := by linarith
  subst z
  by_cases hxy : 0 ≤ x * y
  · have h := mul_nonneg (sub_nonneg.mpr hab) hxy
    nlinarith [mul_nonneg hb (sq_nonneg x), mul_nonneg hc (sq_nonneg y)]
  by_cases hxz : 0 ≤ x * (-x - y)
  · have h := mul_nonneg (sub_nonneg.mpr hbc) hxz
    nlinarith [mul_nonneg ha (sq_nonneg x), mul_nonneg hc (sq_nonneg (-x - y))]
  by_cases hyz : 0 ≤ y * (-x - y)
  · have h := mul_nonneg (sub_nonneg.mpr hca) hyz
    nlinarith [mul_nonneg ha (sq_nonneg y), mul_nonneg hb (sq_nonneg (-x - y))]
  have hprod := mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hxy) (le_of_not_ge hxz)
  have hx0 : x ≠ 0 := by intro h; simp [h] at hxy
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx0
  have hneg := mul_neg_of_pos_of_neg hx2 (lt_of_not_ge hyz)
  nlinarith

/-- The four-coordinate quadratic form from Lemma 4.6(ii). -/
theorem four_quadratic_nonpos {a b d x y : ℝ}
    (ha : |d| ≤ 2 * a) (hb : |d| ≤ 2 * b) :
    -a * x ^ 2 + d * x * y - b * y ^ 2 ≤ 0 := by
  by_cases hd : 0 ≤ d
  · rw [abs_of_nonneg hd] at ha hb
    nlinarith [mul_nonneg hd (sq_nonneg (x - y)),
      mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg x),
      mul_nonneg (sub_nonneg.mpr hb) (sq_nonneg y)]
  · rw [abs_of_neg (lt_of_not_ge hd)] at ha hb
    have hd' : 0 ≤ -d := by linarith
    nlinarith [mul_nonneg hd' (sq_nonneg (x + y)),
      mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg x),
      mul_nonneg (sub_nonneg.mpr hb) (sq_nonneg y)]

end ProbabilityTheory.Copula.RankRegion.RhoTau
