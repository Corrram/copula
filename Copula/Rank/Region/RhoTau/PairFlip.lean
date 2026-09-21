/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.PairExpansion
import Copula.Rank.Region.RhoTau.SwapWeights

open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau.SignData

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (S : SignData ι)

def flipPair (p q : ι) (hpq : p ≠ q) : SignData ι where
  edge i j := if (i = p ∧ j = q) ∨ (i = q ∧ j = p) then 1 else S.edge i j
  symmetric i j := by
    by_cases h : (i = p ∧ j = q) ∨ (i = q ∧ j = p)
    · have h' : (j = p ∧ i = q) ∨ (j = q ∧ i = p) := by tauto
      simp [h, h']
    · have h' : ¬((j = p ∧ i = q) ∨ (j = q ∧ i = p)) := by tauto
      simp [h, h', S.symmetric]
  diagonal i := by
    have h : ¬((i = p ∧ i = q) ∨ (i = q ∧ i = p)) := by
      rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
      · exact hpq h
      · exact hpq h.symm
    simp [h, S.diagonal]
  values i j := by
    split
    · exact Or.inr rfl
    · exact S.values i j

omit [Fintype ι] in
theorem flipPair_edge_away (p q : ι) (hpq : p ≠ q) (i j : ι)
    (hi : i ≠ p ∧ i ≠ q) : (S.flipPair p q hpq).edge i j = S.edge i j := by
  simp [flipPair, hi.1, hi.2]

omit [Fintype ι] in
theorem flipPair_edge_away_right (p q : ι) (hpq : p ≠ q) (i j : ι)
    (hj : j ≠ p ∧ j ≠ q) : (S.flipPair p q hpq).edge i j = S.edge i j := by
  simp [flipPair, hj.1, hj.2]

theorem flipPair_bilinear_base (p q : ι) (hpq : p ≠ q) (v : ι → ℝ)
    (hvp : v p = 0) (hvq : v q = 0) (u : ι → ℝ) :
    (S.flipPair p q hpq).bilinear u v = S.bilinear u v := by
  unfold bilinear
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hjp : j = p
  · subst j; simp [hvp]
  by_cases hjq : j = q
  · subst j; simp [hvq]
  simp only [inversion, S.flipPair_edge_away_right p q hpq i j ⟨hjp, hjq⟩]

theorem flipPair_trilinear_base (p q : ι) (hpq : p ≠ q) (v : ι → ℝ)
    (hvp : v p = 0) (hvq : v q = 0) (u : ι → ℝ) :
    (S.flipPair p q hpq).trilinear u v v = S.trilinear u v v := by
  unfold trilinear
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hjp : j = p
  · subst j; simp [hvp]
  by_cases hjq : j = q
  · subst j; simp [hvq]
  by_cases hkp : k = p
  · subst k; simp [hvp]
  by_cases hkq : k = q
  · subst k; simp [hvq]
  simp only [triple, S.flipPair_edge_away_right p q hpq i j ⟨hjp, hjq⟩,
    S.flipPair_edge_away_right p q hpq i k ⟨hkp, hkq⟩,
    S.flipPair_edge_away p q hpq j k ⟨hjp, hjq⟩]

theorem extremal_pair_equal_linear (p q : ι) (v : ι → ℝ)
    (hvp : v p = 0) (hvq : v q = 0)
    (hop : ∀ i, i ≠ p → i ≠ q → S.edge p i = -S.edge q i) :
    S.trilinear (spike p) v v = S.trilinear (spike q) v v := by
  simp only [trilinear, spike, mul_ite, mul_one, mul_zero, zero_mul, ite_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hip : i = p
  · subst i; simp [hvp]
  by_cases hiq : i = q
  · subst i; simp [hvq]
  by_cases hjp : j = p
  · subst j; simp [hvp]
  by_cases hjq : j = q
  · subst j; simp [hvq]
  simp only [triple, hop i hip hiq, hop j hjp hjq]
  ring

theorem extremal_pair_coefficients (p q : ι) (hpq : p ≠ q) (v : ι → ℝ)
    (hvp : v p = 0) (hvq : v q = 0) (hedge : S.edge p q = -1)
    (hop : ∀ i, i ≠ p → i ≠ q → S.edge p i = -S.edge q i) :
    S.pairCoefficient v p q = ∑ i, v i ∧
      (S.flipPair p q hpq).pairCoefficient v p q = 0 := by
  have h₁ (i : ι) : S.triple p q i * v i = v i := by
    by_cases hip : i = p
    · subst i; simp [hvp]
    by_cases hiq : i = q
    · subst i; simp [hvq]
    rcases S.values q i with hi | hi <;> norm_num [triple, hedge, hop i hip hiq, hi]
  have h₂ (i : ι) : (S.flipPair p q hpq).triple p q i * v i = 0 := by
    by_cases hip : i = p
    · subst i; simp [hvp]
    by_cases hiq : i = q
    · subst i; simp [hvq]
    have hf : (S.flipPair p q hpq).edge p q = 1 := by simp [flipPair]
    rw [triple, hf, S.flipPair_edge_away_right p q hpq p i ⟨hip, hiq⟩,
      S.flipPair_edge_away_right p q hpq q i ⟨hip, hiq⟩, hop i hip hiq]
    rcases S.values q i with hi | hi <;> norm_num [hi]
  constructor
  · simp only [pairCoefficient, h₁]
  · simp only [pairCoefficient, h₂, Finset.sum_const_zero]

/-- Exact restoration of a, with a strictly improved b when a third mass is present. -/
theorem extremal_pair_improvement (p q : ι) (hpq : p ≠ q) (v : ι → ℝ)
    (_hv : ∀ i, 0 ≤ v i) (hvp : v p = 0) (hvq : v q = 0)
    (hedge : S.edge p q = -1)
    (hop : ∀ i, i ≠ p → i ≠ q → S.edge p i = -S.edge q i)
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hrest : 0 < ∑ i, v i) :
    ∃ X Y : ℝ, 0 ≤ X ∧ 0 ≤ Y ∧ X + Y = x + y ∧
      (S.flipPair p q hpq).a (v + (X • spike p + Y • spike q)) =
        S.a (v + (x • spike p + y • spike q)) ∧
      (S.flipPair p q hpq).b (v + (X • spike p + Y • spike q)) <
        S.b (v + (x • spike p + y • spike q)) := by
  obtain ⟨X, Y, hX, hY, hsum, hquad⟩ := restore_pair_quadratic x y
    (2 * S.bilinear (spike p) v) (2 * S.bilinear (spike q) v) hx.le hy.le
  have hI : S.inversion p q = 0 := by simp [inversion, hedge]
  have hI' : (S.flipPair p q hpq).inversion p q = 1 := by simp [inversion, flipPair]
  obtain ⟨hc, hc'⟩ := S.extremal_pair_coefficients p q hpq v hvp hvq hedge hop
  have hlin := S.extremal_pair_equal_linear p q v hvp hvq hop
  refine ⟨X, Y, hX, hY, hsum, ?_, ?_⟩
  · rw [(S.flipPair p q hpq).a_add_pair, S.a_add_pair, hI, hI']
    simp only [a, S.flipPair_bilinear_base p q hpq v hvp hvq]
    nlinarith only [hquad]
  · rw [(S.flipPair p q hpq).b_add_pair, S.b_add_pair, hc, hc']
    simp only [b, S.flipPair_trilinear_base p q hpq v hvp hvq, hlin]
    have hp := mul_pos (mul_pos hx hy) hrest
    have he := congrArg (fun t : ℝ => t * S.trilinear (spike q) v v) hsum
    nlinarith only [hp, he]

end ProbabilityTheory.Copula.RankRegion.RhoTau.SignData
