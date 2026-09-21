/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.OrderSigns

open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

variable {ι : Type*} [Fintype ι]

noncomputable def weighted2 (u : ι → ℝ) (f : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, u i * u j * f i j

noncomputable def weighted3 (u : ι → ℝ) (f : ι → ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, u i * u j * u k * f i j k

theorem weighted3_swap_left (u : ι → ℝ) (f : ι → ι → ι → ℝ) :
    weighted3 u f = weighted3 u (fun i j k => f j i k) := by
  unfold weighted3
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem weighted3_swap_right (u : ι → ℝ) (f : ι → ι → ι → ℝ) :
    weighted3 u f = weighted3 u (fun i j k => f i k j) := by
  unfold weighted3
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weighted3_swap_outer (u : ι → ℝ) (f : ι → ι → ι → ℝ) :
    weighted3 u f = weighted3 u (fun i j k => f k j i) := by
  calc
    _ = weighted3 u (fun i j k => f j i k) := weighted3_swap_left u f
    _ = weighted3 u (fun i j k => f k i j) := weighted3_swap_right u _
    _ = _ := weighted3_swap_left u _

theorem weighted3_add (u : ι → ℝ) (f g : ι → ι → ι → ℝ) :
    weighted3 u (fun i j k => f i j k + g i j k) = weighted3 u f + weighted3 u g := by
  simp [weighted3, mul_add, Finset.sum_add_distrib]

theorem weighted3_sub (u : ι → ℝ) (f g : ι → ι → ι → ℝ) :
    weighted3 u (fun i j k => f i j k - g i j k) = weighted3 u f - weighted3 u g := by
  simp [weighted3, mul_sub, Finset.sum_sub_distrib]

theorem weighted3_neg (u : ι → ℝ) (f : ι → ι → ι → ℝ) :
    weighted3 u (fun i j k => -f i j k) = -weighted3 u f := by simp [weighted3]

theorem weighted3_pair (u : ι → ℝ) (hs : ∑ i, u i = 1) (f : ι → ι → ℝ) :
    weighted3 u (fun i j _ => f i j) = weighted2 u f := by
  have h (i j : ι) : (∑ k, u i * u j * u k * f i j) = u i * u j * f i j := by
    simp_rw [show ∀ k, u i * u j * u k * f i j = (u i * u j * f i j) * u k by intros; ring]
    rw [← Finset.mul_sum, hs, mul_one]
  simp only [weighted3, weighted2, h]

theorem weighted3_shared (u : ι → ℝ) (a b : ι → ι → ℝ) :
    weighted3 u (fun i j k => a i j * b i k) =
      ∑ i, u i * (∑ j, a i j * u j) * (∑ k, b i k * u k) := by
  simp only [weighted3, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The six mixed terms in the cycle product all reduce to the same rank moment. -/
theorem weighted_cycle_product (u : ι → ℝ) (hs : ∑ i, u i = 1)
    (a b : ι → ι → ℝ) (ha : ∀ i j, a j i = -a i j) (hb : ∀ i j, b j i = -b i j) :
    weighted3 u (fun i j k => (a i j - a i k + a j k) * (b i j - b i k + b j k)) =
      3 * weighted2 u (fun i j => a i j * b i j) -
        6 * ∑ i, u i * (∑ j, a i j * u j) * (∑ k, b i k * u k) := by
  let K := weighted3 u (fun i j k => a i j * b i k)
  let D := weighted2 u (fun i j => a i j * b i j)
  have hD₁ : weighted3 u (fun i j _ => a i j * b i j) = D := weighted3_pair u hs _
  have hD₂ : weighted3 u (fun i _ k => a i k * b i k) = D := by
    rw [weighted3_swap_right]
    exact hD₁
  have hD₃ : weighted3 u (fun _ j k => a j k * b j k) = D := by
    rw [weighted3_swap_left, weighted3_swap_right]
    exact hD₁
  have h₁ : weighted3 u (fun i j k => a i j * b j k) = -K := by
    rw [weighted3_swap_left, ← weighted3_neg]
    congr 1
    funext i j k
    rw [ha i j]
    ring
  have h₂ : weighted3 u (fun i j k => a i k * b i j) = K := by
    rw [weighted3_swap_right]
  have h₃ : weighted3 u (fun i j k => a i k * b j k) = K := by
    rw [weighted3_swap_outer]
    calc
      _ = weighted3 u (fun i j k => a i k * b i j) := by
        congr 1
        funext i j k
        rw [ha i k, hb i j]
        ring
      _ = K := h₂
  have h₄ : weighted3 u (fun i j k => a j k * b i j) = -K := by
    rw [weighted3_swap_left]
    calc
      _ = -weighted3 u (fun i j k => a i k * b i j) := by
        rw [← weighted3_neg]
        congr 1
        funext i j k
        rw [hb i j]
        ring
      _ = -K := congrArg Neg.neg h₂
  have h₅ : weighted3 u (fun i j k => a j k * b i k) = K := by
    rw [weighted3_swap_outer]
    dsimp only [K]
    congr 1
    funext i j k
    rw [ha i j, hb i k]
    ring
  have hexp (i j k : ι) : (a i j - a i k + a j k) * (b i j - b i k + b j k) =
      a i j * b i j + a i k * b i k + a j k * b j k - a i j * b i k +
        a i j * b j k - a i k * b i j - a i k * b j k + a j k * b i j - a j k * b i k := by ring
  simp_rw [hexp]
  simp only [weighted3_add, weighted3_sub, hD₁, hD₂, hD₃, h₁, h₂, h₃, h₄, h₅]
  rw [← weighted3_shared]
  dsimp only [D, K]
  ring

end ProbabilityTheory.Copula.RankRegion.RhoTau
