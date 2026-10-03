/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.QuasiCopula.Basic
import Copula.Rank.Basic

/-!
# The lower Fréchet–Hoeffding bound in dimension `d`

The function `W_d(u) = max(0, u₁ + ⋯ + u_d - d + 1)` bounds every `d`-copula from below
(`frechet_lower_le_cdf`). This module records the standard facts about `W_d` itself
(Nelsen 2006, §2.10; Durante–Sempi 2016, §1.7):

* `lowerFrechetBound d` is a `d`-quasi-copula for every `d`
  (`isQuasiCopula_lowerFrechetBound`), and for `d = 2` it is the CDF of `W`
  (`lowerFrechetBound_two`);
* the `W_d`-volume of the cube `[1/2, 1]^d` equals `1 - d/2`
  (`rectangleIncrement_lowerFrechetBound_half`), which is negative for `d ≥ 3`; hence `W_d` is
  not `d`-increasing (`not_isClassical_lowerFrechetBound`) and no `d`-copula has CDF `W_d`
  (`cdf_ne_lowerFrechetBound`).

That `W_d` is nevertheless pointwise best possible (Nelsen 2006, §2.10) is proved in
`Copula.Multivariate.LowerBoundAttained`.
-/

open Finset
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- The lower Fréchet–Hoeffding bound `W_d(u) = max(0, ∑ uᵢ - d + 1)`. -/
noncomputable def lowerFrechetBound (d : ℕ) (u : Fin d → I) : ℝ :=
  max 0 ((∑ i, (u i : ℝ)) - d + 1)

theorem lowerFrechetBound_le_cdf (C : Copula d) (u : Fin d → I) :
    lowerFrechetBound d u ≤ C.cdf u :=
  C.frechet_lower_le_cdf u

theorem lowerFrechetBound_nonneg (u : Fin d → I) : 0 ≤ lowerFrechetBound d u :=
  le_max_left _ _

/-- In dimension two the lower bound is the CDF of the countermonotonic copula `W`. -/
theorem lowerFrechetBound_two (u : Fin 2 → I) :
    lowerFrechetBound 2 u = countermonotonic.cdf u := by
  rw [cdf_countermonotonic, lowerFrechetBound, Fin.sum_univ_two]
  congr 1
  push_cast
  ring

private theorem sum_update_one (i : Fin d) (t : I) :
    ∑ j, ((Function.update (fun _ => (1 : I)) i t j : I) : ℝ) = (d - 1 : ℝ) + t := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h : ∑ j ∈ univ.erase i, ((Function.update (fun _ => (1 : I)) i t j : I) : ℝ) =
      ∑ j ∈ univ.erase i, (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    simp
  rw [h, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp only [Function.update_self, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact i.elim0)
  rw [Nat.cast_sub hd]
  push_cast
  ring

/-- **`W_d` is a quasi-copula** in every dimension. -/
theorem isQuasiCopula_lowerFrechetBound (d : ℕ) : IsQuasiCopula (lowerFrechetBound d) where
  normalized := by simp [lowerFrechetBound]
  grounded u i hi := by
    apply le_antisymm _ (lowerFrechetBound_nonneg u)
    apply max_le le_rfl
    have hle : ∑ j, (u j : ℝ) ≤ ∑ j ∈ univ.erase i, (1 : ℝ) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hi, Set.Icc.coe_zero, zero_add]
      exact Finset.sum_le_sum fun j _ => (u j).property.2
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)] at hle
    have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact i.elim0)
    simp only [card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_sub hd] at hle
    push_cast at hle
    linarith
  marginal i t := by
    rw [lowerFrechetBound, sum_update_one]
    rw [show (d - 1 : ℝ) + t - d + 1 = t by ring]
    exact max_eq_right t.property.1
  monotone u v huv := by
    apply max_le_max le_rfl
    have : ∑ i, (u i : ℝ) ≤ ∑ i, (v i : ℝ) := Finset.sum_le_sum fun i _ => huv i
    linarith
  lipschitz u v := by
    calc
      |lowerFrechetBound d u - lowerFrechetBound d v|
          ≤ |((∑ i, (u i : ℝ)) - d + 1) - ((∑ i, (v i : ℝ)) - d + 1)| := by
        rw [lowerFrechetBound, lowerFrechetBound, max_comm 0, max_comm 0]
        exact abs_max_sub_max_le_abs _ _ _
      _ = |∑ i, ((u i : ℝ) - (v i : ℝ))| := by
        rw [Finset.sum_sub_distrib]
        congr 1
        ring
      _ ≤ _ := Finset.abs_sum_le_sum_abs _ _

private theorem lowerFrechetBound_corner (t : Finset (Fin d)) :
    lowerFrechetBound d (corner (fun _ => unitHalf) (fun _ => 1) t) =
      max 0 (1 - (t.card : ℝ) / 2) := by
  rw [lowerFrechetBound]
  congr 1
  have hs : ∑ i, ((corner (fun _ => unitHalf) (fun _ => (1 : I)) t i : I) : ℝ) =
      ∑ i, (if i ∈ t then (1 / 2 : ℝ) else 1) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ t <;> simp [corner, hi, unitHalf]
  have hs' : ∑ i, (if i ∈ t then (1 / 2 : ℝ) else 1) =
      ∑ i, ((1 : ℝ) - (if i ∈ t then (1 / 2 : ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> norm_num
  rw [hs, hs', Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, Finset.sum_const]
  simp only [card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- **The `W_d`-volume of `[1/2, 1]^d` is `1 - d/2`** (Nelsen 2006, §2.10). -/
theorem rectangleIncrement_lowerFrechetBound_half :
    rectangleIncrement (lowerFrechetBound d) (fun _ => unitHalf) (fun _ => 1) =
      1 - (d : ℝ) / 2 := by
  rw [rectangleIncrement, partialIncrement]
  simp_rw [lowerFrechetBound_corner]
  rw [Finset.sum_powerset_apply_card (fun m => (-1 : ℝ) ^ m * max 0 (1 - (m : ℝ) / 2)),
    Finset.card_univ, Fintype.card_fin]
  rcases d with _ | d
  · simp
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∑ m ∈ range d, (d + 1).choose (m + 1 + 1) •
      ((-1 : ℝ) ^ (m + 1 + 1) * max 0 (1 - ((m + 1 + 1 : ℕ) : ℝ) / 2)) = 0 := by
    apply Finset.sum_eq_zero
    intro m _
    have : max (0 : ℝ) (1 - ((m + 1 + 1 : ℕ) : ℝ) / 2) = 0 := by
      apply max_eq_left
      push_cast
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    rw [this]
    simp
  rw [hz]
  simp only [Nat.choose_one_right, Nat.choose_zero_right, nsmul_eq_mul, pow_one, pow_zero,
    Nat.cast_one, Nat.cast_add, zero_add, one_mul]
  rw [max_eq_right (by norm_num), max_eq_right (by norm_num)]
  push_cast
  ring

/-- **`W_d` is not `d`-increasing for `d ≥ 3`**: the cube `[1/2, 1]^d` has negative volume. -/
theorem rectangleIncrement_lowerFrechetBound_neg (hd : 3 ≤ d) :
    rectangleIncrement (lowerFrechetBound d) (fun _ => unitHalf) (fun _ => 1) < 0 := by
  rw [rectangleIncrement_lowerFrechetBound_half]
  have : (3 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

/-- For `d ≥ 3`, `W_d` violates the classical copula conditions. -/
theorem not_isClassical_lowerFrechetBound (hd : 3 ≤ d) :
    ¬ IsClassical (lowerFrechetBound d) := fun h =>
  (not_le.mpr (rectangleIncrement_lowerFrechetBound_neg hd))
    (h.increasing _ _ fun _ => unitInterval.le_one')

/-- **For `d ≥ 3` no `d`-copula has CDF `W_d`** (Nelsen 2006, §2.10). -/
theorem cdf_ne_lowerFrechetBound (hd : 3 ≤ d) (C : Copula d) :
    C.cdf ≠ lowerFrechetBound d :=
  cdf_ne_of_rectangleIncrement_neg (fun _ => unitInterval.le_one')
    (rectangleIncrement_lowerFrechetBound_neg hd) C

end ProbabilityTheory.Copula
