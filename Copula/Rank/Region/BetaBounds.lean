/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.FootruleGamma

/-! # Bounds at fixed Blomqvist beta

The beta–footrule inequalities of Kokol Bukovšek et al. (2021), Theorem 11,
and the beta–gamma inequalities, as collected in Proposition 2.2 of
Kokol Bukovšek–Mojškerc (2026). Boundary witnesses and the four exact-region
theorems are provided in `Copula.Rank.Region.Beta`.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Area of a symmetric tent of height at most one half. -/
theorem integral_unit_tent {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1 / 2) :
    (∫ u : I, max 0 (h - |(u : ℝ) - 1 / 2|)) = h ^ 2 := by
  let a : I := ⟨1 / 2 - h, by constructor <;> linarith⟩
  let b : I := ⟨1 / 2 + h, by constructor <;> linarith⟩
  have he : (fun u : I => max 0 (h - |(u : ℝ) - 1 / 2|)) =
      fun u : I => (|(u : ℝ) - a| + |(u : ℝ) - b|) / 2 - |(u : ℝ) - 1 / 2| := by
    funext u
    dsimp [a, b]
    simp only [abs_eq_max_neg, max_def]
    split_ifs <;> linarith
  have hh := integral_unit_abs_sub unitHalf
  norm_num [unitHalf] at hh
  rw [he, integral_sub, integral_div, integral_add,
    integral_unit_abs_sub a, integral_unit_abs_sub b, hh]
  · dsimp [a, b, unitHalf]; ring
  all_goals exact integrable_continuous_unit volume (by fun_prop)

private theorem diagonal_beta_upper (C : Copula 2) (u : I) :
    C.diagonal u ≤ (u : ℝ) -
      max 0 (1 / 2 - C.diagonal unitHalf - |(u : ℝ) - 1 / 2|) := by
  have hd := C.diagonal_le u
  rcases le_total u unitHalf with h | h
  · have hm := C.monotone_diagonal h
    have hu : (u : ℝ) ≤ 1 / 2 := h
    rw [abs_of_nonpos (by linarith)]
    rw [max_def]
    split_ifs <;> linarith
  · have hm := (C.diagonal_sub_mem_Icc h).2
    have hu : 1 / 2 ≤ (u : ℝ) := h
    change C.diagonal u - C.diagonal unitHalf ≤ 2 * ((u : ℝ) - 1 / 2) at hm
    rw [abs_of_nonneg (by linarith)]
    rw [max_def]
    split_ifs <;> linarith

private theorem diagonal_beta_lower (C : Copula 2) (u : I) :
    max 0 (2 * (u : ℝ) - 1) +
      2 * max 0 (C.diagonal unitHalf / 2 - |(u : ℝ) - 1 / 2|) ≤ C.diagonal u := by
  have hn := C.diagonal_nonneg u
  have hf := C.diagonal_lower_bound u
  rcases le_total u unitHalf with h | h
  · have hm := (C.diagonal_sub_mem_Icc h).2
    have hu : (u : ℝ) ≤ 1 / 2 := h
    change C.diagonal unitHalf - C.diagonal u ≤ 2 * (1 / 2 - (u : ℝ)) at hm
    rw [abs_of_nonpos (by linarith), max_eq_left (by linarith), max_def]
    split_ifs <;> linarith
  · have hm := C.monotone_diagonal h
    have hu : 1 / 2 ≤ (u : ℝ) := h
    rw [abs_of_nonneg (by linarith), max_eq_right (by linarith), max_def]
    have hf' : 2 * (u : ℝ) - 1 ≤ C.diagonal u := (le_max_right _ _).trans hf
    split_ifs <;> linarith

theorem spearmanFootrule_le_beta (C : Copula 2) :
    C.spearmanFootrule ≤ 1 - 3 / 8 * (1 - C.blomqvistBeta) ^ 2 := by
  have hn := C.diagonal_nonneg unitHalf
  have hb := C.diagonal_le unitHalf
  change C.diagonal unitHalf ≤ 1 / 2 at hb
  have hi := integral_mono C.integrable_diagonal_cdf
    (integrable_continuous_unit volume (by fun_prop)) (C.diagonal_beta_upper)
  rw [integral_sub (integrable_continuous_unit volume (by fun_prop))
    (integrable_continuous_unit volume (by fun_prop)), integral_unit_id,
    integral_unit_tent (by linarith) (by linarith)] at hi
  unfold spearmanFootrule blomqvistBeta
  change (∫ u : I, C.cdf ![u, u]) ≤ 1 / 2 - (1 / 2 - C.cdf ![unitHalf, unitHalf]) ^ 2 at hi
  nlinarith

theorem beta_le_spearmanFootrule (C : Copula 2) :
    3 / 16 * (1 + C.blomqvistBeta) ^ 2 - 1 / 2 ≤ C.spearmanFootrule := by
  have hn := C.diagonal_nonneg unitHalf
  have hb := C.diagonal_le unitHalf
  change C.diagonal unitHalf ≤ 1 / 2 at hb
  have hi := integral_mono (integrable_continuous_unit volume (by fun_prop))
    C.integrable_diagonal_cdf (C.diagonal_beta_lower)
  rw [integral_add (integrable_continuous_unit volume (by fun_prop))
    (integrable_continuous_unit volume (by fun_prop)), integral_unit_max_two_mul_sub_one,
    integral_const_mul, integral_unit_tent (by linarith) (by linarith)] at hi
  unfold spearmanFootrule blomqvistBeta
  change 1 / 4 + 2 * (C.cdf ![unitHalf, unitHalf] / 2) ^ 2 ≤ (∫ u : I, C.cdf ![u, u]) at hi
  nlinarith

theorem giniGamma_le_beta (C : Copula 2) :
    C.giniGamma ≤ 1 - 3 / 8 * (1 - C.blomqvistBeta) ^ 2 := by
  have h1 := C.spearmanFootrule_le_beta
  have h2 := (C.reflect {1}).beta_le_spearmanFootrule
  rw [blomqvistBeta_reflect_second] at h2
  rw [giniGamma_eq_footrule_sub_reflect]
  nlinarith

theorem beta_le_giniGamma (C : Copula 2) :
    3 / 8 * (1 + C.blomqvistBeta) ^ 2 - 1 ≤ C.giniGamma := by
  have h := (C.reflect {1}).giniGamma_le_beta
  rw [giniGamma_reflect_second, blomqvistBeta_reflect_second] at h
  nlinarith

theorem beta_le_kendallTau (C : Copula 2) :
    1 / 4 * (1 + C.blomqvistBeta) ^ 2 - 1 ≤ C.kendallTau := by
  linarith [C.beta_le_spearmanFootrule, C.footrule_le_kendallTau]

theorem kendallTau_le_beta (C : Copula 2) :
    C.kendallTau ≤ 1 - 1 / 4 * (1 - C.blomqvistBeta) ^ 2 := by
  have h := (C.reflect {1}).beta_le_kendallTau
  rw [kendallTau_reflect_second, blomqvistBeta_reflect_second] at h
  nlinarith

end ProbabilityTheory.Copula
