/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel

Adapted from Corrram/lean-verifications, commit
9e144da5e0d8e2b59dadf9cef090947cb2220313.
Source module: Papers.AnsariRockelSteinmassl2026RhoGamma.SignMagnitude
Imports and namespaces adapted to the copula package; unused helpers omitted.
-/
import Copula.Rank.Region.RhoGamma.Moments
import Mathlib.Basic.Sign.Basic

/-! # Lemma 3.1: uniform magnitudes and the sign decomposition

The sign is zero on either median. Both transformed marginals are proved
uniform, and the two moment identities use the original copula measure.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoGamma

noncomputable def rankMagnitude (u : I) : I :=
  ⟨|2 * (u : ℝ) - 1|, abs_nonneg _, by
    rw [abs_le]; constructor <;> linarith [u.property.1, u.property.2]⟩

@[fun_prop] theorem continuous_rankMagnitude : Continuous rankMagnitude := by
  unfold rankMagnitude
  fun_prop

theorem rankMagnitude_uniform :
    (volume : Measure I).map rankMagnitude = volume := by
  apply Measure.ext_of_Iic
  intro v
  rw [Measure.map_apply continuous_rankMagnitude.measurable measurableSet_Iic]
  let a : I := ⟨(1 - (v : ℝ)) / 2, by constructor <;> linarith [v.property.1, v.property.2]⟩
  let b : I := ⟨(1 + (v : ℝ)) / 2, by constructor <;> linarith [v.property.1, v.property.2]⟩
  have he : rankMagnitude ⁻¹' Iic v = Icc a b := by
    ext u
    change |2 * (u : ℝ) - 1| ≤ (v : ℝ) ↔ (1 - (v : ℝ)) / 2 ≤ u ∧ (u : ℝ) ≤ (1 + v) / 2
    rw [abs_le]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [he, unitInterval.volume_Icc, unitInterval.volume_Iic]
  congr 1
  dsimp [a, b]
  ring

theorem magnitude_marginal (C : Copula 2) (i : Fin 2) :
    C.toMeasure.map (fun x => rankMagnitude (x i)) = volume := by
  change C.toMeasure.map (rankMagnitude ∘ (fun x => x i)) = volume
  rw [← Measure.map_map continuous_rankMagnitude.measurable (measurable_pi_apply i),
    C.map_eval, rankMagnitude_uniform]

noncomputable def magnitudeCopula (C : Copula 2) : Copula 2 :=
  Copula.ofMap C.measure (fun x i => rankMagnitude (x i)) (by fun_prop) (magnitude_marginal C)

noncomputable def rankSign (x : Fin 2 → I) : ℝ :=
  (SignType.sign ((2 * (x 0 : ℝ) - 1) * (2 * (x 1 : ℝ) - 1)) : ℝ)

theorem sign_product_identity (x : Fin 2 → I) :
    rankSign x * (rankMagnitude (x 0) : ℝ) * rankMagnitude (x 1) =
      (2 * (x 0 : ℝ) - 1) * (2 * (x 1 : ℝ) - 1) := by
  change (SignType.sign ((2 * (x 0 : ℝ) - 1) * (2 * (x 1 : ℝ) - 1)) : ℝ) *
    |2 * (x 0 : ℝ) - 1| * |2 * (x 1 : ℝ) - 1| = _
  rw [mul_assoc, ← abs_mul, sign_mul_abs]

private theorem sign_min_identity (x y : ℝ) :
    2 * (SignType.sign (x * y) : ℝ) * min |x| |y| = |x + y| - |x - y| := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
    rcases lt_trichotomy y 0 with hy | rfl | hy
  all_goals simp_all [sign_mul, abs_of_neg, abs_of_pos]
  all_goals
    simp only [abs_eq_max_neg, max_def, min_def]
    split_ifs <;> linarith

theorem sign_min_magnitude_identity (x : Fin 2 → I) :
    rankSign x * min (rankMagnitude (x 0) : ℝ) (rankMagnitude (x 1) : ℝ) =
      |(x 0 : ℝ) + x 1 - 1| - |(x 0 : ℝ) - x 1| := by
  have h := sign_min_identity (2 * (x 0 : ℝ) - 1) (2 * (x 1 : ℝ) - 1)
  rw [show (2 * (x 0 : ℝ) - 1) + (2 * (x 1 : ℝ) - 1) =
      2 * ((x 0 : ℝ) + x 1 - 1) by ring,
    show (2 * (x 0 : ℝ) - 1) - (2 * (x 1 : ℝ) - 1) =
      2 * ((x 0 : ℝ) - x 1) by ring, abs_mul, abs_mul] at h
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
  dsimp [rankSign, rankMagnitude]
  linarith

theorem sign_magnitude_rho (C : Copula 2) :
    C.spearmanRho = 3 * (∫ x, rankSign x * (rankMagnitude (x 0) : ℝ) *
      rankMagnitude (x 1) ∂C.toMeasure) := by
  simp_rw [sign_product_identity]
  have he : (fun x : Fin 2 → I => (2 * (x 0 : ℝ) - 1) * (2 * (x 1 : ℝ) - 1)) =
      fun x => 4 * ((x 0 : ℝ) * x 1) - 2 * (x 0 : ℝ) - 2 * (x 1 : ℝ) + 1 := by
    funext x; ring
  rw [he, integral_add, integral_sub, integral_sub, integral_const_mul, integral_const_mul, integral_const_mul,
    C.integral_coe_eval, C.integral_coe_eval]
  · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    unfold Copula.spearmanRho
    ring
  all_goals exact Copula.integrable_continuous_cube _ (by fun_prop)

theorem sign_magnitude_gamma (C : Copula 2) :
    C.giniGamma = 2 * (∫ x, rankSign x *
      min (rankMagnitude (x 0) : ℝ) (rankMagnitude (x 1) : ℝ) ∂C.toMeasure) := by
  simp_rw [sign_min_magnitude_identity]
  exact ProbabilityTheory.Copula.RankRegion.gamma_eq_abs_moments C

end ProbabilityTheory.Copula.RankRegion.RhoGamma
