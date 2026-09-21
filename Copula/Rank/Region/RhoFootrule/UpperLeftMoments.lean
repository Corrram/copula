/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoFootrule.UpperLeftMarginal
import Copula.Rank.Region.RhoFootrule.Moments

open MeasureTheory
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoFootrule.LeftData

open UpperSpline

variable (S : LeftData)

noncomputable def distance : S.Index → ℝ → ℝ
  | .inl _, _ => S.w + (S.N + 1) * S.v
  | .inr (.inl _), s => S.w + S.N * S.v + S.v * s
  | .inr (.inr _), s => S.w + (S.N + 1) * S.v - S.v * s

theorem distance_nonneg (i : S.Index) (s : I) : 0 ≤ S.distance i s := by
  have hv := S.v_nonneg
  have hw := S.w_nonneg
  have hnv : 0 ≤ (S.N : ℝ) * S.v := mul_nonneg (Nat.cast_nonneg _) hv
  rcases i with k | k | k
  · change 0 ≤ S.w + (S.N + 1) * S.v
    positivity
  · change 0 ≤ S.w + S.N * S.v + S.v * (s : ℝ)
    exact add_nonneg (add_nonneg hw hnv) (mul_nonneg hv s.property.1)
  · change 0 ≤ S.w + (S.N + 1) * S.v - S.v * (s : ℝ)
    nlinarith only [hw, hnv, mul_le_mul_of_nonneg_left s.property.2 hv]

theorem path_delta (i : S.Index) (s : I) :
    (S.path i s 1 : ℝ) - S.path i s 0 = S.distance i s := by
  rcases i with k | k | k <;> dsimp [path, point, phase, piecePoint, distance, period] <;>
    push_cast <;> ring

theorem path_abs_distance (i : S.Index) (s : I) :
    |(S.path i s 0 : ℝ) - S.path i s 1| = S.distance i s := by
  rw [abs_sub_comm, S.path_delta, abs_of_nonneg (S.distance_nonneg i s)]

theorem symmetric_abs_distance (i : S.Index × Bool) (s : I) :
    |(S.symmetricPath i s 0 : ℝ) - S.symmetricPath i s 1| = S.distance i.1 s := by
  rcases i with ⟨i, b⟩
  cases b
  · exact S.path_abs_distance i s
  · change |(S.path i s 1 : ℝ) - S.path i s 0| = S.distance i s
    rw [S.path_delta, abs_of_nonneg (S.distance_nonneg i s)]

theorem integral_distance_cost (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x, f |(x 0 : ℝ) - x 1| ∂S.copula.toMeasure) =
      2 * ∑ i : S.Index, S.weight i * ∫ s : I, f (S.distance i s) := by
  rw [S.integral_copula (by fun_prop)]
  simp_rw [S.symmetric_abs_distance]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [Finset.sum_add_distrib]
  ring


theorem integral_distance_reversed (f : ℝ → ℝ) :
    (∫ s : I, f (S.w + (S.N + 1) * S.v - S.v * s)) =
      ∫ s : I, f (S.w + S.N * S.v + S.v * s) := by
  have h := unitInterval.measurePreserving_symm.integral_comp
    unitInterval.symmMeasurableEquiv.measurableEmbedding (fun s : I => f (S.w + S.N * S.v + S.v * s))
  convert h using 1
  congr 1
  funext s
  congr 1
  change S.w + (S.N + 1) * S.v - S.v * (s : ℝ) = S.w + S.N * S.v + S.v * (1 - (s : ℝ))
  ring

theorem integral_distance_formula (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x, f |(x 0 : ℝ) - x 1| ∂S.copula.toMeasure) =
      2 * S.N * S.w * f (S.w + (S.N + 1) * S.v) +
      2 * S.N * (S.N + 1) * S.v * (∫ s : I, f (S.w + S.N * S.v + S.v * s)) := by
  rw [S.integral_distance_cost f hf]
  simp only [Fintype.sum_sum_type, weight, distance, integral_const,
    probReal_univ, smul_eq_mul, one_mul]
  rw [S.integral_distance_reversed, ← Finset.sum_add_distrib]
  have hc (k : Fin S.N) (J : ℝ) :
      (S.N - (k : ℝ)) * S.v * J + ((k : ℝ) + 1) * S.v * J =
        (S.N + 1) * S.v * J := by ring
  simp_rw [hc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem integral_abs_distance :
    (∫ x, |(x 0 : ℝ) - x 1| ∂S.copula.toMeasure) =
      S.w + (S.N + 1) * S.v - S.N * (S.N + 1) * S.v ^ 2 := by
  have hi : (∫ s : I, S.w + S.N * S.v + S.v * (s : ℝ)) =
      S.w + S.N * S.v + S.v / 2 := by
    rw [integral_add (integrable_const _) (integrable_continuous_unit volume (by fun_prop)),
      integral_const, integral_const_mul, integral_unit_id]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    ring
  rw [S.integral_distance_formula (fun x => x) continuous_id, hi]
  nlinarith only [congrArg (fun x : ℝ => x * (S.w + (S.N + 1) * S.v)) S.normalized]

theorem integral_sq_distance :
    (∫ x, ((x 0 : ℝ) - x 1) ^ 2 ∂S.copula.toMeasure) =
      (S.w + (S.N + 1) * S.v) ^ 2 -
        2 * S.N * (S.N + 1) * (S.w + (S.N + 1) * S.v) * S.v ^ 2 +
        2 / 3 * S.N * (S.N + 1) * S.v ^ 3 := by
  have hi : (∫ s : I, (S.w + S.N * S.v + S.v * (s : ℝ)) ^ 2) =
      (S.w + S.N * S.v) ^ 2 + (S.w + S.N * S.v) * S.v + S.v ^ 2 / 3 := by
    have he : (fun s : I => (S.w + S.N * S.v + S.v * (s : ℝ)) ^ 2) =
        fun s : I => (S.w + S.N * S.v) ^ 2 +
          (2 * (S.w + S.N * S.v) * S.v) * (s : ℝ) + S.v ^ 2 * (s : ℝ) ^ 2 := by
      funext s
      ring
    rw [he, integral_add, integral_add, integral_const_mul, integral_const_mul,
      integral_const, integral_unit_id, integral_unit_pow]
    · simp only [probReal_univ, smul_eq_mul, one_mul]
      norm_num
      ring
    all_goals exact integrable_continuous_unit volume (by fun_prop)
  have h := S.integral_distance_formula (fun x => x ^ 2) (by fun_prop)
  simp only [sq_abs] at h
  rw [h, hi]
  nlinarith only [congrArg (fun x : ℝ => x * (S.w + (S.N + 1) * S.v) ^ 2) S.normalized]

theorem footrule :
    S.copula.spearmanFootrule = 1 - 3 * (S.w + (S.N + 1) * S.v - S.N * (S.N + 1) * S.v ^ 2) := by
  rw [footrule_eq_abs_moment, S.integral_abs_distance]

theorem rho :
    S.copula.spearmanRho = 1 - 6 * ((S.w + (S.N + 1) * S.v) ^ 2 -
      2 * S.N * (S.N + 1) * (S.w + (S.N + 1) * S.v) * S.v ^ 2 +
      2 / 3 * S.N * (S.N + 1) * S.v ^ 3) := by
  rw [Copula.spearmanRho_eq_one_sub, S.integral_sq_distance]

end ProbabilityTheory.Copula.RankRegion.RhoFootrule.LeftData
