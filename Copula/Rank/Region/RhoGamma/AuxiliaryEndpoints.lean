/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoGamma.SplittingParameters
import Copula.Rank.Region.RhoFootrule.UpperRightOptimal
import Copula.Rank.Region.RhoFootrule.UpperLeftOptimal
import Copula.Rank.Region.RhoGamma.HalfShift

open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoGamma

open RhoFootrule.UpperSpline

theorem left_offset_neg {n v w : ℝ} (hn : 0 < n) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hp : 0 < period n v w) : offset n v w + v * w < 0 := by
  have he : offset n v w + v * w = -(w ^ 2 + 2 * n * w * v + n * (n + 1) * v ^ 2) / 2 := by
    unfold offset
    ring
  rw [he]
  have hcross : 0 ≤ 2 * n * w * v := by positivity
  have hlast : 0 ≤ n * (n + 1) * v ^ 2 := by positivity
  by_cases hw0 : w = 0
  · have hvp : 0 < v := by
      unfold period at hp
      rw [hw0] at hp
      by_contra h
      have : v = 0 := le_antisymm (le_of_not_gt h) hv
      simp [this] at hp
    have hs : 0 < n * (n + 1) * v ^ 2 := by positivity
    nlinarith only [hs, hcross, sq_nonneg w]
  · have hs : 0 < w ^ 2 := sq_pos_of_ne_zero hw0
    linarith

theorem right_offset_neg {n v w : ℝ} (hn : 0 < n) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hp : 0 < period n v w) : offset n v w < 0 := by
  have hh := left_offset_neg hn hv hw hp
  nlinarith only [hh, mul_nonneg hv hw]

theorem right_discriminant_bound {n v w : ℝ} (hn : 0 ≤ n) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    v ^ 2 ≤ period n v w ^ 2 + 2 * offset n v w := by
  have he : period n v w ^ 2 + 2 * offset n v w - v ^ 2 =
      3 * w ^ 2 + (6 * n + 2) * w * v + 3 * n * (n + 1) * v ^ 2 := by
    unfold period offset
    ring
  have hh : 0 ≤ 3 * w ^ 2 + (6 * n + 2) * w * v + 3 * n * (n + 1) * v ^ 2 := by positivity
  linarith

theorem left_discriminant_bound {n v w : ℝ} (hn : 0 ≤ n) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    v ^ 2 ≤ period n v w ^ 2 + 2 * (offset n v w + v * w) := by
  have hh := right_discriminant_bound hn hv hw
  nlinarith only [hh, mul_nonneg hv hw]

theorem right_dual_zero (S : RhoFootrule.RightData) : S.dual 0 = offset S.N S.v S.w := by
  have hh := S.dual_phase 0 0 0
  norm_num [RhoFootrule.RightData.phase, piecePoint, pieceValue] at hh
  exact hh

theorem left_dual_zero (S : RhoFootrule.LeftData) : S.dual 0 = offset S.N S.v S.w + S.v * S.w := by
  have hh := S.dual_phase 0 1 0
  norm_num [RhoFootrule.LeftData.phase, piecePoint, pieceValue] at hh
  exact hh

theorem right_dual_lipschitz (S : RhoFootrule.RightData) :
    LipschitzWith ⟨S.v, S.v_nonneg⟩ S.dual :=
  potential_lipschitz (by exact_mod_cast S.N_pos) S.v_nonneg S.w_nonneg S.period_pos

theorem left_dual_lipschitz (S : RhoFootrule.LeftData) :
    LipschitzWith ⟨S.v, S.v_nonneg⟩ S.dual := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := (potential_lipschitz (by exact_mod_cast S.N_pos)
    S.v_nonneg S.w_nonneg S.period_pos).dist_le_mul (x + S.w) (y + S.w)
  simpa only [RhoFootrule.LeftData.dual, Real.dist_eq, add_sub_add_right_eq_sub] using hh

theorem halfShift_endpoint_properties {s : ℝ} (hs : 1 ≤ s) :
    3 / 8 - s / 2 < 0 ∧ (s - 1) ^ 2 ≤ s ^ 2 + 2 * (3 / 8 - s / 2) := by
  constructor <;> nlinarith only [hs]

end ProbabilityTheory.Copula.RankRegion.RhoGamma
