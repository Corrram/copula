import Copula.Rank.Region.MeanVariance.Paper.ExactRegion
import Copula.Rank.Region.MeanVariance.Paper.Touchpoints

/-! # Closed boundary formulas and sharp minimal dispersion

The arithmetic arc descriptions are converted to the square-root correction
in equation (9). The minimal variance is attained at every prescribed mean.
-/

open MeasureTheory ProbabilityTheory
open Copula.RankRegion
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.MeanVariance

private theorem radical_correction {k v : ℝ} (hk : 0 < k) (hv : 0 ≤ v) :
    4 * (k * v ^ 2) * Real.sqrt (k * v ^ 2) / Real.sqrt k = 4 * k * v ^ 3 := by
  rw [Real.sqrt_mul hk.le, Real.sqrt_sq hv]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr hk)]

/-- Equation (9), the right half of each contact interval. -/
theorem right_boundary_closed (S : RhoFootrule.RightData) :
    let k : ℝ := S.N * (S.N + 1)
    let ell : ℝ := 1 / (2 * (S.N + 1 : ℝ))
    let delta : ℝ := k * S.v ^ 2
    let m : ℝ := ell + delta
    upperRho (1 - 3 * m) =
      1 - 6 * ell * (2 * m - ell) - 4 * delta * Real.sqrt delta / Real.sqrt k := by
  have hn : (0 : ℝ) < S.N := by exact_mod_cast S.N_pos
  have hb : S.w + S.N * S.v = 1 / (2 * (S.N + 1 : ℝ)) := by
    apply (eq_div_iff (by positivity)).mpr
    nlinarith only [S.normalized]
  have h := upperRho_parameter (RhoFootrule.UpperParameter.right S)
  dsimp only [RhoFootrule.UpperParameter.footrule, RhoFootrule.UpperParameter.rho] at h
  rw [hb] at h
  dsimp only
  rw [h, radical_correction (by positivity) S.v_nonneg]
  ring

/-- Equation (9), the left half of each contact interval. -/
theorem left_boundary_closed (S : RhoFootrule.LeftData) :
    let k : ℝ := S.N * (S.N + 1)
    let ell : ℝ := 1 / (2 * (S.N : ℝ))
    let delta : ℝ := k * S.v ^ 2
    let m : ℝ := ell - delta
    upperRho (1 - 3 * m) =
      1 - 6 * ell * (2 * m - ell) - 4 * delta * Real.sqrt delta / Real.sqrt k := by
  have hn : (0 : ℝ) < S.N := by exact_mod_cast S.N_pos
  have hb : S.w + (S.N + 1) * S.v = 1 / (2 * (S.N : ℝ)) := by
    apply (eq_div_iff (by positivity)).mpr
    nlinarith only [S.normalized]
  have h := upperRho_parameter (RhoFootrule.UpperParameter.left S)
  dsimp only [RhoFootrule.UpperParameter.footrule, RhoFootrule.UpperParameter.rho] at h
  rw [hb] at h
  dsimp only
  rw [h, radical_correction (by positivity) S.v_nonneg]
  ring

/-- The variance correction as determined by the now verified sharp boundary. -/
noncomputable def minimumVariance (m : ℝ) : ℝ :=
  (1 - upperRho (1 - 3 * m)) / 6 - m ^ 2

/-- Proposition 1.6(i): the sharp improvement over the elementary second-moment bound. -/
theorem sharp_second_moment (C : Copula 2) :
    let m := ∫ x, |(x 0 : ℝ) - x 1| ∂C.toMeasure
    m ^ 2 + minimumVariance m ≤ ∫ x, ((x 0 : ℝ) - x 1) ^ 2 ∂C.toMeasure := by
  have h := sharp_upper_bound C
  rw [C.spearmanRho_eq_one_sub, ProbabilityTheory.Copula.RankRegion.MeanVariance.Support.footrule_eq_abs_moment] at h
  dsimp [minimumVariance]
  linarith only [h]

/-- Proposition 1.6(ii): the sharp variance exists and is attained for every mean in [0,1/2]. -/
theorem minimum_variance_attained {m : ℝ} (hm : m ∈ Set.Icc 0 (1 / 2)) :
    ∃ C : Copula 2,
      (∫ x, |(x 0 : ℝ) - x 1| ∂C.toMeasure) = m ∧
      (∫ x, (|(x 0 : ℝ) - x 1| - m) ^ 2 ∂C.toMeasure) = minimumVariance m := by
  obtain ⟨C, hp, hr⟩ := upper_boundary_attained
    (show 1 - 3 * m ∈ Set.Icc (-1 / 2 : ℝ) 1 by constructor <;> linarith [hm.1, hm.2])
  have hmean : (∫ x, |(x 0 : ℝ) - x 1| ∂C.toMeasure) = m := by
    rw [ProbabilityTheory.Copula.RankRegion.MeanVariance.Support.footrule_eq_abs_moment] at hp
    linarith only [hp]
  refine ⟨C, hmean, ?_⟩
  have h := quadratic_defect C
  rw [hp, hr, show (1 - (1 - 3 * m)) / 3 = m by ring] at h
  unfold minimumVariance
  nlinarith only [h]

/-- The correction is nonnegative on its full admissible domain. -/
theorem minimum_variance_nonneg {m : ℝ} (hm : m ∈ Set.Icc 0 (1 / 2)) :
    0 ≤ minimumVariance m := by
  obtain ⟨C, _, hv⟩ := minimum_variance_attained hm
  rw [← hv]
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- Exact square-root correction, right half. -/
theorem right_variance_closed (S : RhoFootrule.RightData) :
    let k : ℝ := S.N * (S.N + 1)
    let delta : ℝ := k * S.v ^ 2
    minimumVariance (1 / (2 * (S.N + 1 : ℝ)) + delta) =
      2 * delta * Real.sqrt delta / (3 * Real.sqrt k) - delta ^ 2 := by
  dsimp only
  unfold minimumVariance
  rw [right_boundary_closed]
  ring

/-- Exact square-root correction, left half. -/
theorem left_variance_closed (S : RhoFootrule.LeftData) :
    let k : ℝ := S.N * (S.N + 1)
    let delta : ℝ := k * S.v ^ 2
    minimumVariance (1 / (2 * (S.N : ℝ)) - delta) =
      2 * delta * Real.sqrt delta / (3 * Real.sqrt k) - delta ^ 2 := by
  dsimp only
  unfold minimumVariance
  rw [left_boundary_closed]
  ring

end ProbabilityTheory.Copula.RankRegion.MeanVariance
