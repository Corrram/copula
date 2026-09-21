/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.BetaBounds

/-! # The cubic Spearman rho–Blomqvist beta bounds

The classical bounds recalled by Kokol Bukovšek et al. are proved from
the package's displacement moment and median quadrant probabilities.
A tent potential certifies the lower bound on squared displacement.
Boundary attainment and the exact-region theorem are provided in
`Copula.Rank.Region.Beta`.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Exactly one coordinate lies below the median. -/
def medianCrossing : Set (Fin 2 → I) :=
  {x | (x 0 ≤ unitHalf ∧ ¬x 1 ≤ unitHalf) ∨ (x 1 ≤ unitHalf ∧ ¬x 0 ≤ unitHalf)}

theorem measurableSet_medianCrossing : MeasurableSet medianCrossing :=
  ((measurableSet_le (measurable_pi_apply 0) measurable_const).inter
    (measurableSet_le (measurable_pi_apply 1) measurable_const).compl).union
  ((measurableSet_le (measurable_pi_apply 1) measurable_const).inter
    (measurableSet_le (measurable_pi_apply 0) measurable_const).compl)

theorem integral_medianCrossing (C : Copula 2) :
    (∫ x, medianCrossing.indicator (fun _ => (1 : ℝ)) x ∂C.toMeasure) =
      (1 - C.blomqvistBeta) / 2 := by
  classical
  let s : Set (Fin 2 → I) := {x | x 0 ≤ unitHalf}
  let t : Set (Fin 2 → I) := {x | x 1 ≤ unitHalf}
  let r : Set (Fin 2 → I) := Iic ![unitHalf, unitHalf]
  have hs : MeasurableSet s := measurableSet_le (measurable_pi_apply 0) measurable_const
  have ht : MeasurableSet t := measurableSet_le (measurable_pi_apply 1) measurable_const
  have hr : MeasurableSet r := measurableSet_Iic
  have he : medianCrossing.indicator (fun _ => (1 : ℝ)) =
      fun x => s.indicator (fun _ => (1 : ℝ)) x + t.indicator (fun _ => (1 : ℝ)) x -
        2 * r.indicator (fun _ => (1 : ℝ)) x := by
    funext x
    by_cases h0 : x 0 ≤ unitHalf <;> by_cases h1 : x 1 ≤ unitHalf <;>
      simp [medianCrossing, s, t, r, Set.indicator, Pi.le_def, Fin.forall_fin_two, h0, h1]
    all_goals norm_num [not_lt_of_ge h0, not_lt_of_ge h1]
  have hsi : (∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂C.toMeasure) = C.toMeasure.real s := by
    simpa only [Set.indicator, Pi.one_apply] using integral_indicator_one (μ := C.toMeasure) hs
  have hti : (∫ x, t.indicator (fun _ => (1 : ℝ)) x ∂C.toMeasure) = C.toMeasure.real t := by
    simpa only [Set.indicator, Pi.one_apply] using integral_indicator_one (μ := C.toMeasure) ht
  have hri : (∫ x, r.indicator (fun _ => (1 : ℝ)) x ∂C.toMeasure) = C.toMeasure.real r := by
    simpa only [Set.indicator, Pi.one_apply] using integral_indicator_one (μ := C.toMeasure) hr
  rw [he, integral_sub, integral_add, integral_const_mul, hsi, hti, hri]
  · rw [C.measureReal_eval_le 0 unitHalf, C.measureReal_eval_le 1 unitHalf]
    change 1 / 2 + 1 / 2 - 2 * C.cdf ![unitHalf, unitHalf] = _
    unfold blomqvistBeta; ring
  · exact (integrable_const _).indicator hs
  · exact (integrable_const _).indicator ht
  · exact ((integrable_const _).indicator hs).add ((integrable_const _).indicator ht)
  · exact ((integrable_const _).indicator hr).const_mul 2

private theorem square_displacement_certificate {q : ℝ} (hq : 0 ≤ q) (x : Fin 2 → I) :
    -2 * q * (max 0 (q - |(x 0 : ℝ) - 1 / 2|) + max 0 (q - |(x 1 : ℝ) - 1 / 2|)) +
      3 * q ^ 2 * medianCrossing.indicator (fun _ => (1 : ℝ)) x ≤
        ((x 0 : ℝ) - x 1) ^ 2 := by
  classical
  by_cases hx : x ∈ medianCrossing
  · rw [Set.indicator_of_mem hx]
    have he : |(x 0 : ℝ) - x 1| = |(x 0 : ℝ) - 1 / 2| + |(x 1 : ℝ) - 1 / 2| := by
      rcases hx with ⟨h0, h1⟩ | ⟨h1, h0⟩
      · have h0' : (x 0 : ℝ) ≤ 1 / 2 := h0
        have h1' : 1 / 2 < (x 1 : ℝ) := lt_of_not_ge h1
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
        ring
      · have h1' : (x 1 : ℝ) ≤ 1 / 2 := h1
        have h0' : 1 / 2 < (x 0 : ℝ) := lt_of_not_ge h0
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
        ring
    have hm := mul_le_mul_of_nonneg_left
      (add_le_add (le_max_right 0 (q - |(x 0 : ℝ) - 1 / 2|))
        (le_max_right 0 (q - |(x 1 : ℝ) - 1 / 2|))) (show 0 ≤ 2 * q by positivity)
    nlinarith [sq_nonneg (|(x 0 : ℝ) - x 1| - q), sq_abs ((x 0 : ℝ) - x 1)]
  · rw [Set.indicator_of_notMem hx]
    have hm : 0 ≤ 2 * q *
        (max 0 (q - |(x 0 : ℝ) - 1 / 2|) + max 0 (q - |(x 1 : ℝ) - 1 / 2|)) := by positivity
    nlinarith [sq_nonneg ((x 0 : ℝ) - x 1)]

theorem spearmanRho_le_beta (C : Copula 2) :
    C.spearmanRho ≤ 1 - 3 / 16 * (1 - C.blomqvistBeta) ^ 3 := by
  let q := (1 - C.blomqvistBeta) / 4
  have hq0 : 0 ≤ q := by dsimp [q]; linarith [C.blomqvistBeta_mem_Icc.2]
  have hq1 : q ≤ 1 / 2 := by dsimp [q]; linarith [C.blomqvistBeta_mem_Icc.1]
  have htent : Integrable (fun x : Fin 2 → I => -2 * q *
      (max 0 (q - |(x 0 : ℝ) - 1 / 2|) + max 0 (q - |(x 1 : ℝ) - 1 / 2|))) C.toMeasure :=
    integrable_continuous_cube _ (by fun_prop)
  have hcross : Integrable (fun x : Fin 2 → I =>
      3 * q ^ 2 * medianCrossing.indicator (fun _ => (1 : ℝ)) x) C.toMeasure :=
    ((integrable_const _).indicator measurableSet_medianCrossing).const_mul _
  have hi := integral_mono (htent.add hcross)
    (integrable_continuous_cube C.toMeasure (by fun_prop)) (square_displacement_certificate hq0)
  simp only [Pi.add_apply] at hi
  rw [integral_add htent hcross, integral_const_mul, integral_const_mul,
    C.integral_medianCrossing, integral_add,
    C.integral_eval 0 (fun u : I => max 0 (q - |(u : ℝ) - 1 / 2|)) (by fun_prop),
    C.integral_eval 1 (fun u : I => max 0 (q - |(u : ℝ) - 1 / 2|)) (by fun_prop),
    integral_unit_tent hq0 hq1] at hi
  · rw [spearmanRho_eq_one_sub]
    dsimp [q] at hi
    nlinarith only [hi]
  all_goals exact integrable_continuous_cube C.toMeasure (by fun_prop)

theorem beta_le_spearmanRho (C : Copula 2) :
    3 / 16 * (1 + C.blomqvistBeta) ^ 3 - 1 ≤ C.spearmanRho := by
  have h := (C.reflect {1}).spearmanRho_le_beta
  rw [spearmanRho_reflect_second, blomqvistBeta_reflect_second] at h
  nlinarith

end ProbabilityTheory.Copula
