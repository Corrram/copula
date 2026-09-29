/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Measures.CDFDistanceBenchmarks

/-! # The sharp population bounds for Hoeffding's D

The pointwise Bernoulli covariance bound `(C(u,v) - uv)² ≤ u(1-u) v(1-v)` gives
`0 ≤ D ≤ 1/30` for Hoeffding's `D = ∫ (C - Π)² dC`; the upper bound is attained at `M` and `W`
(`hoeffdingD_comonotonic`, `hoeffdingD_countermonotonic`), so `30 D ∈ [0,1]`.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The Bernoulli covariance bound for a copula discrepancy. -/
theorem cdfDeviation_sq_le (C : Copula 2) (x : Fin 2 → I) :
    C.cdfDeviation x ^ 2 ≤
      ((x 0 : ℝ) * (1 - (x 0 : ℝ))) * ((x 1 : ℝ) * (1 - (x 1 : ℝ))) := by
  have h0 := C.cdf_le_coord x 0
  have h1 := C.cdf_le_coord x 1
  have hn := C.cdf_nonneg x
  have hl := C.sum_sub_dim_add_one_le_cdf x
  simp only [Fin.sum_univ_two, Nat.cast_ofNat] at hl
  by_cases h : 0 ≤ C.cdfDeviation x
  · have ha : C.cdfDeviation x ≤ (x 0 : ℝ) * (1 - (x 1 : ℝ)) := by
      unfold cdfDeviation
      nlinarith
    have hb : C.cdfDeviation x ≤ (x 1 : ℝ) * (1 - (x 0 : ℝ)) := by
      unfold cdfDeviation
      nlinarith
    have hm := mul_le_mul ha hb h (mul_nonneg (x 0).property.1 (sub_nonneg.mpr (x 1).property.2))
    convert hm using 1 <;> ring
  · have ha : -C.cdfDeviation x ≤ (x 0 : ℝ) * (x 1 : ℝ) := by
      unfold cdfDeviation
      linarith
    have hb : -C.cdfDeviation x ≤ (1 - (x 0 : ℝ)) * (1 - (x 1 : ℝ)) := by
      unfold cdfDeviation
      nlinarith
    have hm := mul_le_mul ha hb (neg_nonneg.mpr (le_of_not_ge h))
      (mul_nonneg (x 0).property.1 (x 1).property.1)
    convert hm using 1 <;> ring

theorem hoeffdingD_le (C : Copula 2) : C.hoeffdingD ≤ 1 / 30 := by
  have hi := integral_mono (C.integrable_cdfDeviation_sq C.toMeasure)
    (integrable_continuous_cube C.toMeasure (show Continuous
      (fun x : Fin 2 → I => (((x 0 : ℝ) * (1 - (x 0 : ℝ))) ^ 2 +
        ((x 1 : ℝ) * (1 - (x 1 : ℝ))) ^ 2) / 2) by fun_prop))
    (fun x => show C.cdfDeviation x ^ 2 ≤
      (((x 0 : ℝ) * (1 - (x 0 : ℝ))) ^ 2 + ((x 1 : ℝ) * (1 - (x 1 : ℝ))) ^ 2) / 2 by
      nlinarith [C.cdfDeviation_sq_le x,
        sq_nonneg ((x 0 : ℝ) * (1 - (x 0 : ℝ)) - (x 1 : ℝ) * (1 - (x 1 : ℝ)))])
  rw [integral_div, integral_add (integrable_continuous_cube _ (by fun_prop))
    (integrable_continuous_cube _ (by fun_prop)),
    C.integral_eval 0 (fun u : I => ((u : ℝ) * (1 - (u : ℝ))) ^ 2) (by fun_prop),
    C.integral_eval 1 (fun u : I => ((u : ℝ) * (1 - (u : ℝ))) ^ 2) (by fun_prop)] at hi
  simp only [mul_pow, integral_unit_sq_mul_one_sub_sq] at hi
  exact hi.trans (by norm_num)

theorem hoeffdingD_mem_Icc (C : Copula 2) : C.hoeffdingD ∈ Set.Icc 0 (1 / 30) :=
  ⟨C.hoeffdingD_nonneg, C.hoeffdingD_le⟩

theorem hoeffdingDNormalized_mem_Icc (C : Copula 2) : C.hoeffdingDNormalized ∈ Set.Icc 0 1 := by
  unfold hoeffdingDNormalized
  constructor <;> nlinarith [C.hoeffdingD_nonneg, C.hoeffdingD_le]

end ProbabilityTheory.Copula
