import Copula.Rank.Region.XiBlest.Paper.Blest
import Copula.Rank.Region.XiBlest.Support.XiReflection

/-! # Benchmarks, range, and response-reflection symmetry of Blest's nu -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest

private theorem weighted_cdf_integrable_prod (C : Copula 2) :
    Integrable (fun p : I × I => (1 - (p.1 : ℝ)) * C.cdf ![p.1, p.2])
      ((volume : Measure I).prod volume) :=
  (show Continuous (fun p : I × I => (1 - (p.1 : ℝ)) * C.cdf ![p.1, p.2]) by
    fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem blest_integral_formula_swapped (C : Copula 2) :
    blestNu C = 24 * (∫ u : I, (1 - (u : ℝ)) * (∫ v : I, C.cdf ![u, v])) - 2 := by
  rw [blest_integral_formula, ← integral_integral_swap (weighted_cdf_integrable_prod C)]
  simp only [integral_const_mul]

private theorem integral_min_unit (u : I) :
    (∫ v : I, min (u : ℝ) v) = (u : ℝ) - (u : ℝ) ^ 2 / 2 := by
  rw [Copula.integral_unitInterval (fun v => min (u : ℝ) v)]
  have hc : Continuous (fun v : ℝ => min (u : ℝ) v) := by fun_prop
  have hL : (∫ v in (0 : ℝ)..(u : ℝ), min (u : ℝ) v) = (u : ℝ) ^ 2 / 2 := by
    calc
      _ = ∫ v in (0 : ℝ)..(u : ℝ), v := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le u.property.1] at hv
        exact min_eq_right hv.2
      _ = _ := by rw [integral_id]; ring
  have hR : (∫ v in (u : ℝ)..1, min (u : ℝ) v) = (1 - (u : ℝ)) * u := by
    calc
      _ = ∫ _ in (u : ℝ)..1, (u : ℝ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le u.property.2] at hv
        exact min_eq_left hv.1
      _ = _ := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 u) (hc.intervalIntegrable u 1), hL, hR]
  ring

theorem blest_comonotonic : blestNu (Copula.comonotonic 2) = 1 := by
  rw [blest_integral_formula_swapped]
  simp only [Copula.cdf_comonotonic_two, Matrix.cons_val_zero, Matrix.cons_val_one, integral_min_unit]
  have he : (fun u : I => (1 - (u : ℝ)) * ((u : ℝ) - (u : ℝ) ^ 2 / 2)) =
      fun u : I => (u : ℝ) - (3 / 2 : ℝ) * (u : ℝ) ^ 2 + (1 / 2 : ℝ) * (u : ℝ) ^ 3 := by
    funext u; ring
  rw [he, integral_add, integral_sub, integral_const_mul, integral_const_mul,
    Copula.integral_unit_id, Copula.integral_unit_pow, Copula.integral_unit_pow]
  · norm_num
  all_goals exact Copula.integrable_continuous_unit volume (by fun_prop)

/-- Equation (13): only the second-coordinate reflection is asserted here. -/
theorem blest_reflect_second (C : Copula 2) : blestNu (C.reflect {1}) = -blestNu C := by
  have hi (u : I) : (∫ v : I, (C.reflect {1}).cdf ![u, v]) =
      (u : ℝ) - (∫ v : I, C.cdf ![u, v]) := by
    simp only [Copula.cdf_reflect_second]
    rw [integral_sub (integrable_const _) (Copula.integrable_continuous_unit volume (by fun_prop))]
    have hs := unitInterval.measurePreserving_symm.integral_comp
      unitInterval.symmMeasurableEquiv.measurableEmbedding (fun v : I => C.cdf ![u, v])
    rw [hs]
    simp
  rw [blest_integral_formula_swapped, blest_integral_formula_swapped]
  simp_rw [hi, mul_sub]
  have hj : Integrable (fun u : I => (1 - (u : ℝ)) * (∫ v : I, C.cdf ![u, v])) := by
    have h := (weighted_cdf_integrable_prod C).integral_prod_left
    simpa only [integral_const_mul] using h
  rw [integral_sub (Copula.integrable_continuous_unit volume (by fun_prop)) hj]
  have he : (fun u : I => (1 - (u : ℝ)) * u) = fun u : I => (u : ℝ) * (1 - (u : ℝ)) := by
    funext u; ring
  rw [he, Copula.integral_unit_mul_one_sub]
  ring

theorem blest_countermonotonic : blestNu Copula.countermonotonic = -1 := by
  rw [← Copula.reflect_comonotonic_eq_countermonotonic, blest_reflect_second, blest_comonotonic]

theorem blest_mem_Icc (C : Copula 2) : blestNu C ∈ Icc (-1) 1 := by
  have hL := blest_mono Copula.countermonotonic C C.cdf_countermonotonic_le
  have hU := blest_mono C (Copula.comonotonic 2) C.cdf_le_comonotonic
  rw [blest_countermonotonic] at hL
  rw [blest_comonotonic] at hU
  exact ⟨hL, hU⟩

theorem xi_blest_reflection (C : Copula 2) :
    (C.reflect {1}).chatterjeeXi = C.chatterjeeXi ∧
      blestNu (C.reflect {1}) = -blestNu C :=
  ⟨ProbabilityTheory.Copula.RankRegion.XiBlest.Support.xi_reflect_second C, blest_reflect_second C⟩

end ProbabilityTheory.Copula.RankRegion.XiBlest
