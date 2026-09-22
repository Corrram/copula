import Copula.Rank.Region.XiRho.Support.RampIntegrals

/-! # Integration of a pair of reflected endpoint pieces and a middle piece -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

theorem integral_unit_three_pieces {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2)
    (f g h : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    (∫ v : I, if (v : ℝ) ≤ c then f v else if (v : ℝ) ≤ 1 - c then g v else h (1 - (v : ℝ))) =
      (∫ v in (0 : ℝ)..c, f v + h v) + ∫ v in c..(1 - c), g v := by
  let F (v : ℝ) := if v ≤ c then f v else if v ≤ 1 - c then g v else h (1 - v)
  have h0 : EqOn F f (Ioo 0 c) := fun v hv => by dsimp [F]; rw [ite_eq_left hv.2.le]
  have h1 : EqOn F g (Ioo c (1 - c)) := fun v hv => by
    dsimp [F]; rw [ite_eq_right (not_le.mpr hv.1), ite_eq_left hv.2.le]
  have h2 : EqOn F (fun v => h (1 - v)) (Ioo (1 - c) 1) := fun v hv => by
    dsimp [F]; rw [ite_eq_right (by linarith [hv.1] : ¬v ≤ c), ite_eq_right (not_le.mpr hv.1)]
  have h01 : c ≤ 1 - c := by linarith
  have h12 : 1 - c ≤ 1 := by linarith
  have hi0 := (hf.intervalIntegrable (μ := volume) 0 c).congr_uIoo
    (by simpa only [uIoo_of_le hc0] using h0.symm)
  have hi1 := (hg.intervalIntegrable (μ := volume) c (1 - c)).congr_uIoo
    (by simpa only [uIoo_of_le h01] using h1.symm)
  have hi2 := ((hh.comp (by fun_prop : Continuous (fun v : ℝ => 1 - v))).intervalIntegrable
    (μ := volume) (1 - c) 1).congr_uIoo
    (by simpa only [uIoo_of_le h12, Function.comp_def] using h2.symm)
  change (∫ v : I, F v) = _
  rw [Copula.integral_unitInterval F,
    ← intervalIntegral.integral_add_adjacent_intervals (hi0.trans hi1) hi2,
    ← intervalIntegral.integral_add_adjacent_intervals hi0 hi1,
    intervalIntegral.integral_congr_Ioo_of_le hc0 h0,
    intervalIntegral.integral_congr_Ioo_of_le h01 h1,
    intervalIntegral.integral_congr_Ioo_of_le h12 h2,
    intervalIntegral.integral_comp_sub_left]
  rw [show 1 - (1 - c) = c by ring, sub_self,
    intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hh.intervalIntegrable _ _)]
  ring

/-- Exact radical integral, using the substitution v=t^2/(2b), including the endpoint. -/
theorem integral_sqrt_scaled_cube {b a : ℝ} (hb : 0 < b) (ha : 0 ≤ a) :
    (∫ v in (0 : ℝ)..(a ^ 2 / (2 * b)), Real.sqrt (2 * b * v) ^ 3) = a ^ 5 / (5 * b) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => t ^ 2 / (2 * b)) (t / b) t := by
    convert! ((hasDerivAt_id t).pow 2).div_const (2 * b) using 1
    simp only [id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    field_simp
  have hs := intervalIntegral.integral_comp_mul_deriv (a := (0 : ℝ)) (b := a)
    (f := fun t : ℝ => t ^ 2 / (2 * b)) (f' := fun t => t / b)
    (g := fun v => Real.sqrt (2 * b * v) ^ 3)
    (fun t _ => hd t) (by fun_prop) (by fun_prop)
  have he : (∫ t in (0 : ℝ)..a, Real.sqrt (2 * b * (t ^ 2 / (2 * b))) ^ 3 * (t / b)) =
      ∫ t in (0 : ℝ)..a, t ^ 4 / b := by
    apply intervalIntegral.integral_congr_Ioo_of_le ha
    intro t ht
    dsimp only
    rw [show 2 * b * (t ^ 2 / (2 * b)) = t ^ 2 by field_simp, Real.sqrt_sq ht.1.le]
    ring
  change (∫ t in (0 : ℝ)..a, Real.sqrt (2 * b * (t ^ 2 / (2 * b))) ^ 3 * (t / b)) = _ at hs
  rw [he, intervalIntegral.integral_div, integral_pow] at hs
  norm_num at hs
  rw [← hs]
  ring

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
