import Copula.Dependence.Density
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Polynomial moments of a truncated linear ramp -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

noncomputable def ramp (q u : I) : ℝ := max 0 ((q : ℝ) - u)

theorem continuous_ramp (q : I) : Continuous (ramp q) := by
  unfold ramp
  fun_prop

theorem ramp_mem (q u : I) : ramp q u ∈ Icc 0 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le zero_le_one (by linarith [q.property.2, u.property.1])

theorem integral_ramp_pow (q : I) (n : ℕ) :
    (∫ u : I, ramp q u ^ (n + 1)) = (q : ℝ) ^ (n + 2) / (n + 2) := by
  have he : (fun u : I => ramp q u ^ (n + 1)) =
      (Iic q).indicator (fun u => ((q : ℝ) - u) ^ (n + 1)) := by
    funext u
    by_cases hu : u ≤ q
    · rw [indicator_of_mem (show u ∈ Iic q from hu), ramp, max_eq_right (sub_nonneg.mpr (show (u : ℝ) ≤ q from hu))]
    · rw [indicator_of_notMem (show u ∉ Iic q from hu), ramp, max_eq_left (sub_nonpos.mpr (show (q : ℝ) ≤ u from le_of_not_ge hu))]
      simp
  rw [he, integral_indicator measurableSet_Iic, Copula.integral_unit_Iic (fun t => ((q : ℝ) - t) ^ (n + 1))]
  have hn : (n + 2 : ℝ) ≠ 0 := by positivity
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => -((q : ℝ) - t) ^ (n + 2) / (n + 2))
      (((q : ℝ) - t) ^ (n + 1)) t := by
    convert! (((((hasDerivAt_id t).const_sub (q : ℝ)).pow (n + 2)).neg).div_const
      (n + 2 : ℝ)) using 1
    simp only [id_eq, show n + 2 - 1 = n + 1 by omega, Nat.cast_add, Nat.cast_ofNat]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((show Continuous (fun t : ℝ => ((q : ℝ) - t) ^ (n + 1)) by fun_prop).intervalIntegrable _ _)]
  simp only [sub_self, sub_zero, zero_pow (by omega : n + 2 ≠ 0), neg_zero, zero_div, zero_sub]
  ring

theorem integral_ramp (q : I) : (∫ u : I, ramp q u) = (q : ℝ) ^ 2 / 2 := by
  simpa using integral_ramp_pow q 0

theorem integral_ramp_sq (q : I) : (∫ u : I, ramp q u ^ 2) = (q : ℝ) ^ 3 / 3 := by
  have h := integral_ramp_pow q 1
  norm_num at h
  exact h

theorem integral_id_mul_ramp (q : I) :
    (∫ u : I, (u : ℝ) * ramp q u) = (q : ℝ) ^ 3 / 6 := by
  have he (u : I) : (u : ℝ) * ramp q u = (q : ℝ) * ramp q u - ramp q u ^ 2 := by
    unfold ramp
    rcases le_total (u : ℝ) q with hu | hu
    · rw [max_eq_right (sub_nonneg.mpr hu)]
      ring
    · rw [max_eq_left (sub_nonpos.mpr hu)]
      ring
  simp_rw [he]
  rw [integral_sub ((Copula.integrable_continuous_unit volume (continuous_ramp q)).const_mul _)
    (show Integrable (fun u => ramp q u ^ 2) from Copula.integrable_continuous_unit volume ((continuous_ramp q).pow 2)),
    integral_const_mul, integral_ramp, integral_ramp_sq]
  ring

theorem integral_weight_mul_ramp (q : I) :
    (∫ u : I, (1 - (u : ℝ)) * ramp q u) = (q : ℝ) ^ 2 / 2 - (q : ℝ) ^ 3 / 6 := by
  simp_rw [sub_mul, one_mul]
  rw [integral_sub (Copula.integrable_continuous_unit volume (continuous_ramp q))
    (show Integrable (fun u : I => (u : ℝ) * ramp q u) from Copula.integrable_continuous_unit volume (continuous_subtype_val.mul (continuous_ramp q))),
    integral_ramp, integral_id_mul_ramp]

/-- Reflection preserves the uniform integral on the unit interval. -/
theorem integral_unit_reflection (f : I → ℝ) :
    (∫ u : I, f (unitInterval.symm u)) = ∫ u : I, f u :=
  unitInterval.measurePreserving_symm.integral_comp
    unitInterval.symmMeasurableEquiv.measurableEmbedding f

theorem integral_complement_reflected_ramp_sq (q : I) :
    (∫ u : I, (1 - ramp q (unitInterval.symm u)) ^ 2) =
      1 - (q : ℝ) ^ 2 + (q : ℝ) ^ 3 / 3 := by
  have he (u : I) : (1 - ramp q (unitInterval.symm u)) ^ 2 =
      (fun w : I => 1 - 2 * ramp q w + ramp q w ^ 2) (unitInterval.symm u) := by ring
  simp_rw [he]
  rw [integral_unit_reflection (fun w : I => 1 - 2 * ramp q w + ramp q w ^ 2)]
  have hi : Integrable (ramp q) := Copula.integrable_continuous_unit volume (continuous_ramp q)
  have hs : Integrable (fun u => ramp q u ^ 2) :=
    Copula.integrable_continuous_unit volume ((continuous_ramp q).pow 2)
  have hh : Integrable (fun u => 1 - 2 * ramp q u) :=
    (integrable_const _).sub (hi.const_mul _)
  rw [integral_add hh hs, integral_sub (integrable_const _) (hi.const_mul _),
    integral_const_mul, integral_ramp, integral_ramp_sq]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  ring

theorem integral_weight_complement_reflected_ramp (q : I) :
    (∫ u : I, (1 - (u : ℝ)) * (1 - ramp q (unitInterval.symm u))) =
      1 / 2 - (q : ℝ) ^ 3 / 6 := by
  have he (u : I) : (1 - (u : ℝ)) * (1 - ramp q (unitInterval.symm u)) =
      (fun w : I => (w : ℝ) - (w : ℝ) * ramp q w) (unitInterval.symm u) := by
    simp only [unitInterval.coe_symm_eq]
    ring
  simp_rw [he]
  rw [integral_unit_reflection (fun w : I => (w : ℝ) - (w : ℝ) * ramp q w),
    integral_sub (Copula.integrable_continuous_unit volume continuous_subtype_val)
      (show Integrable (fun u : I => (u : ℝ) * ramp q u) from
        Copula.integrable_continuous_unit volume (continuous_subtype_val.mul (continuous_ramp q))),
    Copula.integral_unit_id, integral_id_mul_ramp]

theorem integral_unit_two_halves (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ v : I, if (v : ℝ) ≤ 1 / 2 then f v else g (1 - (v : ℝ))) =
      ∫ v in (0 : ℝ)..(1 / 2), f v + g v := by
  rw [Copula.integral_unitInterval (fun v => if v ≤ 1 / 2 then f v else g (1 - v))]
  have h0 : EqOn (fun v : ℝ => if v ≤ 1 / 2 then f v else g (1 - v)) f (Ioo 0 (1 / 2)) := by
    intro v hv
    exact ite_eq_left hv.2.le
  have h1 : EqOn (fun v : ℝ => if v ≤ 1 / 2 then f v else g (1 - v))
      (fun v => g (1 - v)) (Ioo (1 / 2) 1) := by
    intro v hv
    exact ite_eq_right (not_le.mpr hv.1)
  have hi0 := (hf.intervalIntegrable (μ := volume) 0 (1 / 2)).congr_uIoo
    (by simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using h0.symm)
  have hi1 := ((hg.comp (by fun_prop : Continuous (fun v : ℝ => 1 - v))).intervalIntegrable (μ := volume)
    (1 / 2) 1).congr_uIoo
      (by simpa only [uIoo_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1), Function.comp_def] using h1.symm)
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1,
    intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2) h0,
    intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1) h1,
    intervalIntegral.integral_comp_sub_left]
  norm_num only [sub_self, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  exact (intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)).symm

theorem integral_sqrt_two_cube_half :
    (∫ v in (0 : ℝ)..(1 / 2), Real.sqrt (2 * v) ^ 3) = 1 / 5 := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
    convert! ((hasDerivAt_id t).pow 2).div_const 2 using 1
    simp only [id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have hs := intervalIntegral.integral_comp_mul_deriv (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => t ^ 2 / 2) (f' := id) (g := fun v => Real.sqrt (2 * v) ^ 3)
    (fun t _ => hd t) (by fun_prop) (by fun_prop)
  have he : (∫ t in (0 : ℝ)..1, (Real.sqrt (2 * (t ^ 2 / 2)) ^ 3) * t) =
      ∫ t in (0 : ℝ)..1, t ^ 4 := by
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro t ht
    dsimp only
    rw [show 2 * (t ^ 2 / 2) = t ^ 2 by ring, Real.sqrt_sq ht.1.le]
    ring
  change (∫ t in (0 : ℝ)..1, Real.sqrt (2 * (t ^ 2 / 2)) ^ 3 * t) = _ at hs
  rw [he] at hs
  have heval : (∫ t in (0 : ℝ)..1, t ^ 4) = 1 / 5 := by norm_num [integral_pow]
  rw [heval] at hs
  simpa only [zero_pow (by decide : 2 ≠ 0), zero_div, one_pow] using hs.symm

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
