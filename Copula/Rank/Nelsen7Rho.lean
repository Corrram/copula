/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Nelsen7
import Copula.Rank.Region.XiRho.Support.StochasticRho

/-! # Spearman rho of Nelsen's seventh family

The rational CDF integral and its logarithmic evaluation cover the full closed
parameter interval, with separate finite endpoint values.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Integral of a nonnegative linear hinge on the unit interval. -/
theorem integral_unit_linear_hinge (h : ℝ) (hh : 0 ≤ h) (t : I) :
    (∫ u : I, max 0 (h * ((u : ℝ) - (t : ℝ)))) =
      h * (1 - (t : ℝ)) ^ 2 / 2 := by
  rw [ProbabilityTheory.Copula.integral_unitInterval
    (fun u : ℝ => max 0 (h * (u - (t : ℝ))))]
  have hc : Continuous (fun u : ℝ => max 0 (h * (u - (t : ℝ)))) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (a := 0) (b := (t : ℝ)))
    (hc.intervalIntegrable (a := (t : ℝ)) (b := 1))]
  have hleft : (∫ u in (0 : ℝ)..(t : ℝ), max 0 (h * (u - (t : ℝ)))) = 0 := by
    have he : (∫ u in (0 : ℝ)..(t : ℝ), max 0 (h * (u - (t : ℝ)))) =
        ∫ _ in (0 : ℝ)..(t : ℝ), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le t.property.1] at hu
      exact max_eq_left (mul_nonpos_of_nonneg_of_nonpos hh (sub_nonpos.mpr hu.2))
    rw [he, intervalIntegral.integral_const]
    simp
  have hright : (∫ u in (t : ℝ)..1, max 0 (h * (u - (t : ℝ)))) =
      h * (1 - (t : ℝ)) ^ 2 / 2 := by
    have he : (∫ u in (t : ℝ)..1, max 0 (h * (u - (t : ℝ)))) =
        ∫ u in (t : ℝ)..1, h * (u - (t : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le t.property.2] at hu
      exact max_eq_right (mul_nonneg hh (sub_nonneg.mpr hu.1))
    rw [he, intervalIntegral.integral_const_mul]
    change h * (∫ u in (t : ℝ)..1, (fun x : ℝ => x) u - (fun _ : ℝ => (t : ℝ)) u) =
      h * (1 - (t : ℝ)) ^ 2 / 2
    have hsub : (∫ u in (t : ℝ)..1, u - (t : ℝ)) =
        (∫ u in (t : ℝ)..1, u) - (∫ _ in (t : ℝ)..1, (t : ℝ)) := by
      simpa only using (intervalIntegral.integral_sub
        (f := fun u : ℝ => u) (g := fun _ : ℝ => (t : ℝ))
        (continuous_id.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _))
    rw [hsub, integral_id, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hleft, hright]
  ring



/-- Affine reciprocal integral on the unit interval. -/
theorem integral_unit_affine_reciprocal (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    (∫ v : I, 1 / (a * (v : ℝ) + 1 - a)) =
      -(Real.log (1 - a)) / a := by
  let b : ℝ := 1 - a
  have hb : 0 < b := sub_pos.mpr ha1
  have hsub := intervalIntegral.mul_integral_comp_mul_add
    (a := (0 : ℝ)) (b := (1 : ℝ)) (f := fun x : ℝ => 1 / x) a b
  have hend : a * (1 : ℝ) + b = 1 := by dsimp [b]; ring
  simp only [mul_zero, zero_add, hend] at hsub
  rw [integral_one_div_of_pos hb zero_lt_one] at hsub
  have hlog : Real.log (1 / b) = -Real.log b := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hb.ne']
    simp
  rw [hlog] at hsub
  have he : (fun v : I => 1 / (a * (v : ℝ) + 1 - a)) =
      fun v : I => 1 / (a * (v : ℝ) + b) := by
    funext v
    congr 1
    dsimp [b]
    ring
  rw [he]
  change (∫ v : I, 1 / (a * (v : ℝ) + b)) = -Real.log b / a
  rw [ProbabilityTheory.Copula.integral_unitInterval (fun v : ℝ => 1 / (a * v + b))]
  apply (eq_div_iff ha.ne').mpr
  nlinarith [hsub]

/-- The logarithmic one-variable integral in Nelsen 7's Spearman rho. -/
theorem integral_unit_nelsen7_rational (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    (∫ v : I, (v : ℝ) ^ 2 / (2 * (a * (v : ℝ) + 1 - a))) =
      (3 * a ^ 2 - 2 * a - 2 * (a - 1) ^ 2 * Real.log (1 - a)) /
        (4 * a ^ 3) := by
  have hden (v : I) : 0 < a * (v : ℝ) + 1 - a := by
    have hb : 0 < 1 - a := sub_pos.mpr ha1
    nlinarith [mul_nonneg ha.le v.property.1]
  have hreccont : Continuous (fun v : I => 1 / (a * (v : ℝ) + 1 - a)) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro v
    exact (hden v).ne'
  have hrec : Integrable (fun v : I => 1 / (a * (v : ℝ) + 1 - a)) :=
    ProbabilityTheory.Copula.integrable_continuous_unit volume hreccont
  have hlin : Integrable (fun v : I => (v : ℝ) / (2 * a)) :=
    ProbabilityTheory.Copula.integrable_continuous_unit volume (by fun_prop)
  have hconst : Integrable (fun _ : I => (1 - a) / (2 * a ^ 2)) := integrable_const _
  have he (v : I) :
      (v : ℝ) ^ 2 / (2 * (a * (v : ℝ) + 1 - a)) =
        (v : ℝ) / (2 * a) - (1 - a) / (2 * a ^ 2) +
          ((1 - a) ^ 2 / (2 * a ^ 2)) * (1 / (a * (v : ℝ) + 1 - a)) := by
    let d : ℝ := a * (v : ℝ) + 1 - a
    have hd : d ≠ 0 := (hden v).ne'
    change (v : ℝ) ^ 2 / (2 * d) =
      (v : ℝ) / (2 * a) - (1 - a) / (2 * a ^ 2) +
        ((1 - a) ^ 2 / (2 * a ^ 2)) * (1 / d)
    field_simp [ha.ne', hd]
    dsimp [d]
    ring
  simp_rw [he]
  have hsplit :
      (∫ v : I, (v : ℝ) / (2 * a) - (1 - a) / (2 * a ^ 2) +
        ((1 - a) ^ 2 / (2 * a ^ 2)) * (1 / (a * (v : ℝ) + 1 - a))) =
      (∫ v : I, (v : ℝ) / (2 * a) - (1 - a) / (2 * a ^ 2)) +
      (∫ v : I, ((1 - a) ^ 2 / (2 * a ^ 2)) *
        (1 / (a * (v : ℝ) + 1 - a))) := by
    simpa only [Pi.sub_apply] using (integral_add (hlin.sub hconst)
      (hrec.const_mul ((1 - a) ^ 2 / (2 * a ^ 2))))
  rw [hsplit]
  have hpart :
      (∫ v : I, (v : ℝ) / (2 * a) - (1 - a) / (2 * a ^ 2)) =
      (∫ v : I, (v : ℝ) / (2 * a)) -
        (∫ _ : I, (1 - a) / (2 * a ^ 2)) := by
    simpa only [Pi.sub_apply] using (integral_sub hlin hconst)
  rw [hpart]
  have hlast :
      (∫ v : I, ((1 - a) ^ 2 / (2 * a ^ 2)) *
        (1 / (a * (v : ℝ) + 1 - a))) =
      ((1 - a) ^ 2 / (2 * a ^ 2)) *
        (∫ v : I, 1 / (a * (v : ℝ) + 1 - a)) := by
    exact integral_const_mul _ _
  rw [hlast]
  have hlinval : (∫ v : I, (v : ℝ) / (2 * a)) = 1 / (4 * a) := by
    have he' : (fun v : I => (v : ℝ) / (2 * a)) =
        fun v : I => (v : ℝ) * (1 / (2 * a)) := by funext v; ring
    rw [he', integral_mul_const, ProbabilityTheory.Copula.integral_unit_id]
    ring
  rw [hlinval, integral_const,
    integral_unit_affine_reciprocal a ha ha1]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  field_simp [ha.ne']
  ring



private theorem nelsen7_height_nonneg (θ v : I) :
    0 ≤ (θ : ℝ) * v + 1 - θ := by
  nlinarith [θ.property.2, mul_nonneg θ.property.1 v.property.1]

private theorem nelsen7_height_mul_threshold (θ v : I) :
    ((θ : ℝ) * v + 1 - θ) * (nelsen7Threshold θ v : ℝ) =
      (1 - (θ : ℝ)) * (1 - (v : ℝ)) := by
  by_cases hz : (θ : ℝ) * v + 1 - θ = 0
  · have ht : (θ : ℝ) = 1 := by
      nlinarith [θ.property.2, mul_nonneg θ.property.1 v.property.1]
    rw [hz, ht]
    ring
  · dsimp [nelsen7Threshold]
    field_simp

private theorem nelsen7_height_times_remaining (θ v : I) :
    ((θ : ℝ) * v + 1 - θ) * (1 - (nelsen7Threshold θ v : ℝ)) =
      (v : ℝ) := by
  have ht := nelsen7_height_mul_threshold θ v
  nlinarith

private theorem nelsen7_cdf_hinge (θ u v : I) :
    (nelsen7 θ).cdf ![u, v] =
      max 0 (((θ : ℝ) * v + 1 - θ) * ((u : ℝ) -
        (nelsen7Threshold θ v : ℝ))) := by
  rw [cdf_nelsen7]
  congr 1
  have ht := nelsen7_height_mul_threshold θ v
  nlinarith

/-- The inner CDF integral in the paper's Spearman-rho calculation,
valid also at the countermonotonic and independence endpoints. -/
theorem nelsen7_integral_cdf_first (θ v : I) :
    (∫ u : I, (nelsen7 θ).cdf ![u, v]) =
      (v : ℝ) ^ 2 / (2 * ((θ : ℝ) * v + 1 - θ)) := by
  simp_rw [nelsen7_cdf_hinge θ]
  rw [integral_unit_linear_hinge _ (nelsen7_height_nonneg θ v)]
  let h : ℝ := (θ : ℝ) * v + 1 - θ
  let q : ℝ := 1 - (nelsen7Threshold θ v : ℝ)
  have hq : h * q = (v : ℝ) := nelsen7_height_times_remaining θ v
  change h * q ^ 2 / 2 = (v : ℝ) ^ 2 / (2 * h)
  by_cases hz : h = 0
  · have hv : (v : ℝ) = 0 := by rw [hz] at hq; simpa using hq.symm
    simp [hz, hv]
  · field_simp
    rw [← hq]
    ring

/-- Appendix A.5.1's one-variable rho integral, including both endpoints;
its logarithmic evaluation remains a separate calculus step. -/
theorem nelsen7_rho_integral (θ : I) :
    (nelsen7 θ).spearmanRho =
      12 * (∫ v : I, (v : ℝ) ^ 2 / (2 * ((θ : ℝ) * v + 1 - θ))) - 3 := by
  rw [RankRegion.XiRho.Support.spearmanRho_eq_iterated_cdf]
  simp_rw [nelsen7_integral_cdf_first θ]

/-- Appendix A.5.1's closed Spearman-rho expression at interior parameters. -/
theorem nelsen7_rho_interior (θ : I) (h0 : (0 : ℝ) < θ) (h1 : (θ : ℝ) < 1) :
    (nelsen7 θ).spearmanRho =
      12 * ((3 * (θ : ℝ) ^ 2 - 2 * θ -
        2 * ((θ : ℝ) - 1) ^ 2 * Real.log (1 - (θ : ℝ))) /
        (4 * (θ : ℝ) ^ 3)) - 3 := by
  rw [nelsen7_rho_integral,
    integral_unit_nelsen7_rational (θ : ℝ) h0 h1]

/-- Table 6's exact Nelsen 7 Spearman-rho formula on the full parameter
interval, with the two singular logarithmic endpoints stated separately. -/
theorem nelsen7_rho (θ : I) :
    (nelsen7 θ).spearmanRho =
      if θ = 0 then -1 else if θ = 1 then 0 else
        12 * ((3 * (θ : ℝ) ^ 2 - 2 * θ -
          2 * ((θ : ℝ) - 1) ^ 2 * Real.log (1 - (θ : ℝ))) /
          (4 * (θ : ℝ) ^ 3)) - 3 := by
  by_cases h0 : θ = 0
  · subst θ
    simp
  by_cases h1 : θ = 1
  · subst θ
    simp
  have hp : (0 : ℝ) < θ :=
    lt_of_le_of_ne θ.property.1 (Ne.symm (fun hz => h0 (Subtype.ext hz)))
  have hlt : (θ : ℝ) < 1 :=
    lt_of_le_of_ne θ.property.2 (fun hz => h1 (Subtype.ext hz))
  simpa [h0, h1] using nelsen7_rho_interior θ hp hlt


end ProbabilityTheory.Copula
