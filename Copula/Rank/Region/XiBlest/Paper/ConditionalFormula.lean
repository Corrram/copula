import Copula.Rank.Region.XiBlest.Paper.Blest
import Copula.Rank.Region.XiBlest.Support.ClampedRhoOptimization
import Copula.Dependence.Density

/-! # Blest's coefficient as a quadratic-weighted conditional CDF integral -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
open ProbabilityTheory.Copula.RankRegion.XiBlest.Support

namespace ProbabilityTheory.Copula.RankRegion.XiBlest

private theorem integral_upper_weight (w : I) :
    (∫ u : I, if w ≤ u then 1 - (u : ℝ) else 0) = (1 - (w : ℝ)) ^ 2 / 2 := by
  have hi : Integrable (fun u : I => 1 - (u : ℝ)) :=
    Copula.integrable_continuous_unit volume (by fun_prop)
  have hl : (∫ u in Iic w, 1 - (u : ℝ)) = (w : ℝ) - (w : ℝ)^2/2 := by
    rw [Copula.integral_unit_Iic (fun u => 1-u),
      intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
        ((show Continuous (fun t : ℝ => t) from continuous_id).intervalIntegrable _ _), intervalIntegral.integral_const, integral_id]
    simp only [sub_zero, smul_eq_mul, mul_one, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have ht : (∫ u : I, 1 - (u : ℝ)) = 1/2 := by
    rw [integral_sub (integrable_const _) (Copula.integrable_continuous_unit volume (by fun_prop)),
      integral_const, Copula.integral_unit_id]
    norm_num
  have he : (∫ u : I, if w ≤ u then 1 - (u : ℝ) else 0) = ∫ u in Ici w, 1-(u : ℝ) := by
    rw [← integral_indicator measurableSet_Ici]
    rfl
  rw [he, integral_Ici_eq_integral_Ioi]
  have hh := integral_add_compl (s := Iic w) measurableSet_Iic hi
  rw [compl_Iic, hl, ht] at hh
  linarith

private theorem integrable_weighted_lower {g : I → ℝ} (hg : Measurable g)
    (hb : ∀ u, g u ∈ Icc 0 1) :
    Integrable (fun p : I × I => if p.2 ≤ p.1 then (1-(p.1 : ℝ))*g p.2 else 0)
      ((volume : Measure I).prod volume) := by
  refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact (((measurable_const.sub (measurable_subtype_coe.comp measurable_fst)).mul
      (hg.comp measurable_snd)).ite (measurableSet_le measurable_snd measurable_fst)
      measurable_const).aestronglyMeasurable
  · split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr p.1.property.2) (hb p.2).1)]
      nlinarith [p.1.property.1, p.1.property.2, (hb p.2).1, (hb p.2).2,
        mul_nonneg p.1.property.1 (hb p.2).1]
    · norm_num

theorem integral_weighted_lower {g : I → ℝ} (hg : Measurable g)
    (hb : ∀ u, g u ∈ Icc 0 1) :
    (∫ u : I, (1-(u : ℝ)) * (∫ w in Iic u, g w)) =
      (∫ w : I, (1-(w : ℝ))^2 * g w) / 2 := by
  classical
  calc
    _ = ∫ u : I, ∫ w : I, if w ≤ u then (1-(u : ℝ))*g w else 0 := by
      congr 1; funext u
      rw [← integral_const_mul, ← integral_indicator measurableSet_Iic]
      rfl
    _ = ∫ w : I, ∫ u : I, if w ≤ u then (1-(u : ℝ))*g w else 0 :=
      integral_integral_swap (integrable_weighted_lower hg hb)
    _ = ∫ w : I, ((1-(w : ℝ))^2/2)*g w := by
      congr 1; funext w
      have he : (fun u : I => if w ≤ u then (1-(u : ℝ))*g w else 0) =
          fun u : I => (if w ≤ u then 1-(u : ℝ) else 0)*g w := by
        funext u; split_ifs <;> simp
      rw [he, integral_mul_const, integral_upper_weight]
    _ = _ := by simp_rw [div_mul_eq_mul_div]; exact integral_div 2 _

theorem integrable_blest_section (C : Copula 2) (v : I) :
    Integrable (fun u : I => (1-(u : ℝ))^2 * C.conditionalCDF u v) :=
  integrable_unit_bounded (((measurable_const.sub measurable_subtype_coe).pow_const 2).mul
    (C.measurable_conditionalCDF_left v)) (fun u => ⟨mul_nonneg (sq_nonneg _)
      (C.conditionalCDF_nonneg u v),
      (mul_le_mul_of_nonneg_left (C.conditionalCDF_le_one u v) (sq_nonneg _)).trans
        (by nlinarith [u.property.1, u.property.2])⟩)

theorem blest_conditional_formula (C : Copula 2) :
    blestNu C = 12 * (∫ v : I, ∫ u : I, (1-(u : ℝ))^2 * C.conditionalCDF u v) - 2 := by
  rw [blest_integral_formula]
  have he (v : I) := integral_weighted_lower (C.measurable_conditionalCDF_left v)
    (fun u => ⟨C.conditionalCDF_nonneg u v, C.conditionalCDF_le_one u v⟩)
  simp_rw [C.cdf_eq_integral_conditionalCDF, he]
  rw [integral_div]
  ring

theorem integrable_blest_profile (C : Copula 2) :
    Integrable (fun v : I => ∫ u : I, (1-(u : ℝ))^2 * C.conditionalCDF u v) := by
  have he (v : I) : (∫ u : I, (1-(u : ℝ))^2 * C.conditionalCDF u v) =
      2 * (∫ u : I, (1-(u : ℝ))*C.cdf ![u,v]) := by
    have h := integral_weighted_lower (C.measurable_conditionalCDF_left v)
      (fun u => ⟨C.conditionalCDF_nonneg u v, C.conditionalCDF_le_one u v⟩)
    simp_rw [← C.cdf_eq_integral_conditionalCDF] at h
    linarith
  simp_rw [he]
  have hi : Integrable (fun p : I × I => (1-(p.1 : ℝ))*C.cdf ![p.1,p.2])
      ((volume : Measure I).prod volume) :=
    (show Continuous (fun p : I × I => (1-(p.1 : ℝ))*C.cdf ![p.1,p.2]) by
      fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact hi.integral_prod_right.const_mul 2

end ProbabilityTheory.Copula.RankRegion.XiBlest
