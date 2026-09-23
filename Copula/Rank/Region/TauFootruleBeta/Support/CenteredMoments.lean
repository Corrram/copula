import Copula.Rank.Region.TauFootruleBeta.Support.CenteredOrdinal
import Copula.Rank.Region.TauFootruleBeta.Support.RankMoments
import Copula.Rank.Symmetry

/-! # Reflected centered blocks and absolute moments -/

open MeasureTheory ProbabilityTheory
open Copula.OrdinalSum
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support

theorem integral_centeredOrdinal (C : Copula 2) (α : I)
    {f : (Fin 2 → I) → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂(centeredOrdinal C α).toMeasure) =
      (centralMargin α : ℝ) * (∫ u : I, f (fun _ => lowerEmbed (centralMargin α) u)) +
      (α : ℝ) * (∫ x, f (fun i => centralEmbed α (x i)) ∂C.toMeasure) +
      (centralMargin α : ℝ) * (∫ u : I, f (fun _ =>
        upperEmbed (centralMargin α) (upperEmbed (centralSplit α) u))) := by
  rw [centeredOrdinal, Copula.integral_ordinalSum _ _ _ hf,
    Copula.integral_comonotonic _ (by fun_prop),
    Copula.integral_ordinalSum _ _ _ (by fun_prop),
    Copula.integral_comonotonic _ (by fun_prop)]
  have h₁ := central_weight α
  have h₂ : (1 - (centralMargin α : ℝ)) * (1 - (centralSplit α : ℝ)) = centralMargin α := by
    dsimp [centralMargin] at *
    linarith
  dsimp only [centralEmbed]
  linear_combination
    (∫ x, f (fun i => upperEmbed (centralMargin α) (lowerEmbed (centralSplit α) (x i)))
      ∂C.toMeasure) * h₁ +
    (∫ u : I, f (fun _ => upperEmbed (centralMargin α) (upperEmbed (centralSplit α) u))) * h₂

theorem centeredOrdinal_abs_sum (C : Copula 2) (α : I) :
    (∫ x, |(x 0 : ℝ) + x 1 - 1| ∂(centeredOrdinal C α).toMeasure) =
      (1 - (α : ℝ) ^ 2) / 2 +
        (α : ℝ) ^ 2 * (∫ x, |(x 0 : ℝ) + x 1 - 1| ∂C.toMeasure) := by
  rw [integral_centeredOrdinal _ _ (by fun_prop)]
  have hL : (fun u : I => |(lowerEmbed (centralMargin α) u : ℝ) +
      lowerEmbed (centralMargin α) u - 1|) =
      fun u : I => 1 - 2 * (centralMargin α : ℝ) * (u : ℝ) := by
    funext u
    change |(centralMargin α : ℝ) * u + (centralMargin α : ℝ) * u - 1| = _
    rw [abs_of_nonpos]
    · ring
    · have h := mul_le_mul_of_nonneg_left u.property.2 (centralMargin α).property.1
      dsimp [centralMargin] at *
      nlinarith [α.property.1]
  have hU : (fun u : I => |(upperEmbed (centralMargin α) (upperEmbed (centralSplit α) u) : ℝ) +
      upperEmbed (centralMargin α) (upperEmbed (centralSplit α) u) - 1|) =
      fun u : I => (α : ℝ) + 2 * (centralMargin α : ℝ) * (u : ℝ) := by
    have he (u : I) :
        (upperEmbed (centralMargin α) (upperEmbed (centralSplit α) u) : ℝ) =
          1 - (centralMargin α : ℝ) + (centralMargin α : ℝ) * u := by
      change (centralMargin α : ℝ) + (1 - (centralMargin α : ℝ)) *
        ((centralSplit α : ℝ) + (1 - (centralSplit α : ℝ)) * u) = _
      have hw := central_weight α
      dsimp [centralMargin] at *
      linear_combination (1 - (u : ℝ)) * hw
    funext u
    rw [he]
    have hm : 2 * (centralMargin α : ℝ) = 1 - (α : ℝ) := by dsimp [centralMargin]; ring
    rw [abs_of_nonneg]
    · linarith
    · nlinarith [α.property.1, mul_nonneg (centralMargin α).property.1 u.property.1]
  have hC : (fun x : Fin 2 → I => |(centralEmbed α (x 0) : ℝ) + centralEmbed α (x 1) - 1|) =
      fun x => (α : ℝ) * |(x 0 : ℝ) + x 1 - 1| := by
    funext x
    simp only [coe_centralEmbed]
    rw [show (1 - (α : ℝ)) / 2 + (α : ℝ) * x 0 +
      ((1 - (α : ℝ)) / 2 + (α : ℝ) * x 1) - 1 =
      (α : ℝ) * ((x 0 : ℝ) + x 1 - 1) by ring, abs_mul, abs_of_nonneg α.property.1]
  rw [hL, hC, hU, integral_sub, integral_add, integral_const_mul, integral_const_mul,
    Copula.integral_unit_id]
  · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    dsimp [centralMargin]
    ring
  all_goals exact Copula.integrable_continuous_unit volume (by fun_prop)

theorem footrule_reflect_eq_abs_sum (C : Copula 2) :
    (C.reflect {1}).spearmanFootrule =
      1 - 3 * (∫ x, |(x 0 : ℝ) + x 1 - 1| ∂C.toMeasure) := by
  rw [footrule_eq_abs_moment, Copula.integral_reflect _ _ _ (by fun_prop)]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Copula.reflectPoint, Finset.mem_singleton, show (0 : Fin 2) ≠ 1 by decide,
    ite_false, ite_true, unitInterval.coe_symm_eq]
  congr 1
  ring

theorem centeredOrdinal_reflect_footrule (C : Copula 2) (α : I) :
    ((centeredOrdinal C α).reflect {1}).spearmanFootrule =
      (α : ℝ) ^ 2 * (C.reflect {1}).spearmanFootrule - (1 - (α : ℝ) ^ 2) / 2 := by
  rw [footrule_reflect_eq_abs_sum, centeredOrdinal_abs_sum, footrule_reflect_eq_abs_sum]
  ring

end ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support
