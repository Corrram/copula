import Copula.OrdinalSum.Measure
import Copula.Order.Survival
import Copula.Rank.ChatterjeeExamples

/-! # Measurable functional dependence survives ordinal sums -/

open MeasureTheory ProbabilityTheory
open Copula.OrdinalSum
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.MeanVariance.Support

def HasFunctionalWitness (C : Copula 2) : Prop :=
  ∃ f : I → I, Measurable f ∧ ∀ᵐ x ∂C.toMeasure, x 1 = f (x 0)

theorem HasFunctionalWitness.xi_eq_one {C : Copula 2} (h : HasFunctionalWitness C) :
    C.chatterjeeXi = 1 := by
  obtain ⟨f, hf, he⟩ := h
  exact C.chatterjeeXi_eq_one_of_function hf he

theorem functional_comonotonic : HasFunctionalWitness (Copula.comonotonic 2) := by
  refine ⟨id, measurable_id, ?_⟩
  rw [Copula.toMeasure_comonotonic]
  apply (ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2
  exact Filter.Eventually.of_forall fun _ => rfl

theorem functional_countermonotonic : HasFunctionalWitness Copula.countermonotonic := by
  refine ⟨unitInterval.symm, unitInterval.continuous_symm.measurable, ?_⟩
  rw [Copula.toMeasure_countermonotonic]
  apply (ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2
  exact Filter.Eventually.of_forall fun _ => rfl

theorem HasFunctionalWitness.ordinalSum {C D : Copula 2}
    (hC : HasFunctionalWitness C) (hD : HasFunctionalWitness D) (a : I) :
    HasFunctionalWitness (C.ordinalSum D a) := by
  classical
  by_cases h0 : a = 0
  · simpa [h0] using hD
  by_cases h1 : a = 1
  · simpa [h1] using hC
  have ha0 : 0 < a := lt_of_le_of_ne a.property.1 (Ne.symm h0)
  have ha1 : a < 1 := lt_of_le_of_ne a.property.2 h1
  obtain ⟨f, hf, hCf⟩ := hC
  obtain ⟨g, hg, hDg⟩ := hD
  let F : I → I := fun u => if u ≤ a then lowerEmbed a (f (lowerCoord a u))
    else upperEmbed a (g (upperCoord a u))
  have hF : Measurable F := Measurable.piecewise measurableSet_Iic
    ((measurable_lowerEmbed a).comp (hf.comp (continuous_lowerCoord a).measurable))
    ((measurable_upperEmbed a).comp (hg.comp (continuous_upperCoord a).measurable))
  refine ⟨F, hF, ?_⟩
  rw [Copula.toMeasure_ordinalSum, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (show Measurable _ from by fun_prop).aemeasurable
      (measurableSet_eq_fun (by fun_prop) (hF.comp (measurable_pi_apply 0)))).2
    filter_upwards [hCf] with x hx
    change lowerEmbed a (x 1) = F (lowerEmbed a (x 0))
    simp only [F, ite_eq_left (lowerEmbed_le a (x 0)), lowerCoord_lowerEmbed a (x 0) ha0, hx]
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (show Measurable _ from by fun_prop).aemeasurable
      (measurableSet_eq_fun (by fun_prop) (hF.comp (measurable_pi_apply 0)))).2
    filter_upwards [hDg, D.ae_eval_ne 0 0] with x hx hzero
    have ht0 : (0 : ℝ) < x 0 := lt_of_le_of_ne (x 0).property.1
      (fun he => hzero (Subtype.ext he.symm))
    have hu : ¬upperEmbed a (x 0) ≤ a := by
      change ¬((a : ℝ) + (1 - (a : ℝ)) * x 0 ≤ a)
      have hp : (0 : ℝ) < 1 - a := sub_pos.mpr ha1
      nlinarith [mul_pos hp ht0]
    change upperEmbed a (x 1) = F (upperEmbed a (x 0))
    simp only [F, ite_eq_right hu, upperCoord_upperEmbed a (x 0) ha1, hx]

end ProbabilityTheory.Copula.RankRegion.MeanVariance.Support
