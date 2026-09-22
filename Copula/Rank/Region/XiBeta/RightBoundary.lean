import Copula.Rank.Region.XiBeta.LeftBoundary
import Copula.OrdinalSum.Measure

/-! # Attaining xi=1 at every beta

We use a two-block decreasing shuffle, `W ⊕ W`, as an alternative witness
to the increasing shuffle in Proposition 6. No subclass properties of
the source's particular witness are inferred from this construction.
-/

open MeasureTheory ProbabilityTheory Set
open Copula.OrdinalSum
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBeta

noncomputable def twoBlockFlip (a u : I) : I :=
  if u ≤ a then lowerEmbed a (unitInterval.symm (lowerCoord a u))
  else upperEmbed a (unitInterval.symm (upperCoord a u))

theorem measurable_twoBlockFlip (a : I) : Measurable (twoBlockFlip a) := by
  classical
  exact Measurable.piecewise measurableSet_Iic
    ((continuous_lowerEmbed a).comp (unitInterval.continuous_symm.comp
      (continuous_lowerCoord a))).measurable
    ((continuous_upperEmbed a).comp (unitInterval.continuous_symm.comp
      (continuous_upperCoord a))).measurable

theorem xi_twoBlockFlip (a : I) :
    (Copula.countermonotonic.ordinalSum Copula.countermonotonic a).chatterjeeXi = 1 := by
  by_cases h0 : a = 0
  · simp [h0]
  by_cases h1 : a = 1
  · simp [h1]
  have ha0 : 0 < a := lt_of_le_of_ne a.property.1 (Ne.symm h0)
  have ha1 : a < 1 := lt_of_le_of_ne a.property.2 h1
  apply Copula.chatterjeeXi_eq_one_of_function _ (measurable_twoBlockFlip a)
  rw [Copula.toMeasure_ordinalSum, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (show Measurable _ from by fun_prop).aemeasurable
      (measurableSet_eq_fun (by fun_prop) ((measurable_twoBlockFlip a).comp (by fun_prop)))).2
    rw [Copula.toMeasure_countermonotonic]
    apply (ae_map_iff (by fun_prop)
      (measurableSet_eq_fun ((measurable_lowerEmbed a).comp (measurable_pi_apply 1))
        ((measurable_twoBlockFlip a).comp ((measurable_lowerEmbed a).comp (measurable_pi_apply 0))))).2
    apply Filter.Eventually.of_forall
    intro t
    change lowerEmbed a (unitInterval.symm t) = twoBlockFlip a (lowerEmbed a t)
    rw [twoBlockFlip, ite_eq_left (lowerEmbed_le a t), lowerCoord_lowerEmbed a t ha0]
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (show Measurable _ from by fun_prop).aemeasurable
      (measurableSet_eq_fun (by fun_prop) ((measurable_twoBlockFlip a).comp (by fun_prop)))).2
    rw [Copula.toMeasure_countermonotonic]
    apply (ae_map_iff (by fun_prop)
      (measurableSet_eq_fun ((measurable_upperEmbed a).comp (measurable_pi_apply 1))
        ((measurable_twoBlockFlip a).comp ((measurable_upperEmbed a).comp (measurable_pi_apply 0))))).2
    have hz : ∀ᵐ t : I, t ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [hz] with t ht
    have ht0 : (0 : ℝ) < t := lt_of_le_of_ne t.property.1
      (fun he => ht (Subtype.ext he.symm))
    have hu : ¬upperEmbed a t ≤ a := by
      change ¬((a : ℝ) + (1 - (a : ℝ)) * t ≤ a)
      have hp : (0 : ℝ) < 1 - a := sub_pos.mpr ha1
      nlinarith [mul_pos hp ht0]
    change upperEmbed a (unitInterval.symm t) = twoBlockFlip a (upperEmbed a t)
    rw [twoBlockFlip, ite_eq_right hu, upperCoord_upperEmbed a t ha1]

noncomputable def rightSplit (b : ℝ) (hb : b ∈ Icc (-1) 1) : I :=
  ⟨(b + 1) / 4, by constructor <;> linarith [hb.1, hb.2]⟩

noncomputable def rightBoundary (b : ℝ) (hb : b ∈ Icc (-1) 1) : Copula 2 :=
  Copula.countermonotonic.ordinalSum Copula.countermonotonic (rightSplit b hb)

theorem rightBoundary_beta (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (rightBoundary b hb).blomqvistBeta = b := by
  let a := rightSplit b hb
  have ha : (a : ℝ) ≤ 1 / 2 := by dsimp [a, rightSplit]; linarith [hb.2]
  have ha1 : a < 1 := by change (a : ℝ) < 1; linarith
  have hh : a ≤ Copula.unitHalf := ha
  rw [Copula.blomqvistBeta]
  change 4 * (Copula.countermonotonic.ordinalSum Copula.countermonotonic a).cdf
    ![Copula.unitHalf, Copula.unitHalf] - 1 = b
  rw [Copula.cdf_ordinalSum_upper _ _ a _ _ hh hh, Copula.cdf_countermonotonic]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [coe_upperCoord_of_ge a Copula.unitHalf ha1 hh]
  have hu : ((Copula.unitHalf : ℝ) - a) / (1 - (a : ℝ)) +
      ((Copula.unitHalf : ℝ) - a) / (1 - (a : ℝ)) - 1 ≤ 0 := by
    have hp : (0 : ℝ) < 1 - a := sub_pos.mpr ha1
    change (1 / 2 - (a : ℝ)) / (1 - (a : ℝ)) +
      (1 / 2 - (a : ℝ)) / (1 - (a : ℝ)) - 1 ≤ 0
    rw [← add_div]
    exact sub_nonpos.mpr ((div_le_one hp).mpr (by linarith [a.property.1]))
  rw [max_eq_left hu]
  dsimp [a, rightSplit]
  ring

theorem rightBoundary_xi (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (rightBoundary b hb).chatterjeeXi = 1 := xi_twoBlockFlip _

theorem right_boundary_attained (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    ∃ C : Copula 2, C.blomqvistBeta = b ∧ C.chatterjeeXi = 1 :=
  ⟨rightBoundary b hb, rightBoundary_beta b hb, rightBoundary_xi b hb⟩

end ProbabilityTheory.Copula.RankRegion.XiBeta
