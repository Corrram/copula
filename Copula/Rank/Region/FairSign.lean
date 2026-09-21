/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel

Adapted from Corrram/lean-verifications, commit
9e144da5e0d8e2b59dadf9cef090947cb2220313.
Source module: Verification.FairSign
Imports and namespaces adapted to the copula package; unused helpers omitted.
-/
import Copula.OrdinalSum.Measure
import Copula.Rank.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! # Uniform ranks from a uniform magnitude and a fair sign

The sign selector may depend on the magnitude and on arbitrary other data.
Symmetrizing it with its opposite still produces the uniform rank law.
-/

open MeasureTheory ProbabilityTheory Set
open Copula.OrdinalSum
open scoped unitInterval ENNReal

namespace ProbabilityTheory.Copula.RankRegion

noncomputable def positiveRank (a : I) : I := upperEmbed Copula.unitHalf a
noncomputable def negativeRank (a : I) : I := lowerEmbed Copula.unitHalf (unitInterval.symm a)

@[fun_prop] theorem continuous_positiveRank : Continuous positiveRank := by
  unfold positiveRank
  fun_prop

@[fun_prop] theorem continuous_negativeRank : Continuous negativeRank := by
  unfold negativeRank
  fun_prop

@[fun_prop] theorem measurable_positiveRank : Measurable positiveRank := by
  unfold positiveRank
  fun_prop

@[fun_prop] theorem measurable_negativeRank : Measurable negativeRank := by
  unfold negativeRank
  fun_prop

theorem coe_positiveRank (a : I) : (positiveRank a : ℝ) = (1 + (a : ℝ)) / 2 := by
  change 1 / 2 + (1 - (1 / 2 : ℝ)) * a = _
  ring

theorem coe_negativeRank (a : I) : (negativeRank a : ℝ) = (1 - (a : ℝ)) / 2 := by
  change (1 / 2 : ℝ) * (unitInterval.symm a : ℝ) = _
  rw [unitInterval.coe_symm_eq]
  ring

noncomputable def fairMeasure {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (f g : Ω → X) : Measure X :=
  ENNReal.ofReal (1 / 2 : ℝ) • μ.map f + ENNReal.ofReal (1 / 2 : ℝ) • μ.map g

theorem fairMeasure_probability {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f g : Ω → X}
    (hf : Measurable f) (hg : Measurable g) : IsProbabilityMeasure (fairMeasure μ f g) := by
  constructor
  simp only [fairMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hf MeasurableSet.univ, Measure.map_apply hg MeasurableSet.univ,
    preimage_univ, measure_univ, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem integral_fairMeasure {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) {f g : Ω → X} {h : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) (hi : Integrable h (μ.map f)) (hj : Integrable h (μ.map g)) :
    (∫ x, h x ∂fairMeasure μ f g) =
      (1 / 2 : ℝ) * (∫ x, h (f x) ∂μ) + (1 / 2 : ℝ) * (∫ x, h (g x) ∂μ) := by
  rw [fairMeasure, integral_add_measure (hi.smul_measure (by norm_num))
    (hj.smul_measure (by norm_num)), integral_smul_measure, integral_smul_measure,
    integral_map hf.aemeasurable hh.aestronglyMeasurable,
    integral_map hg.aemeasurable hh.aestronglyMeasurable]
  norm_num

theorem fairMeasure_map {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure Ω) {f g : Ω → X} {h : X → Y}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    (fairMeasure μ f g).map h = fairMeasure μ (h ∘ f) (h ∘ g) := by
  rw [fairMeasure, Measure.map_add _ _ hh,
    Measure.map_smul _ hh.aemeasurable, Measure.map_smul _ hh.aemeasurable,
    Measure.map_map hh hf, Measure.map_map hh hg]
  rfl

theorem fair_ranks_uniform :
    fairMeasure (volume : Measure I) positiveRank negativeRank = volume := by
  let C := Copula.comonotonic 2
  have h := congrArg (fun μ : Measure (Fin 2 → I) => μ.map (fun x => x 0))
    (Copula.toMeasure_ordinalSum C C Copula.unitHalf)
  rw [Copula.map_eval, Measure.map_add _ _ (measurable_pi_apply 0),
    Measure.map_smul _ (measurable_pi_apply 0).aemeasurable,
    Measure.map_smul _ (measurable_pi_apply 0).aemeasurable,
    Measure.map_map (measurable_pi_apply 0) (by fun_prop),
    Measure.map_map (measurable_pi_apply 0) (by fun_prop)] at h
  change volume = ENNReal.ofReal (1 / 2) •
      C.toMeasure.map (lowerEmbed Copula.unitHalf ∘ (fun x => x 0)) +
    ENNReal.ofReal (1 - 1 / 2) •
      C.toMeasure.map (upperEmbed Copula.unitHalf ∘ (fun x => x 0)) at h
  rw [← Measure.map_map (measurable_lowerEmbed _) (measurable_pi_apply 0),
    ← Measure.map_map (measurable_upperEmbed _) (measurable_pi_apply 0), C.map_eval] at h
  have hn : (volume : Measure I).map negativeRank = volume.map (lowerEmbed Copula.unitHalf) := by
    change volume.map (lowerEmbed Copula.unitHalf ∘ unitInterval.symm) = _
    rw [← Measure.map_map (measurable_lowerEmbed _) unitInterval.measurable_symm,
      unitInterval.measurePreserving_symm.map_eq]
  unfold fairMeasure positiveRank
  rw [hn, add_comm]
  convert h.symm using 1
  norm_num

noncomputable def signedRank (s : Bool) (a : I) : I := if s then positiveRank a else negativeRank a

theorem measurable_signedRank {Ω : Type*} [MeasurableSpace Ω] {A : Ω → I} {S : Ω → Bool}
    (hA : Measurable A) (hS : Measurable S) : Measurable (fun w => signedRank (S w) (A w)) := by
  unfold signedRank
  exact Measurable.ite (measurableSet_eq_fun hS measurable_const)
    (measurable_positiveRank.comp hA) (measurable_negativeRank.comp hA)

theorem fair_signed_rank_uniform {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {A : Ω → I} {S : Ω → Bool}
    (hA : Measurable A) (hS : Measurable S) (hU : μ.map A = volume) :
    fairMeasure μ (fun w => signedRank (S w) (A w))
      (fun w => signedRank (!(S w)) (A w)) = volume := by
  have hN : Measurable (fun w => !(S w)) := (measurable_of_finite Bool.not).comp hS
  have hf := measurable_signedRank hA hS
  have hg := measurable_signedRank hA hN
  let := fairMeasure_probability μ hf hg
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hi : Integrable (fun w => f (signedRank (S w) (A w))) μ := by
    apply (integrable_map_measure f.continuous.aestronglyMeasurable hf.aemeasurable).mp
    exact Copula.integrable_continuous_unit _ f.continuous
  have hj : Integrable (fun w => f (signedRank (!(S w)) (A w))) μ := by
    apply (integrable_map_measure f.continuous.aestronglyMeasurable hg.aemeasurable).mp
    exact Copula.integrable_continuous_unit _ f.continuous
  rw [integral_fairMeasure μ hf hg f.continuous.measurable
    (Copula.integrable_continuous_unit _ f.continuous)
    (Copula.integrable_continuous_unit _ f.continuous), ← mul_add, ← integral_add hi hj]
  have he : (fun w => f (signedRank (S w) (A w)) + f (signedRank (!(S w)) (A w))) =
      fun w => f (positiveRank (A w)) + f (negativeRank (A w)) := by
    funext w
    cases S w <;> simp [signedRank, add_comm]
  rw [he, ← integral_map (f := fun u : I => f (positiveRank u) + f (negativeRank u))
    hA.aemeasurable (by fun_prop), hU]
  have h := congrArg (fun ν : Measure I => ∫ u, f u ∂ν) fair_ranks_uniform
  rw [integral_fairMeasure _ measurable_positiveRank measurable_negativeRank f.continuous.measurable
    (Copula.integrable_continuous_unit _ f.continuous)
    (Copula.integrable_continuous_unit _ f.continuous)] at h
  rw [integral_add]
  · linarith
  all_goals apply (integrable_map_measure f.continuous.aestronglyMeasurable
      (by fun_prop)).mp
  all_goals exact Copula.integrable_continuous_unit _ f.continuous

end ProbabilityTheory.Copula.RankRegion
