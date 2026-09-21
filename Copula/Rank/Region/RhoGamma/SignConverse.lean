/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel

Adapted from Corrram/lean-verifications, commit
9e144da5e0d8e2b59dadf9cef090947cb2220313.
Source module: Papers.AnsariRockelSteinmassl2026RhoGamma.SignConverse
Imports and namespaces adapted to the copula package; unused helpers omitted.
-/
import Copula.Rank.Region.RhoGamma.Transport
import Copula.Rank.Region.FairSign

/-! # Lemma 3.1 converse: realization of a joint magnitude/sign law

The original probability space is arbitrary: the sign need not be a function
of the two magnitudes. A fair simultaneous sign flip makes both ranks uniform.
-/

open MeasureTheory ProbabilityTheory Set ProbabilityTheory.Copula.RankRegion
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoGamma

noncomputable def signedLift (e s : Bool) (a b : I) : Fin 2 → I :=
  ![signedRank e a, signedRank (if e then s else !s) b]

theorem measurable_signedLift {Ω : Type*} [MeasurableSpace Ω]
    {A B : Ω → I} {S : Ω → Bool} (hA : Measurable A) (hB : Measurable B)
    (hS : Measurable S) (e : Bool) :
    Measurable (fun w => signedLift e (S w) (A w) (B w)) := by
  apply Measurable.of_eval
  intro i
  fin_cases i
  · exact measurable_signedRank hA measurable_const
  · cases e
    · exact measurable_signedRank hB ((measurable_of_finite Bool.not).comp hS)
    · exact measurable_signedRank hB hS

section Construction

variable {Ω : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
  {A B : Ω → I} {S : Ω → Bool}
  (hA : Measurable A) (hB : Measurable B) (hS : Measurable S)
  (hU : μ.toMeasure.map A = volume) (hV : μ.toMeasure.map B = volume)

noncomputable def signCopula : Copula 2 where
  measure := ⟨fairMeasure μ.toMeasure
    (fun w => signedLift true (S w) (A w) (B w))
    (fun w => signedLift false (S w) (A w) (B w)),
    fairMeasure_probability _ (measurable_signedLift hA hB hS true)
      (measurable_signedLift hA hB hS false)⟩
  marginal_eq i := by
    change (fairMeasure μ.toMeasure
      (fun w => signedLift true (S w) (A w) (B w))
      (fun w => signedLift false (S w) (A w) (B w))).map (fun x => x i) = volume
    rw [fairMeasure_map _ (measurable_signedLift hA hB hS true)
      (measurable_signedLift hA hB hS false) (measurable_pi_apply i)]
    fin_cases i
    · exact fair_signed_rank_uniform μ.toMeasure (S := fun _ => true) hA measurable_const hU
    · exact fair_signed_rank_uniform μ.toMeasure hB hS hV

theorem toMeasure_signCopula :
    (signCopula μ hA hB hS hU hV).toMeasure = fairMeasure μ.toMeasure
      (fun w => signedLift true (S w) (A w) (B w))
      (fun w => signedLift false (S w) (A w) (B w)) := rfl

end Construction

theorem magnitude_signedRank (s : Bool) (a : I) : rankMagnitude (signedRank s a) = a := by
  apply Subtype.ext
  cases s <;> simp only [signedRank, Bool.false_eq_true, ite_false, ite_true,
    rankMagnitude, coe_positiveRank, coe_negativeRank]
  · rw [show 2 * ((1 - (a : ℝ)) / 2) - 1 = -(a : ℝ) by ring,
      abs_neg, abs_of_nonneg a.property.1]
  · rw [show 2 * ((1 + (a : ℝ)) / 2) - 1 = (a : ℝ) by ring,
      abs_of_nonneg a.property.1]

theorem magnitude_signedLift (e s : Bool) (a b : I) :
    (fun i => rankMagnitude (signedLift e s a b i)) = ![a, b] := by
  funext i
  fin_cases i <;> exact magnitude_signedRank _ _

theorem sign_signedLift (e s : Bool) {a b : I} (ha : 0 < (a : ℝ)) (hb : 0 < (b : ℝ)) :
    rankSign (signedLift e s a b) = if s then 1 else -1 := by
  have hp := mul_pos ha hb
  cases e <;> cases s <;>
    simp only [rankSign, signedLift, signedRank, Bool.false_eq_true, ite_false, ite_true,
      Bool.not_false, Bool.not_true, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, coe_positiveRank, coe_negativeRank]
  all_goals
    ring_nf
    simp_all

theorem measurable_rankSign : Measurable rankSign := by
  have he : rankSign = fun x : Fin 2 → I =>
      if 0 < (2 * (x 0 : ℝ) - 1) * (2 * (x 1 : ℝ) - 1) then (1 : ℝ)
      else if (2 * (x 0 : ℝ) - 1) * (2 * (x 1 : ℝ) - 1) < 0 then -1 else 0 := by
    funext x
    simp only [rankSign, sign_apply]
    split_ifs <;> rfl
  rw [he]
  exact Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) measurable_const
    (Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      measurable_const measurable_const)

noncomputable def rankTriple (x : Fin 2 → I) : (Fin 2 → I) × ℝ :=
  ((fun i => rankMagnitude (x i)), rankSign x)

theorem measurable_rankTriple : Measurable rankTriple := by
  exact (show Continuous (fun x : Fin 2 → I => fun i => rankMagnitude (x i)) by
    fun_prop).measurable.prodMk measurable_rankSign

private theorem uniform_positive_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {A : Ω → I} (hA : Measurable A) (hU : μ.map A = volume) :
    ∀ᵐ w ∂μ, 0 < (A w : ℝ) := by
  have hn := (volume : Measure I).ae_ne 0
  rw [← hU] at hn
  have ha : ∀ᵐ w ∂μ, A w ≠ 0 :=
    (ae_map_iff hA.aemeasurable (measurableSet_singleton 0).compl).mp hn
  filter_upwards [ha] with w hw
  exact lt_of_le_of_ne (A w).property.1 (Ne.symm (fun h => hw (Subtype.ext h)))

/-- Full joint-law converse, including random signs conditional on both magnitudes. -/
theorem signCopula_joint_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) {A B : Ω → I} {S : Ω → Bool}
    (hA : Measurable A) (hB : Measurable B) (hS : Measurable S)
    (hU : μ.toMeasure.map A = volume) (hV : μ.toMeasure.map B = volume) :
    (signCopula μ hA hB hS hU hV).toMeasure.map rankTriple =
      μ.toMeasure.map (fun w => (![A w, B w], if S w then (1 : ℝ) else -1)) := by
  have he (e : Bool) :
      (fun w => rankTriple (signedLift e (S w) (A w) (B w))) =ᵐ[μ.toMeasure]
        fun w => (![A w, B w], if S w then (1 : ℝ) else -1) := by
    filter_upwards [uniform_positive_ae μ.toMeasure hA hU,
      uniform_positive_ae μ.toMeasure hB hV] with w ha hb
    exact Prod.ext (magnitude_signedLift e (S w) (A w) (B w))
      (sign_signedLift e (S w) ha hb)
  rw [toMeasure_signCopula, fairMeasure_map _ (measurable_signedLift hA hB hS true)
    (measurable_signedLift hA hB hS false) measurable_rankTriple]
  unfold fairMeasure
  simp only [Function.comp_def]
  rw [Measure.map_congr (he true), Measure.map_congr (he false), ← add_smul,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

private theorem measurable_inputTriple {Ω : Type*} [MeasurableSpace Ω]
    {A B : Ω → I} {S : Ω → Bool} (hA : Measurable A) (hB : Measurable B)
    (hS : Measurable S) :
    Measurable (fun w => (![A w, B w], if S w then (1 : ℝ) else -1)) := by
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro i
    fin_cases i
    · exact hA
    · exact hB
  · exact Measurable.ite (measurableSet_eq_fun hS measurable_const)
      measurable_const measurable_const

section Recovery

variable {Ω : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
  {A B : Ω → I} {S : Ω → Bool}
  (hA : Measurable A) (hB : Measurable B) (hS : Measurable S)
  (hU : μ.toMeasure.map A = volume) (hV : μ.toMeasure.map B = volume)

theorem signCopula_magnitude_law :
    (magnitudeCopula (signCopula μ hA hB hS hU hV)).toMeasure =
      μ.toMeasure.map (fun w => ![A w, B w]) := by
  have h := congrArg (fun ν : Measure ((Fin 2 → I) × ℝ) => ν.map Prod.fst)
    (signCopula_joint_law μ hA hB hS hU hV)
  rw [Measure.map_map measurable_fst measurable_rankTriple,
    Measure.map_map measurable_fst (measurable_inputTriple hA hB hS)] at h
  exact h

theorem integral_signCopula {f : ((Fin 2 → I) × ℝ) → ℝ} (hf : Measurable f) :
    (∫ x, f (rankTriple x) ∂(signCopula μ hA hB hS hU hV).toMeasure) =
      ∫ w, f (![A w, B w], if S w then (1 : ℝ) else -1) ∂μ.toMeasure := by
  rw [← integral_map measurable_rankTriple.aemeasurable hf.aestronglyMeasurable,
    signCopula_joint_law μ hA hB hS hU hV,
    integral_map (measurable_inputTriple hA hB hS).aemeasurable hf.aestronglyMeasurable]

theorem signCopula_rho :
    (signCopula μ hA hB hS hU hV).spearmanRho =
      3 * ∫ w, (if S w then (1 : ℝ) else -1) * (A w : ℝ) * B w ∂μ.toMeasure := by
  rw [sign_magnitude_rho]
  congr 1
  exact integral_signCopula μ hA hB hS hU hV
    (f := fun p => p.2 * (p.1 0 : ℝ) * p.1 1) (by fun_prop)

theorem signCopula_gamma :
    (signCopula μ hA hB hS hU hV).giniGamma =
      2 * ∫ w, (if S w then (1 : ℝ) else -1) * min (A w : ℝ) (B w : ℝ) ∂μ.toMeasure := by
  rw [sign_magnitude_gamma]
  congr 1
  exact integral_signCopula μ hA hB hS hU hV
    (f := fun p => p.2 * min (p.1 0 : ℝ) (p.1 1 : ℝ)) (by fun_prop)

end Recovery

end ProbabilityTheory.Copula.RankRegion.RhoGamma
