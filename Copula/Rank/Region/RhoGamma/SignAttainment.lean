/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel

Adapted from Corrram/lean-verifications, commit
9e144da5e0d8e2b59dadf9cef090947cb2220313.
Source module: Papers.AnsariRockelSteinmassl2026RhoGamma.SignAttainment
Imports and namespaces adapted to the copula package; unused helpers omitted.
-/
import Copula.Rank.Region.RhoGamma.SignConverse
import Copula.Rank.Region.Optimization

/-! # Lemma 3.2: attaining the sign bound for every magnitude coupling -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoGamma

noncomputable def thresholdSign (t : ℝ) (x : Fin 2 → I) : Bool :=
  if t ≤ max (x 0 : ℝ) (x 1 : ℝ) then true else false

theorem measurable_thresholdSign (t : ℝ) : Measurable (thresholdSign t) := by
  exact Measurable.ite (measurableSet_le measurable_const (by fun_prop))
    measurable_const measurable_const

noncomputable def signOptimizer (D : Copula 2) (t : ℝ) : Copula 2 :=
  signCopula D.measure (measurable_pi_apply 0) (measurable_pi_apply 1)
    (measurable_thresholdSign t) (D.map_eval 0) (D.map_eval 1)

theorem signOptimizer_magnitude (D : Copula 2) (t : ℝ) :
    magnitudeCopula (signOptimizer D t) = D := by
  apply Copula.ext
  unfold signOptimizer
  erw [signCopula_magnitude_law]
  have he : (fun x : Fin 2 → I => ![x 0, x 1]) = id := by
    funext x i
    fin_cases i <;> rfl
  rw [he, Measure.map_id]
  rfl

theorem signOptimizer_value (D : Copula 2) (t : ℝ) :
    (signOptimizer D t).spearmanRho - 3 / 2 * t * (signOptimizer D t).giniGamma =
      3 * ∫ x, magnitudeCost t x ∂D.toMeasure := by
  rw [supporting_functional]
  congr 1
  have hi := integral_signCopula D.measure (measurable_pi_apply 0) (measurable_pi_apply 1)
    (measurable_thresholdSign t) (D.map_eval 0) (D.map_eval 1)
    (f := fun p => p.2 * min (p.1 0 : ℝ) (p.1 1 : ℝ) *
      (max (p.1 0 : ℝ) (p.1 1 : ℝ) - t)) (by fun_prop)
  change (∫ x, rankSign x * min (rankMagnitude (x 0) : ℝ) (rankMagnitude (x 1) : ℝ) *
    (max (rankMagnitude (x 0) : ℝ) (rankMagnitude (x 1) : ℝ) - t)
    ∂(signOptimizer D t).toMeasure) = _ at hi
  rw [hi]
  apply integral_congr_ae
  filter_upwards [] with x
  change (if thresholdSign t x then (1 : ℝ) else -1) * min (x 0 : ℝ) (x 1 : ℝ) *
    (max (x 0 : ℝ) (x 1 : ℝ) - t) = magnitudeCost t x
  unfold thresholdSign magnitudeCost
  by_cases h : t ≤ max (x 0 : ℝ) (x 1 : ℝ)
  · simp [h, abs_of_nonneg (sub_nonneg.mpr h)]
  · simp only [h, ite_false, Bool.false_eq_true,
      abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h))]
    ring

/-- Every uniform magnitude law has a copula that attains the pointwise sign bound. -/
theorem sign_bound_attained (D : Copula 2) (t : ℝ) :
    ∃ C : Copula 2, magnitudeCopula C = D ∧
      C.spearmanRho - 3 / 2 * t * C.giniGamma = 3 * ∫ x, magnitudeCost t x ∂D.toMeasure :=
  ⟨signOptimizer D t, signOptimizer_magnitude D t, signOptimizer_value D t⟩

/-- Equality of the upper-bound problems, without assuming existence of an optimizer. -/
theorem supporting_bound_iff_transport_bound (t v : ℝ) :
    (∀ C : Copula 2, C.spearmanRho - 3 / 2 * t * C.giniGamma ≤ 3 * v) ↔
      ∀ D : Copula 2, (∫ x, magnitudeCost t x ∂D.toMeasure) ≤ v := by
  constructor
  · intro h D
    have hc := h (signOptimizer D t)
    rw [signOptimizer_value] at hc
    linarith
  · intro h C
    exact (supporting_functional_le C t).trans (mul_le_mul_of_nonneg_left (h _) (by norm_num))

/-- An optimal magnitude coupling yields an optimal copula with the same magnitude law. -/
theorem transport_optimizer_lifts (D : Copula 2) (t : ℝ)
    (hD : ∀ E : Copula 2, (∫ x, magnitudeCost t x ∂E.toMeasure) ≤
      ∫ x, magnitudeCost t x ∂D.toMeasure) :
    ∀ C : Copula 2, C.spearmanRho - 3 / 2 * t * C.giniGamma ≤
      (signOptimizer D t).spearmanRho - 3 / 2 * t * (signOptimizer D t).giniGamma := by
  rw [signOptimizer_value]
  exact (supporting_bound_iff_transport_bound t _).mpr hD

/-- A feasible potential with contact certifies an attained supporting line. -/
theorem transport_contact_support (D : Copula 2) (t : ℝ) {f : I → ℝ}
    (hf : Continuous f)
    (hfeasible : ∀ x : Fin 2 → I, magnitudeCost t x ≤ f (x 0) + f (x 1))
    (hcontact : ∀ᵐ x ∂D.toMeasure, magnitudeCost t x = f (x 0) + f (x 1)) :
    (∀ C : Copula 2, C.spearmanRho - 3 / 2 * t * C.giniGamma ≤ 6 * ∫ u : I, f u) ∧
    ((signOptimizer D t).spearmanRho - 3 / 2 * t * (signOptimizer D t).giniGamma =
      6 * ∫ u : I, f u) := by
  have hv := transport_contact_value D t hf hcontact
  constructor
  · intro C
    have h := transport_optimizer_lifts D t (transport_contact_optimal D t hf hfeasible hcontact).1 C
    rw [signOptimizer_value, hv] at h
    linarith
  · rw [signOptimizer_value, hv]
    ring

/-- The magnitude transport value, defined independently of any proposed optimizer. -/
noncomputable def transportValue (t : ℝ) : ℝ :=
  sSup (Set.range (fun D : Copula 2 => ∫ x, magnitudeCost t x ∂D.toMeasure))

/-- Compactness supplies a genuine maximizer in equation (31). -/
theorem transportValue_attained (t : ℝ) :
    ∃ D : Copula 2, (∫ x, magnitudeCost t x ∂D.toMeasure) = transportValue t ∧
      ∀ E : Copula 2, (∫ x, magnitudeCost t x ∂E.toMeasure) ≤ transportValue t := by
  obtain ⟨D, hD⟩ := ProbabilityTheory.Copula.RankRegion.exists_copula_maximizer (continuous_magnitudeCost t)
  have hg : IsGreatest (Set.range (fun E : Copula 2 => ∫ x, magnitudeCost t x ∂E.toMeasure))
      (∫ x, magnitudeCost t x ∂D.toMeasure) := by
    refine ⟨⟨D, rfl⟩, ?_⟩
    rintro _ ⟨E, rfl⟩
    exact hD E
  have hv : transportValue t = ∫ x, magnitudeCost t x ∂D.toMeasure := hg.csSup_eq
  exact ⟨D, hv.symm, fun E => hv.symm ▸ hD E⟩

/-- Equation (32), including attainment of both maxima. -/
theorem supporting_maximum (t : ℝ) :
    IsGreatest (Set.range (fun C : Copula 2 => C.spearmanRho - 3 / 2 * t * C.giniGamma))
      (3 * transportValue t) := by
  obtain ⟨D, hv, hD⟩ := transportValue_attained t
  constructor
  · exact ⟨signOptimizer D t, by simpa only [hv] using signOptimizer_value D t⟩
  · rintro _ ⟨C, rfl⟩
    exact (supporting_bound_iff_transport_bound t (transportValue t)).mpr hD C

end ProbabilityTheory.Copula.RankRegion.RhoGamma
