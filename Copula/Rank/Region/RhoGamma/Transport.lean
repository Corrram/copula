/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel

Adapted from Corrram/lean-verifications, commit
9e144da5e0d8e2b59dadf9cef090947cb2220313.
Source module: Papers.AnsariRockelSteinmassl2026RhoGamma.Transport
Imports and namespaces adapted to the copula package; unused helpers omitted.
-/
import Copula.Rank.Region.RhoGamma.SignMagnitude

/-! # The supporting functional and transport weak duality

The magnitude law is constructed from the original copula. The supporting
bound and contact-set certificate do not assume the proposed optimizer.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoGamma

noncomputable def magnitudeCost (t : ℝ) (x : Fin 2 → I) : ℝ :=
  min (x 0 : ℝ) (x 1 : ℝ) * |max (x 0 : ℝ) (x 1 : ℝ) - t|

@[fun_prop] theorem continuous_magnitudeCost (t : ℝ) : Continuous (magnitudeCost t) := by
  unfold magnitudeCost
  fun_prop

theorem integral_magnitudeCopula (C : Copula 2) {f : (Fin 2 → I) → ℝ}
    (hf : Continuous f) :
    (∫ x, f x ∂(magnitudeCopula C).toMeasure) =
      ∫ x, f (fun i => rankMagnitude (x i)) ∂C.toMeasure := by
  change (∫ x, f x ∂(C.toMeasure.map (fun x i => rankMagnitude (x i)))) = _
  exact integral_map (show Continuous (fun x : Fin 2 → I => fun i => rankMagnitude (x i)) by
    fun_prop).measurable.aemeasurable hf.aestronglyMeasurable

theorem supporting_functional (C : Copula 2) (t : ℝ) :
    C.spearmanRho - 3 / 2 * t * C.giniGamma =
      3 * (∫ x, rankSign x * min (rankMagnitude (x 0) : ℝ) (rankMagnitude (x 1) : ℝ) *
        (max (rankMagnitude (x 0) : ℝ) (rankMagnitude (x 1) : ℝ) - t) ∂C.toMeasure) := by
  have hp (x : Fin 2 → I) :
      rankSign x * min (rankMagnitude (x 0) : ℝ) (rankMagnitude (x 1) : ℝ) *
        (max (rankMagnitude (x 0) : ℝ) (rankMagnitude (x 1) : ℝ) - t) =
      (2 * (x 0 : ℝ) - 1) * (2 * (x 1 : ℝ) - 1) -
        t * (|(x 0 : ℝ) + x 1 - 1| - |(x 0 : ℝ) - x 1|) := by
    rw [mul_sub, mul_assoc, min_mul_max,
      ← mul_assoc, sign_product_identity, mul_comm _ t, sign_min_magnitude_identity]
  simp_rw [hp]
  rw [integral_sub, integral_const_mul, sign_magnitude_rho, sign_magnitude_gamma]
  · simp_rw [sign_product_identity, sign_min_magnitude_identity]
    ring
  all_goals exact Copula.integrable_continuous_cube C.toMeasure (by fun_prop)

theorem supporting_functional_le (C : Copula 2) (t : ℝ) :
    C.spearmanRho - 3 / 2 * t * C.giniGamma ≤
      3 * (∫ x, magnitudeCost t x ∂(magnitudeCopula C).toMeasure) := by
  have hp (x : Fin 2 → I) :
      (2 * (x 0 : ℝ) - 1) * (2 * (x 1 : ℝ) - 1) -
        t * (|(x 0 : ℝ) + x 1 - 1| - |(x 0 : ℝ) - x 1|) ≤
      magnitudeCost t (fun i => rankMagnitude (x i)) := by
    rw [← sign_product_identity, ← sign_min_magnitude_identity]
    have he : rankSign x * (rankMagnitude (x 0) : ℝ) * rankMagnitude (x 1) -
        t * (rankSign x * min (rankMagnitude (x 0) : ℝ) (rankMagnitude (x 1) : ℝ)) =
        min (rankMagnitude (x 0) : ℝ) (rankMagnitude (x 1) : ℝ) *
          (rankSign x * (max (rankMagnitude (x 0) : ℝ) (rankMagnitude (x 1) : ℝ) - t)) := by
      linear_combination -(rankSign x) *
        (min_mul_max (rankMagnitude (x 0) : ℝ) (rankMagnitude (x 1) : ℝ))
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (le_min (rankMagnitude (x 0)).property.1
      (rankMagnitude (x 1)).property.1)
    unfold rankSign
    generalize SignType.sign ((2 * (x 0 : ℝ) - 1) * (2 * (x 1 : ℝ) - 1)) = s
    cases s
    · change (0 : ℝ) * _ ≤ _
      simpa only [zero_mul] using abs_nonneg (max (rankMagnitude (x 0) : ℝ) (rankMagnitude (x 1) : ℝ) - t)
    · change (-1 : ℝ) * _ ≤ _
      simpa only [neg_one_mul] using neg_le_abs (max (rankMagnitude (x 0) : ℝ) (rankMagnitude (x 1) : ℝ) - t)
    · change (1 : ℝ) * _ ≤ _
      simpa only [one_mul] using le_abs_self (max (rankMagnitude (x 0) : ℝ) (rankMagnitude (x 1) : ℝ) - t)
  rw [integral_magnitudeCopula _ (continuous_magnitudeCost t)]
  have hi := integral_mono
    (Copula.integrable_continuous_cube C.toMeasure (by fun_prop))
    (Copula.integrable_continuous_cube C.toMeasure (by fun_prop)) hp
  rw [integral_sub, integral_const_mul] at hi
  · have hr := sign_magnitude_rho C
    have hg := sign_magnitude_gamma C
    simp_rw [sign_product_identity] at hr
    simp_rw [sign_min_magnitude_identity] at hg
    rw [hr, hg]
    linarith
  all_goals exact Copula.integrable_continuous_cube C.toMeasure (by fun_prop)

theorem transport_weak_duality (C : Copula 2) (t : ℝ) {f : I → ℝ}
    (hf : Continuous f) (hfeasible : ∀ x : Fin 2 → I, magnitudeCost t x ≤ f (x 0) + f (x 1)) :
    (∫ x, magnitudeCost t x ∂C.toMeasure) ≤ 2 * ∫ u : I, f u := by
  have hi := integral_mono (Copula.integrable_continuous_cube C.toMeasure (by fun_prop))
    (Copula.integrable_continuous_cube C.toMeasure (by fun_prop)) hfeasible
  rw [integral_add, C.integral_eval 0 f hf.measurable, C.integral_eval 1 f hf.measurable] at hi
  · linarith
  all_goals exact Copula.integrable_continuous_cube C.toMeasure (by fun_prop)

theorem transport_contact_value (C : Copula 2) (t : ℝ) {f : I → ℝ}
    (hf : Continuous f)
    (hcontact : ∀ᵐ x ∂C.toMeasure, magnitudeCost t x = f (x 0) + f (x 1)) :
    (∫ x, magnitudeCost t x ∂C.toMeasure) = 2 * ∫ u : I, f u := by
  rw [integral_congr_ae hcontact, integral_add,
    C.integral_eval 0 f hf.measurable, C.integral_eval 1 f hf.measurable]
  · ring
  all_goals exact Copula.integrable_continuous_cube C.toMeasure (by fun_prop)

theorem transport_contact_optimal (C : Copula 2) (t : ℝ) {f : I → ℝ}
    (hf : Continuous f) (hfeasible : ∀ x : Fin 2 → I, magnitudeCost t x ≤ f (x 0) + f (x 1))
    (hcontact : ∀ᵐ x ∂C.toMeasure, magnitudeCost t x = f (x 0) + f (x 1)) :
    (∀ D : Copula 2, (∫ x, magnitudeCost t x ∂D.toMeasure) ≤
      ∫ x, magnitudeCost t x ∂C.toMeasure) ∧
    (∀ g : I → ℝ, Continuous g → (∀ x : Fin 2 → I, magnitudeCost t x ≤ g (x 0) + g (x 1)) →
      (2 * ∫ u : I, f u) ≤ 2 * ∫ u : I, g u) := by
  have hv := transport_contact_value C t hf hcontact
  constructor
  · intro D
    rw [hv]
    exact transport_weak_duality D t hf hfeasible
  · intro g hg hgf
    rw [← hv]
    exact transport_weak_duality C t hg hgf

end ProbabilityTheory.Copula.RankRegion.RhoGamma
