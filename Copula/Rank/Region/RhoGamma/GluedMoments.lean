/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoGamma.GluedCertificate
import Copula.Rank.Region.OrdinalSumIntegration

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoGamma.AuxiliaryCertificate

variable (A : AuxiliaryCertificate)

theorem lower_threshold (x : Fin 2 → I) :
    thresholdSign A.t (fun i => OrdinalSum.lowerEmbed A.a (x i)) = false := by
  have h0 : (OrdinalSum.lowerEmbed A.a (x 0) : ℝ) ≤ A.a := OrdinalSum.lowerEmbed_le A.a (x 0)
  have h1 : (OrdinalSum.lowerEmbed A.a (x 1) : ℝ) ≤ A.a := OrdinalSum.lowerEmbed_le A.a (x 1)
  have hh : ¬A.t ≤ max (OrdinalSum.lowerEmbed A.a (x 0) : ℝ) (OrdinalSum.lowerEmbed A.a (x 1)) := by
    have hm := max_le h0 h1
    linarith only [hm, A.a_lt_t]
  simp only [thresholdSign, hh, ite_false]

theorem upper_threshold (u v : I)
    (hc : A.h u + A.h v = ((u : ℝ) - v) ^ 2 - A.s * |(u : ℝ) - v|) :
    A.t ≤ max (OrdinalSum.upperEmbed A.a u : ℝ) (OrdinalSum.upperEmbed A.a v) := by
  have hh := A.upper_contact u v hc
  change _ = gluedPotential A.a A.t A.upper _ + gluedPotential A.a A.t A.upper _ at hh
  rw [gluedPotential_of_ge A.upper A.upper_join (OrdinalSum.le_upperEmbed A.a u),
    gluedPotential_of_ge A.upper A.upper_join (OrdinalSum.le_upperEmbed A.a v),
    A.upper_contact_signed u v hc, ← min_mul_max (OrdinalSum.upperEmbed A.a u : ℝ) (OrdinalSum.upperEmbed A.a v : ℝ)] at hh
  have hm : 0 < min (OrdinalSum.upperEmbed A.a u : ℝ) (OrdinalSum.upperEmbed A.a v) :=
    lt_min (A.a_pos.trans_le (OrdinalSum.le_upperEmbed A.a u))
      (A.a_pos.trans_le (OrdinalSum.le_upperEmbed A.a v))
  by_contra ht
  have ht' := lt_of_not_ge ht
  rw [abs_of_nonpos (by linarith)] at hh
  nlinarith only [hh, mul_pos hm (sub_pos.mpr ht')]

theorem upper_threshold_ae :
    ∀ᵐ x ∂A.D.toMeasure, thresholdSign A.t (fun i => OrdinalSum.upperEmbed A.a (x i)) = true := by
  filter_upwards [A.contact] with x hx
  simp only [thresholdSign, A.upper_threshold (x 0) (x 1) hx, ite_true]

theorem signed_integral {f : (Fin 2 → I) → ℝ} (hf : Continuous f) :
    (∫ x, (if thresholdSign A.t x then (1 : ℝ) else -1) * f x ∂A.magnitudes.toMeasure) =
      -(A.a : ℝ) * (∫ u : I, f (fun _ => OrdinalSum.lowerEmbed A.a u)) +
        A.z * ∫ x, f (fun i => OrdinalSum.upperEmbed A.a (x i)) ∂A.D.toMeasure := by
  have hL : (fun x : Fin 2 → I =>
      (if thresholdSign A.t (fun i => OrdinalSum.lowerEmbed A.a (x i)) then (1 : ℝ) else -1) *
        f (fun i => OrdinalSum.lowerEmbed A.a (x i))) =
      (fun x => -f (fun i => OrdinalSum.lowerEmbed A.a (x i))) := by
    funext x
    simp only [A.lower_threshold, Bool.false_eq_true, ite_false, neg_one_mul]
  have hU : (fun x : Fin 2 → I =>
      (if thresholdSign A.t (fun i => OrdinalSum.upperEmbed A.a (x i)) then (1 : ℝ) else -1) *
        f (fun i => OrdinalSum.upperEmbed A.a (x i))) =ᵐ[A.D.toMeasure]
      (fun x => f (fun i => OrdinalSum.upperEmbed A.a (x i))) := by
    filter_upwards [A.upper_threshold_ae] with x hx
    simp only [hx, ite_true, one_mul]
  have hm : Measurable (fun x : Fin 2 → I => (if thresholdSign A.t x then (1 : ℝ) else -1) * f x) :=
    (Measurable.ite ((measurableSet_singleton true).preimage (measurable_thresholdSign A.t))
      measurable_const measurable_const).mul hf.measurable
  change (∫ x, _ ∂((comonotonic 2).ordinalSum A.D A.a).toMeasure) = _
  rw [integral_ordinalSum_measurable _ _ _ hm (by
    rw [hL]
    exact integrable_continuous_cube _ (by fun_prop))
    ((integrable_continuous_cube _ (show Continuous (fun x => f (fun i => OrdinalSum.upperEmbed A.a (x i))) by fun_prop)).congr hU.symm)]
  rw [hL, integral_neg, integral_comonotonic _ (by fun_prop), integral_congr_ae hU]
  have hz : 1 - (A.a : ℝ) = A.z := by linarith only [A.a_add_z]
  rw [hz]
  ring


theorem integral_min (D : Copula 2) :
    (∫ x, min (x 0 : ℝ) (x 1 : ℝ) ∂D.toMeasure) = (D.spearmanFootrule + 2) / 6 := by
  have hh := D.concordanceQ_comonotonic
  rw [concordanceQ_comm, concordanceQ] at hh
  simp only [cdf_comonotonic_two] at hh
  linarith

theorem integral_lower_min :
    (∫ u : I, min (OrdinalSum.lowerEmbed A.a u : ℝ) (OrdinalSum.lowerEmbed A.a u)) =
      (A.a : ℝ) / 2 := by
  simp only [min_self, OrdinalSum.lowerEmbed]
  rw [integral_const_mul, integral_unit_id]
  ring

theorem integral_upper_min :
    (∫ x, min (OrdinalSum.upperEmbed A.a (x 0) : ℝ) (OrdinalSum.upperEmbed A.a (x 1)) ∂A.D.toMeasure) =
      (A.a : ℝ) + A.z * (A.D.spearmanFootrule + 2) / 6 := by
  have hz : 1 - (A.a : ℝ) = A.z := by linarith only [A.a_add_z]
  have he : (fun x : Fin 2 → I =>
      min (OrdinalSum.upperEmbed A.a (x 0) : ℝ) (OrdinalSum.upperEmbed A.a (x 1))) =
      fun x => (A.a : ℝ) + A.z * min (x 0 : ℝ) (x 1 : ℝ) := by
    funext x
    simp only [OrdinalSum.upperEmbed, hz]
    rw [min_add_add_left, mul_min_of_nonneg _ _ A.z_pos.le]
  rw [he, integral_add (integrable_const _) (integrable_continuous_cube _ (by fun_prop)),
    integral_const, integral_const_mul, integral_min]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

theorem gamma :
    A.copula.giniGamma = 1 - 2 * (A.a : ℝ) ^ 2 - A.z ^ 2 * (1 - A.D.spearmanFootrule) / 3 := by
  unfold copula signOptimizer
  erw [signCopula_gamma]
  erw [A.signed_integral (f := fun x => min (x 0 : ℝ) (x 1 : ℝ)) (by fun_prop),
    A.integral_lower_min, A.integral_upper_min]
  have hz : A.z = 1 - (A.a : ℝ) := by linarith only [A.a_add_z]
  rw [hz]
  ring

theorem integral_lower_product :
    (∫ u : I, (OrdinalSum.lowerEmbed A.a u : ℝ) * OrdinalSum.lowerEmbed A.a u) =
      (A.a : ℝ) ^ 2 / 3 := by
  have he : (fun u : I => (OrdinalSum.lowerEmbed A.a u : ℝ) * OrdinalSum.lowerEmbed A.a u) =
      fun u : I => (A.a : ℝ) ^ 2 * (u : ℝ) ^ 2 := by funext u; dsimp [OrdinalSum.lowerEmbed]; ring
  rw [he, integral_const_mul, integral_unit_pow]
  norm_num
  ring

theorem integral_upper_product :
    (∫ x, (OrdinalSum.upperEmbed A.a (x 0) : ℝ) * OrdinalSum.upperEmbed A.a (x 1) ∂A.D.toMeasure) =
      (A.a : ℝ) ^ 2 + (A.a : ℝ) * A.z + A.z ^ 2 * (A.D.spearmanRho + 3) / 12 := by
  have hz : 1 - (A.a : ℝ) = A.z := by linarith only [A.a_add_z]
  have he : (fun x : Fin 2 → I =>
      (OrdinalSum.upperEmbed A.a (x 0) : ℝ) * OrdinalSum.upperEmbed A.a (x 1)) =
      fun x => (A.a : ℝ) ^ 2 + ((A.a : ℝ) * A.z) * (x 0 : ℝ) +
        ((A.a : ℝ) * A.z) * (x 1 : ℝ) + A.z ^ 2 * ((x 0 : ℝ) * x 1) := by
    funext x
    simp only [OrdinalSum.upperEmbed, hz]
    ring
  rw [he, integral_add, integral_add, integral_add, integral_const,
    integral_const_mul, integral_const_mul, integral_const_mul,
    A.D.integral_coe_eval, A.D.integral_coe_eval]
  · simp only [probReal_univ, smul_eq_mul, one_mul, spearmanRho]
    ring
  all_goals exact integrable_continuous_cube _ (by fun_prop)

theorem rho :
    A.copula.spearmanRho = 1 - 2 * (A.a : ℝ) ^ 3 - A.z ^ 3 * (1 - A.D.spearmanRho) / 4 := by
  unfold copula signOptimizer
  erw [signCopula_rho]
  have he : (fun x : Fin 2 → I => (if thresholdSign A.t x then (1 : ℝ) else -1) *
      (x 0 : ℝ) * x 1) = fun x => (if thresholdSign A.t x then (1 : ℝ) else -1) *
      ((x 0 : ℝ) * x 1) := by funext x; ring
  erw [he, A.signed_integral (f := fun x => (x 0 : ℝ) * x 1) (by fun_prop),
    A.integral_lower_product, A.integral_upper_product]
  have hz : A.z = 1 - (A.a : ℝ) := by linarith only [A.a_add_z]
  rw [hz]
  ring

theorem maximizes_rho (C : Copula 2) (h : C.giniGamma = A.copula.giniGamma) :
    C.spearmanRho ≤ A.copula.spearmanRho := by
  have hh := A.supporting_bound C
  rw [h] at hh
  linarith

end ProbabilityTheory.Copula.RankRegion.RhoGamma.AuxiliaryCertificate
