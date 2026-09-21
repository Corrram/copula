/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoGamma.AuxiliaryCertificate
import Copula.Rank.Region.RhoGamma.SignAttainment
import Copula.OrdinalSum.Blocks

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoGamma.AuxiliaryCertificate

variable (A : AuxiliaryCertificate)

noncomputable def a : I :=
  ⟨centralLength A.s A.c,
    (splitting_properties A.s_pos A.c_neg A.w_nonneg A.discriminant).1.le,
    (splitting_properties A.s_pos A.c_neg A.w_nonneg A.discriminant).2.1.le⟩

noncomputable def z : ℝ := cornerLength A.s A.c
noncomputable def t : ℝ := supportingSlope A.s A.c

theorem a_pos : 0 < (A.a : ℝ) :=
  (splitting_properties A.s_pos A.c_neg A.w_nonneg A.discriminant).1

theorem a_lt_one : (A.a : ℝ) < 1 :=
  (splitting_properties A.s_pos A.c_neg A.w_nonneg A.discriminant).2.1

theorem z_pos : 0 < A.z :=
  (splitting_properties A.s_pos A.c_neg A.w_nonneg A.discriminant).2.2.1

theorem a_add_z : (A.a : ℝ) + A.z = 1 :=
  (splitting_properties A.s_pos A.c_neg A.w_nonneg A.discriminant).2.2.2.1

theorem a_lt_t : (A.a : ℝ) < A.t :=
  (splitting_properties A.s_pos A.c_neg A.w_nonneg A.discriminant).2.2.2.2.1

theorem slope_bound : A.t + A.z * A.w ≤ 2 * (A.a : ℝ) :=
  (splitting_properties A.s_pos A.c_neg A.w_nonneg A.discriminant).2.2.2.2.2.1

theorem matching : A.z ^ 2 * A.c = 2 * (A.a : ℝ) * ((A.a : ℝ) - A.t) :=
  (splitting_properties A.s_pos A.c_neg A.w_nonneg A.discriminant).2.2.2.2.2.2

theorem t_eq : A.t = A.z * A.s := by unfold t supportingSlope z; ring

noncomputable def upper : ℝ → ℝ := upperPotential A.a A.t A.z A.h

@[fun_prop] theorem continuous_upper : Continuous A.upper :=
  continuous_upperPotential _ _ _ A.lipschitz.continuous

theorem upper_join : A.upper A.a = (A.a : ℝ) * (A.t - A.a) / 2 :=
  upperPotential_join (A.at_zero.symm ▸ A.matching)

theorem upper_monotone : MonotoneOn A.upper (Set.Icc (A.a : ℝ) 1) :=
  (upperPotential_monotone A.z_pos A.w_nonneg A.lipschitz A.slope_bound).mono
    (fun _ hx => hx.1)

theorem upper_positive (x y : ℝ) (hax : (A.a : ℝ) ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    x * (y - A.t) ≤ A.upper x + A.upper y :=
  upperPotential_positive_cost A.z_pos A.a_add_z A.t_eq A.feasible x y hax hxy hy1

noncomputable def dual : ℝ → ℝ := gluedPotential A.a A.t A.upper

@[fun_prop] theorem continuous_dual : Continuous A.dual :=
  continuous_gluedPotential A.continuous_upper A.upper_join

theorem dual_feasible (x y : I) :
    min (x : ℝ) y * |max (x : ℝ) y - A.t| ≤ A.dual x + A.dual y :=
  gluedPotential_feasible A.a.property.1 A.a_lt_t.le
    (by nlinarith only [A.slope_bound, mul_nonneg A.z_pos.le A.w_nonneg])
    A.upper_join A.upper_monotone A.upper_positive x y

noncomputable def magnitudes : Copula 2 := (comonotonic 2).ordinalSum A.D A.a


theorem upper_embed_value (u : I) :
    A.upper (OrdinalSum.upperEmbed A.a u) =
      (((A.a : ℝ) + A.z * u) ^ 2 - A.t * ((A.a : ℝ) + A.z * u)) / 2 -
        A.z ^ 2 / 2 * A.h u := by
  have hz : 1 - (A.a : ℝ) = A.z := by linarith only [A.a_add_z]
  have he : (OrdinalSum.upperEmbed A.a u : ℝ) = (A.a : ℝ) + A.z * u := by
    simp only [OrdinalSum.upperEmbed, hz]
  unfold upper upperPotential
  rw [he]
  have hu : (((A.a : ℝ) + A.z * u - A.a) / A.z) = (u : ℝ) := by
    field_simp [ne_of_gt A.z_pos]
    ring
  rw [hu]

theorem upper_contact_signed (u v : I)
    (hc : A.h u + A.h v = ((u : ℝ) - v) ^ 2 - A.s * |(u : ℝ) - v|) :
    A.upper (OrdinalSum.upperEmbed A.a u) + A.upper (OrdinalSum.upperEmbed A.a v) =
      (OrdinalSum.upperEmbed A.a u : ℝ) * OrdinalSum.upperEmbed A.a v -
        A.t * min (OrdinalSum.upperEmbed A.a u : ℝ) (OrdinalSum.upperEmbed A.a v) := by
  wlog huv : (u : ℝ) ≤ v generalizing u v
  · have hh := this v u (by simpa only [add_comm, sub_sq_comm, abs_sub_comm] using hc) (le_of_not_ge huv)
    simpa only [add_comm, mul_comm, min_comm] using hh
  have hz : 1 - (A.a : ℝ) = A.z := by linarith only [A.a_add_z]
  have hxy : (OrdinalSum.upperEmbed A.a u : ℝ) ≤ OrdinalSum.upperEmbed A.a v := by
    simp only [OrdinalSum.upperEmbed, hz]
    linarith only [mul_le_mul_of_nonneg_left huv A.z_pos.le]
  rw [min_eq_left hxy, A.upper_embed_value, A.upper_embed_value]
  simp only [OrdinalSum.upperEmbed, hz]
  rw [abs_of_nonpos (sub_nonpos.mpr huv)] at hc
  rw [A.t_eq]
  nlinarith only [congrArg (fun r : ℝ => A.z ^ 2 * r) hc]

theorem upper_contact (u v : I)
    (hc : A.h u + A.h v = ((u : ℝ) - v) ^ 2 - A.s * |(u : ℝ) - v|) :
    min (OrdinalSum.upperEmbed A.a u : ℝ) (OrdinalSum.upperEmbed A.a v) *
        |max (OrdinalSum.upperEmbed A.a u : ℝ) (OrdinalSum.upperEmbed A.a v) - A.t| =
      A.dual (OrdinalSum.upperEmbed A.a u) + A.dual (OrdinalSum.upperEmbed A.a v) := by
  apply le_antisymm (A.dual_feasible _ _)
  change gluedPotential A.a A.t A.upper _ + gluedPotential A.a A.t A.upper _ ≤ _
  rw [gluedPotential_of_ge A.upper A.upper_join (OrdinalSum.le_upperEmbed A.a u),
    gluedPotential_of_ge A.upper A.upper_join (OrdinalSum.le_upperEmbed A.a v),
    A.upper_contact_signed u v hc]
  have hh := mul_le_mul_of_nonneg_left
    (le_abs_self (max (OrdinalSum.upperEmbed A.a u : ℝ) (OrdinalSum.upperEmbed A.a v) - A.t))
    (le_min (OrdinalSum.upperEmbed A.a u).property.1 (OrdinalSum.upperEmbed A.a v).property.1)
  rw [mul_sub, min_mul_max] at hh
  nlinarith only [hh]

theorem lower_contact (u : I) :
    (OrdinalSum.lowerEmbed A.a u : ℝ) * |(OrdinalSum.lowerEmbed A.a u : ℝ) - A.t| =
      A.dual (OrdinalSum.lowerEmbed A.a u) + A.dual (OrdinalSum.lowerEmbed A.a u) := by
  change _ = gluedPotential A.a A.t A.upper _ + gluedPotential A.a A.t A.upper _
  rw [gluedPotential_of_le A.upper (OrdinalSum.lowerEmbed_le A.a u)]
  rw [abs_of_nonpos (by
    have hh := OrdinalSum.lowerEmbed_le A.a u
    have ht := A.a_lt_t
    change (OrdinalSum.lowerEmbed A.a u : ℝ) ≤ A.a at hh
    linarith)]
  ring

theorem magnitude_contact :
    ∀ᵐ x ∂A.magnitudes.toMeasure,
      magnitudeCost A.t x = A.dual (x 0) + A.dual (x 1) := by
  have hm : MeasurableSet {x : Fin 2 → I | magnitudeCost A.t x = A.dual (x 0) + A.dual (x 1)} :=
    isClosed_eq (continuous_magnitudeCost A.t) (by fun_prop) |>.measurableSet
  rw [magnitudes, toMeasure_ordinalSum, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (show Measurable (fun (x : Fin 2 → I) i => OrdinalSum.lowerEmbed A.a (x i)) by fun_prop).aemeasurable hm).2
    rw [toMeasure_comonotonic]
    apply (ae_map_iff (show Measurable (fun (u : I) (_ : Fin 2) => u) by fun_prop).aemeasurable (by
      exact hm.preimage (by fun_prop))).2
    filter_upwards [] with u
    simpa only [magnitudeCost, min_self, max_self] using A.lower_contact u
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (show Measurable (fun (x : Fin 2 → I) i => OrdinalSum.upperEmbed A.a (x i)) by fun_prop).aemeasurable hm).2
    filter_upwards [A.contact] with x hx
    exact A.upper_contact (x 0) (x 1) hx

noncomputable def copula : Copula 2 := signOptimizer A.magnitudes A.t

/-- Every concrete auxiliary branch yields an attained global rho–gamma support line. -/
theorem supporting_bound (C : Copula 2) :
    C.spearmanRho - 3 / 2 * A.t * C.giniGamma ≤
      A.copula.spearmanRho - 3 / 2 * A.t * A.copula.giniGamma :=
  transport_optimizer_lifts A.magnitudes A.t
    (transport_contact_optimal A.magnitudes A.t
      (show Continuous (fun u : I => A.dual u) by fun_prop)
      (fun x => A.dual_feasible (x 0) (x 1)) A.magnitude_contact).1 C

end ProbabilityTheory.Copula.RankRegion.RhoGamma.AuxiliaryCertificate
