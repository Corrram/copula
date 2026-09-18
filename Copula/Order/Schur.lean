/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.ChatterjeeExamples
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-! # Schur order of conditional distributions

We use the convex-test characterization of majorization of the functions
`u ↦ P(V ≤ t | U = u)`, for every threshold `t`. Their common mean is `t`.
This compares the predictability of the second coordinate given the first.
It is a preorder on copulas, not an antisymmetric order.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Directional Schur order, in its continuous convex-test formulation. -/
def SchurLE (C D : Copula 2) : Prop :=
  ∀ (t : I) (φ : ℝ → ℝ), Continuous φ → ConvexOn ℝ (Icc 0 1) φ →
    (∫ u : I, φ (C.conditionalCDF u t)) ≤ ∫ u : I, φ (D.conditionalCDF u t)

@[refl] theorem SchurLE.refl (C : Copula 2) : C.SchurLE C := fun _ _ _ _ => le_rfl

@[trans] theorem SchurLE.trans {C D E : Copula 2} (h : C.SchurLE D)
    (k : D.SchurLE E) : C.SchurLE E :=
  fun t φ hc hv => (h t φ hc hv).trans (k t φ hc hv)

theorem integrable_comp_conditionalCDF (C : Copula 2) (t : I)
    {φ : ℝ → ℝ} (hφ : Continuous φ) : Integrable (fun u : I => φ (C.conditionalCDF u t)) := by
  obtain ⟨b, hb⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ.continuousOn
  refine (integrable_const b).mono'
    (hφ.measurable.comp (C.measurable_conditionalCDF_left t)).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u =>
    hb _ ⟨C.conditionalCDF_nonneg u t, C.conditionalCDF_le_one u t⟩

/-- Conditional-kernel versions may be replaced almost everywhere. -/
theorem schurLE_iff_of_kernel_ae (C D : Copula 2) (κ η : Kernel I I)
    (hκ : C.conditionalKernel =ᵐ[volume] κ) (hη : D.conditionalKernel =ᵐ[volume] η) :
    C.SchurLE D ↔ ∀ (t : I) (φ : ℝ → ℝ), Continuous φ → ConvexOn ℝ (Icc 0 1) φ →
      (∫ u : I, φ ((κ u).real (Iic t))) ≤ ∫ u : I, φ ((η u).real (Iic t)) := by
  have hc (t : I) (φ : ℝ → ℝ) :
      (∫ u : I, φ (C.conditionalCDF u t)) = ∫ u : I, φ ((κ u).real (Iic t)) := by
    apply integral_congr_ae
    filter_upwards [hκ] with u hu
    simp only [conditionalCDF, hu]
  have hd (t : I) (φ : ℝ → ℝ) :
      (∫ u : I, φ (D.conditionalCDF u t)) = ∫ u : I, φ ((η u).real (Iic t)) := by
    apply integral_congr_ae
    filter_upwards [hη] with u hu
    simp only [conditionalCDF, hu]
  simp only [SchurLE, hc, hd]

/-- Measure-preserving reparametrization of conditional CDFs preserves Schur equivalence. -/
theorem schurLE_of_rearrangement (C D : Copula 2) {r : I → I}
    (hr : MeasurePreserving r volume volume)
    (h : ∀ t : I, (fun u => C.conditionalCDF u t) =ᵐ[volume]
      fun u => D.conditionalCDF (r u) t) : C.SchurLE D ∧ D.SchurLE C := by
  have he (t : I) (φ : ℝ → ℝ) (hc : Continuous φ) :
      (∫ u : I, φ (C.conditionalCDF u t)) = ∫ u : I, φ (D.conditionalCDF u t) := by
    calc
      _ = ∫ u : I, φ (D.conditionalCDF (r u) t) := integral_congr_ae (by
        filter_upwards [h t] with u hu using congrArg φ hu)
      _ = _ := by
        have hm : AEStronglyMeasurable (fun u : I => φ (D.conditionalCDF u t))
            (Measure.map r volume) := by
          rw [hr.map_eq]
          exact (hc.measurable.comp (D.measurable_conditionalCDF_left t)).aestronglyMeasurable
        simpa only [hr.map_eq] using (integral_map hr.measurable.aemeasurable hm).symm
  exact ⟨fun t φ hc _ => (he t φ hc).le, fun t φ hc _ => (he t φ hc).ge⟩

/-- Independence is a least element, by Jensen's inequality. -/
theorem schurLE_independence (C : Copula 2) : (independence 2).SchurLE C := by
  intro t φ hc hv
  have he : (∫ u : I, φ ((independence 2).conditionalCDF u t)) = φ (t : ℝ) := by
    calc
      _ = ∫ _ : I, φ (t : ℝ) := integral_congr_ae (by
        filter_upwards [conditionalKernel_independence] with u hu
        simp [conditionalCDF, hu, Measure.real, unitInterval.volume_Iic,
          ENNReal.toReal_ofReal t.property.1])
      _ = _ := by simp
  rw [he, ← C.integral_conditionalCDF t]
  exact hv.map_integral_le hc.continuousOn isClosed_Icc
    (Filter.Eventually.of_forall fun u =>
      ⟨C.conditionalCDF_nonneg u t, C.conditionalCDF_le_one u t⟩)
    (C.integrable_conditionalCDF t) (C.integrable_comp_conditionalCDF t hc)

/-- The chord through the endpoint values bounds a convex conditional functional. -/
theorem integral_convex_conditionalCDF_le (C : Copula 2) (t : I)
    {φ : ℝ → ℝ} (hc : Continuous φ) (hv : ConvexOn ℝ (Icc 0 1) φ) :
    (∫ u : I, φ (C.conditionalCDF u t)) ≤ (1 - (t : ℝ)) * φ 0 + (t : ℝ) * φ 1 := by
  have hi : Integrable (fun u : I => (1 - C.conditionalCDF u t) * φ 0 +
      C.conditionalCDF u t * φ 1) :=
    ((integrable_const 1).sub (C.integrable_conditionalCDF t)).mul_const _ |>.add
      ((C.integrable_conditionalCDF t).mul_const _)
  have h := integral_mono (C.integrable_comp_conditionalCDF t hc) hi (fun u => by
    have h := hv.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
      (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
      (sub_nonneg.mpr (C.conditionalCDF_le_one u t)) (C.conditionalCDF_nonneg u t)
      (show 1 - C.conditionalCDF u t + C.conditionalCDF u t = 1 by ring)
    simpa only [smul_eq_mul, mul_zero, mul_one, zero_add] using h)
  rw [integral_add, integral_mul_const, integral_mul_const,
    integral_sub (integrable_const 1) (C.integrable_conditionalCDF t),
    C.integral_conditionalCDF] at h
  · simpa using h
  · exact ((integrable_const 1).sub (C.integrable_conditionalCDF t)).mul_const _
  · exact (C.integrable_conditionalCDF t).mul_const _

theorem integral_conditionalCDF_of_function (D : Copula 2) {f : I → I} (hf : Measurable f)
    (h : ∀ᵐ x ∂D.toMeasure, x 1 = f (x 0)) (t : I) (φ : ℝ → ℝ) :
    (∫ u : I, φ (D.conditionalCDF u t)) = (1 - (t : ℝ)) * φ 0 + (t : ℝ) * φ 1 := by
  have he : (fun u : I => φ (D.conditionalCDF u t)) =ᵐ[volume]
      fun u => (1 - D.conditionalCDF u t) * φ 0 + D.conditionalCDF u t * φ 1 := by
    filter_upwards [D.conditionalKernel_of_function hf h] with u hu
    simp only [conditionalCDF, hu, Kernel.deterministic_apply, Measure.real,
      Measure.dirac_apply' _ measurableSet_Iic, Set.indicator]
    split_ifs <;> norm_num
  rw [integral_congr_ae he, integral_add, integral_mul_const, integral_mul_const,
    integral_sub (integrable_const 1) (D.integrable_conditionalCDF t),
    D.integral_conditionalCDF]
  · simp
  · exact ((integrable_const 1).sub (D.integrable_conditionalCDF t)).mul_const _
  · exact (D.integrable_conditionalCDF t).mul_const _

/-- Every copula is below every deterministic dependence in directional Schur order. -/
theorem schurLE_of_function (C D : Copula 2) {f : I → I} (hf : Measurable f)
    (h : ∀ᵐ x ∂D.toMeasure, x 1 = f (x 0)) : C.SchurLE D := by
  intro t φ hc hv
  rw [D.integral_conditionalCDF_of_function hf h]
  exact C.integral_convex_conditionalCDF_le t hc hv

theorem schurLE_comonotonic (C : Copula 2) : C.SchurLE (comonotonic 2) := by
  apply schurLE_of_function C _ measurable_id
  rw [toMeasure_comonotonic]
  apply (ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2
  exact Filter.Eventually.of_forall fun _ => rfl

theorem schurLE_countermonotonic (C : Copula 2) : C.SchurLE countermonotonic := by
  apply schurLE_of_function C _ unitInterval.measurable_symm
  rw [toMeasure_countermonotonic]
  apply (ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2
  exact Filter.Eventually.of_forall fun _ => rfl

/-- Chatterjee's xi respects the directional Schur preorder. -/
theorem SchurLE.chatterjeeXi_le {C D : Copula 2} (h : C.SchurLE D) :
    C.chatterjeeXi ≤ D.chatterjeeXi := by
  have hs (t : I) : (∫ u : I, C.conditionalCDF u t ^ 2) ≤ ∫ u : I, D.conditionalCDF u t ^ 2 :=
    h t (fun z => z ^ 2) (by fun_prop)
      ((convexOn_pow (𝕜 := ℝ) 2).subset (fun _ hx => hx.1) (convex_Icc 0 1))
  have hi := integral_mono C.integrable_integral_conditionalCDF_sq
    D.integrable_integral_conditionalCDF_sq hs
  unfold chatterjeeXi
  linarith

end ProbabilityTheory.Copula
