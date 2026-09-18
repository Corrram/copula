/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Integration
import Mathlib.Probability.Kernel.CondDistrib

/-! # Conditional distributions of the second coordinate given the first -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- A regular conditional distribution of coordinate `1` given coordinate `0`.
Its values on a null set of conditioning points are immaterial. -/
noncomputable def conditionalKernel (C : Copula 2) : Kernel I I :=
  condDistrib (fun x : Fin 2 → I => x 1) (fun x => x 0) C.toMeasure

instance (C : Copula 2) : IsMarkovKernel C.conditionalKernel :=
  inferInstanceAs (IsMarkovKernel (condDistrib _ _ C.toMeasure))

/-- The conditional CDF `P(V ≤ t | U = u)`, for a fixed version of the kernel. -/
noncomputable def conditionalCDF (C : Copula 2) (u t : I) : ℝ :=
  (C.conditionalKernel u).real (Iic t)

theorem conditionalCDF_nonneg (C : Copula 2) (u t : I) : 0 ≤ C.conditionalCDF u t :=
  measureReal_nonneg

theorem conditionalCDF_le_one (C : Copula 2) (u t : I) : C.conditionalCDF u t ≤ 1 :=
  measureReal_le_one

theorem measurable_conditionalCDF (C : Copula 2) :
    Measurable (fun p : I × I => C.conditionalCDF p.2 p.1) := by
  have h := Kernel.measurable_kernel_prodMk_left
    (κ := C.conditionalKernel.comap Prod.snd measurable_snd)
    (t := {p : (I × I) × I | p.2 ≤ p.1.1})
    (measurableSet_le measurable_snd measurable_fst.fst)
  exact h.ennreal_toReal

theorem measurable_conditionalCDF_left (C : Copula 2) (t : I) :
    Measurable (fun u => C.conditionalCDF u t) :=
  C.measurable_conditionalCDF.comp (measurable_const.prodMk measurable_id)

theorem integrable_conditionalCDF (C : Copula 2) (t : I) :
    Integrable (fun u => C.conditionalCDF u t) := by
  refine (integrable_const (1 : ℝ)).mono'
    (C.measurable_conditionalCDF_left t).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (C.conditionalCDF_nonneg u t)]
    exact C.conditionalCDF_le_one u t

theorem conditionalKernel_comp_volume (C : Copula 2) :
    C.conditionalKernel ∘ₘ (volume : Measure I) = volume := by
  have h := condDistrib_comp_map (μ := C.toMeasure)
    (mα := inferInstance) (mβ := inferInstance)
    (X := fun x : Fin 2 → I => x 0) (Y := fun x => x 1)
    (measurable_pi_apply 0).aemeasurable (measurable_pi_apply 1).aemeasurable
  simpa only [conditionalKernel, C.map_eval] using h

/-- Averaging a conditional CDF recovers the uniform second marginal. -/
theorem integral_conditionalCDF (C : Copula 2) (t : I) :
    (∫ u : I, C.conditionalCDF u t) = (t : ℝ) := by
  have h := congrArg (fun μ : Measure I => μ (Iic t)) C.conditionalKernel_comp_volume
  rw [Measure.bind_apply measurableSet_Iic C.conditionalKernel.aemeasurable,
    unitInterval.volume_Iic] at h
  unfold conditionalCDF Measure.real
  rw [integral_toReal (C.conditionalKernel.measurable_coe measurableSet_Iic).aemeasurable
    (Filter.Eventually.of_forall fun u => measure_lt_top _ _), h,
    ENNReal.toReal_ofReal t.property.1]

theorem integrable_conditionalCDF_sq (C : Copula 2) (t : I) :
    Integrable (fun u => C.conditionalCDF u t ^ 2) := by
  refine (C.integrable_conditionalCDF t).mono'
    ((C.measurable_conditionalCDF_left t).pow_const 2).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [C.conditionalCDF_nonneg u t, C.conditionalCDF_le_one u t]

theorem integral_conditionalCDF_sq_le (C : Copula 2) (t : I) :
    (∫ u : I, C.conditionalCDF u t ^ 2) ≤ (t : ℝ) := by
  rw [← C.integral_conditionalCDF t]
  apply integral_mono (C.integrable_conditionalCDF_sq t) (C.integrable_conditionalCDF t)
  intro u
  nlinarith [C.conditionalCDF_nonneg u t, C.conditionalCDF_le_one u t]

end ProbabilityTheory.Copula
