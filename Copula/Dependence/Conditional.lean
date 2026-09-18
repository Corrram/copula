/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.TotalPositivity
import Copula.Rank.ChatterjeeExamples

/-! # Conditional kernels as witnesses of stochastic increasingness -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Disintegration along the first coordinate recovers the copula CDF. -/
theorem cdf_eq_integral_conditionalCDF (C : Copula 2) (u v : I) :
    C.cdf ![u, v] = ∫ t in Iic u, C.conditionalCDF t v := by
  have hm := compProd_map_condDistrib (μ := C.toMeasure) (mα := inferInstance)
    (mβ := inferInstance) (X := fun x : Fin 2 → I => x 0) (Y := fun x => x 1)
    (measurable_pi_apply 0).aemeasurable (measurable_pi_apply 1).aemeasurable
  rw [C.map_eval] at hm
  have h := congrArg (fun μ : Measure (I × I) => μ (Iic u ×ˢ Iic v)) hm
  rw [Measure.compProd_apply_prod measurableSet_Iic measurableSet_Iic,
    Measure.map_apply (by fun_prop) (measurableSet_Iic.prod measurableSet_Iic)] at h
  have he : (fun x : Fin 2 → I => (x 0, x 1)) ⁻¹' (Iic u ×ˢ Iic v) = Iic ![u, v] := by
    ext x
    simp [Pi.le_def, Fin.forall_fin_two]
  rw [he] at h
  unfold conditionalCDF Measure.real cdf
  rw [integral_toReal (C.conditionalKernel.measurable_coe measurableSet_Iic).aemeasurable
    (Filter.Eventually.of_forall fun t => measure_lt_top _ _)]
  exact congrArg ENNReal.toReal h.symm

theorem cdf_eq_integral_kernel (C : Copula 2) (κ : Kernel I I)
    (hκ : C.conditionalKernel =ᵐ[volume] κ) (u v : I) :
    C.cdf ![u, v] = ∫ t in Iic u, (κ t).real (Iic v) := by
  rw [C.cdf_eq_integral_conditionalCDF]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hκ] with t ht
  simp only [conditionalCDF, ht]

theorem integral_Iic_add_Ioc_unit {f : I → ℝ} (hf : Integrable f) {a b : I} (hab : a ≤ b) :
    (∫ t in Iic a, f t) + (∫ t in Ioc a b, f t) = ∫ t in Iic b, f t := by
  rw [← setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
    hf.integrableOn hf.integrableOn, Iic_union_Ioc_eq_Iic hab]

/-- The indefinite integral of an antitone function satisfies the concavity chord inequality. -/
theorem integral_Iic_concave_of_antitone {f : I → ℝ} (hf : Integrable f) (ha : Antitone f)
    (a b c : I) (hab : a ≤ b) (hbc : b ≤ c) :
    ((b : ℝ) - (a : ℝ)) * (∫ t in Iic c, f t) +
      ((c : ℝ) - (b : ℝ)) * (∫ t in Iic a, f t) ≤
        ((c : ℝ) - (a : ℝ)) * (∫ t in Iic b, f t) := by
  have hl := setIntegral_mono_on (integrable_const (f b)) hf.integrableOn
    measurableSet_Ioc (fun t (ht : t ∈ Ioc a b) => ha ht.2)
  have hr := setIntegral_mono_on hf.integrableOn (integrable_const (f b))
    measurableSet_Ioc (fun t (ht : t ∈ Ioc b c) => ha ht.1.le)
  have hab' : (a : ℝ) ≤ (b : ℝ) := hab
  have hbc' : (b : ℝ) ≤ (c : ℝ) := hbc
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, unitInterval.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab'), smul_eq_mul] at hl
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, unitInterval.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hbc'), smul_eq_mul] at hr
  have h₁ := integral_Iic_add_Ioc_unit hf hab
  have h₂ := integral_Iic_add_Ioc_unit hf hbc
  nlinarith [mul_nonneg (sub_nonneg.mpr hbc') (sub_nonneg.mpr hl),
    mul_nonneg (sub_nonneg.mpr hab') (sub_nonneg.mpr hr)]

/-- A stochastically increasing version of the conditional kernel proves SI.
The almost-everywhere identification makes this independent of null-set choices. -/
theorem isSI_of_kernel (C : Copula 2) (κ : Kernel I I) [IsMarkovKernel κ]
    (hκ : C.conditionalKernel =ᵐ[volume] κ)
    (hmono : ∀ v : I, Antitone (fun u => (κ u).real (Iic v))) : C.IsSI := by
  intro a b c v hab hbc
  simp_rw [C.cdf_eq_integral_kernel κ hκ]
  apply integral_Iic_concave_of_antitone _ (hmono v) a b c hab hbc
  refine (integrable_const (1 : ℝ)).mono'
    (κ.measurable_coe measurableSet_Iic).ennreal_toReal.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one

/-- TP2 of a version of the conditional CDF kernel. This allows singular copulas. -/
def HasTP2Kernel (C : Copula 2) : Prop :=
  ∃ κ : Kernel I I, IsMarkovKernel κ ∧ C.conditionalKernel =ᵐ[volume] κ ∧
    IsTP2 (fun u v : I => (κ u).real (Iic v))

theorem HasTP2Kernel.isSI {C : Copula 2} (h : C.HasTP2Kernel) : C.IsSI := by
  obtain ⟨κ, hMarkov, hκ, htp⟩ := h
  let := hMarkov
  apply C.isSI_of_kernel κ hκ
  intro v a b hab
  have ht := htp a b v 1 hab v.property.2
  have he : Iic (1 : I) = univ := by ext x; simp [unitInterval.le_one']
  simpa [he] using ht

end ProbabilityTheory.Copula
