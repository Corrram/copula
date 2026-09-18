/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.TotalPositivity

/-! # Identifying copula densities from their lower-orthant integrals -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem HasMTP2Density.absolutelyContinuous {d : ℕ} {C : Copula d}
    (h : C.HasMTP2Density) : C.toMeasure ≪ (volume : Measure (Fin d → I)) := by
  obtain ⟨f, _, _, _, he⟩ := h
  rw [he]
  exact withDensity_absolutelyContinuous _ _

/-- An integrable nonnegative candidate is the copula's density when its
lower-orthant integrals agree with the CDF. -/
theorem toMeasure_eq_withDensity_of_cdf_integral {d : ℕ} (C : Copula d)
    {f : (Fin d → I) → ℝ} (hf : Integrable f) (hn : ∀ x, 0 ≤ f x)
    (hF : ∀ u, (∫ x in Iic u, f x) = C.cdf u) :
    C.toMeasure = (volume : Measure (Fin d → I)).withDensity (fun x => ENNReal.ofReal (f x)) := by
  let μ := (volume : Measure (Fin d → I)).withDensity (fun x => ENNReal.ofReal (f x))
  have htop : Iic (fun _ : Fin d => (1 : I)) = univ := by
    ext x; simp [Pi.le_def, unitInterval.le_one']
  have htotal : (∫ x, f x) = 1 := by simpa [htop] using hF (fun _ => 1)
  have hprob : IsProbabilityMeasure μ := ⟨by
    change ((volume : Measure (Fin d → I)).withDensity (fun x => ENNReal.ofReal (f x))) univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hn), htotal]
    simp⟩
  let := hprob
  have hμ (u : Fin d → I) : μ.real (Iic u) = C.cdf u := by
    change ((volume : Measure (Fin d → I)).withDensity (fun x => ENNReal.ofReal (f x))).real (Iic u) = _
    rw [Measure.real, withDensity_apply _ measurableSet_Iic,
      ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (Filter.Eventually.of_forall hn),
      ENNReal.toReal_ofReal (integral_nonneg hn), hF]
  let D := C.isClassical_cdf.ofMeasure ⟨μ, hprob⟩ hμ
  have he : D = C := cdf_injective (C.isClassical_cdf.cdf_ofMeasure ⟨μ, hprob⟩ hμ)
  rw [← he]
  rfl

theorem integral_unit_Iic (f : ℝ → ℝ) (u : I) :
    (∫ t in Iic u, f (t : ℝ)) = ∫ t in (0 : ℝ)..(u : ℝ), f t := by
  classical
  rw [← integral_indicator measurableSet_Iic]
  have he : (Iic u).indicator (fun t : I => f (t : ℝ)) =
      fun t : I => (Iic (u : ℝ)).indicator f (t : ℝ) := rfl
  rw [he, integral_unitInterval, intervalIntegral.integral_of_le zero_le_one,
    setIntegral_indicator measurableSet_Iic, intervalIntegral.integral_of_le u.property.1]
  have hs : Ioc (0 : ℝ) 1 ∩ Iic (u : ℝ) = Ioc 0 (u : ℝ) := by
    ext t
    simp only [mem_inter_iff, mem_Ioc, mem_Iic]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, h.2.trans u.property.2⟩, h.2⟩
  rw [hs]

theorem integral_unit_Iic_one_sub_two_mul (u : I) :
    (∫ t in Iic u, 1 - 2 * (t : ℝ)) = (u : ℝ) * (1 - (u : ℝ)) := by
  rw [integral_unit_Iic (fun t => 1 - 2 * t),
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      ((show Continuous (fun t : ℝ => 2 * t) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, integral_id]
  simp only [sub_zero, smul_eq_mul, mul_one, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  ring

theorem integral_cube_Iic_mul (f g : I → ℝ) (u v : I) :
    (∫ x in Iic ![u, v], f (x 0) * g (x 1)) =
      (∫ t in Iic u, f t) * (∫ t in Iic v, g t) := by
  classical
  rw [← integral_indicator measurableSet_Iic]
  have he : (Iic ![u, v]).indicator (fun x : Fin 2 → I => f (x 0) * g (x 1)) =
      fun x : Fin 2 → I => (Iic u).indicator f (x 0) * (Iic v).indicator g (x 1) := by
    funext x
    simp only [Set.indicator, mem_Iic, Pi.le_def, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    by_cases h0 : x 0 ≤ u <;> by_cases h1 : x 1 ≤ v <;> simp [h0, h1]
  rw [he]
  change (∫ x, (Iic u).indicator f (x 0) * (Iic v).indicator g (x 1)
    ∂(independence 2).toMeasure) = _
  rw [integral_independence_mul, integral_indicator measurableSet_Iic,
    integral_indicator measurableSet_Iic]

end ProbabilityTheory.Copula
