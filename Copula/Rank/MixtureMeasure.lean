/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Mixture
import Copula.Rank.Integration

/-! # Probability laws and integration for copula mixtures -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem toMeasure_mix {d : ℕ} (C D : Copula d) (a : I) :
    (C.mix D a).toMeasure = ENNReal.ofReal (a : ℝ) • C.toMeasure +
      ENNReal.ofReal (1 - (a : ℝ)) • D.toMeasure := by
  let μ := ENNReal.ofReal (a : ℝ) • C.toMeasure +
    ENNReal.ofReal (1 - (a : ℝ)) • D.toMeasure
  have hprob : IsProbabilityMeasure μ := ⟨by
    simp only [μ, Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    rw [← ENNReal.ofReal_add a.property.1 (sub_nonneg.mpr a.property.2)]
    simp⟩
  have hμ (u : Fin d → I) : μ.real (Iic u) = (C.mix D a).cdf u := by
    change (ENNReal.ofReal (a : ℝ) • C.toMeasure +
      ENNReal.ofReal (1 - (a : ℝ)) • D.toMeasure).real (Iic u) = _
    rw [measureReal_add_apply (by simp [Measure.smul_apply, ENNReal.mul_ne_top])
      (by simp [Measure.smul_apply, ENNReal.mul_ne_top]),
      measureReal_ennreal_smul_apply, measureReal_ennreal_smul_apply,
      ENNReal.toReal_ofReal a.property.1, ENNReal.toReal_ofReal (sub_nonneg.mpr a.property.2),
      cdf_mix]
    rfl
  let E := (C.mix D a).isClassical_cdf.ofMeasure ⟨μ, hprob⟩ hμ
  have he : E = C.mix D a :=
    cdf_injective ((C.mix D a).isClassical_cdf.cdf_ofMeasure ⟨μ, hprob⟩ hμ)
  rw [← he]
  rfl

/-- Integrating against a mixture averages the two integrals with the same weights. -/
theorem integral_mix {d : ℕ} (C D : Copula d) (a : I) {f : (Fin d → I) → ℝ}
    (hf : Continuous f) :
    (∫ x, f x ∂(C.mix D a).toMeasure) =
      (a : ℝ) * (∫ x, f x ∂C.toMeasure) + (1 - (a : ℝ)) * ∫ x, f x ∂D.toMeasure := by
  rw [toMeasure_mix, integral_add_measure
    ((integrable_continuous_cube _ hf).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_continuous_cube _ hf).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal a.property.1, ENNReal.toReal_ofReal (sub_nonneg.mpr a.property.2)]
  rfl

end ProbabilityTheory.Copula
