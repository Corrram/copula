/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Measures.Hoeffding
import Copula.Measures.SchweizerWolff
import Copula.Rank.ConditionalDistance
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Dependence coefficients from CDF discrepancies

All coefficients here are functionals of the deviation `C(u,v) - u v` of a bivariate copula
from independence (`cdfDeviation`).

* Hoeffding's `D = ∫ (C - Π)² dC` integrates the squared discrepancy against the copula itself;
  `hoeffdingDNormalized = 30 D` takes the value one at the Fréchet–Hoeffding bounds.
* The Blum–Kiefer–Rosenblatt coefficient `R = ∫ (C - Π)² dΠ` integrates against independent
  uniform coordinates; `90 R` is Hoeffding's `Φ²` (`hoeffdingPhiSq`, see
  `hoeffdingPhiSq_eq_ninety_mul_blumKieferRosenblattR`).
* For copulas (which always have atomless margins) the Bergsma–Dassios sign covariance `τ*`
  has the CDF representation `12 D + 24 R`, which is used as its definition here.
* Distance correlation of the two uniform coordinates is `√Φ²`.

The Schweizer–Wolff `σ` (`schweizerWolff`) and Hoeffding's `Φ²` (`hoeffdingPhiSq`) are defined
in `Copula.Measures.SchweizerWolff` and `Copula.Measures.Hoeffding`; here they are rewritten in
terms of `cdfDeviation`. References: Nelsen, *An Introduction to Copulas*, 2nd ed., §5.3;
Blum, Kiefer and Rosenblatt (1961); Bergsma and Dassios (2014). No equivalence to finite-sample
estimators is asserted.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The difference between a bivariate copula CDF and the product CDF. -/
noncomputable def cdfDeviation (C : Copula 2) (x : Fin 2 → I) : ℝ :=
  C.cdf x - (x 0 : ℝ) * (x 1 : ℝ)

theorem cdfDeviation_apply (C : Copula 2) (x : Fin 2 → I) :
    C.cdfDeviation x = C.cdf x - (x 0 : ℝ) * (x 1 : ℝ) := rfl

theorem cdfDeviation_two (C : Copula 2) (u v : I) :
    C.cdfDeviation ![u, v] = C.cdf ![u, v] - (u : ℝ) * v := rfl

theorem continuous_cdfDeviation (C : Copula 2) : Continuous C.cdfDeviation :=
  C.continuous_cdf.sub (by fun_prop)

theorem integrable_cdfDeviation_sq (C : Copula 2) (μ : Measure (Fin 2 → I))
    [IsFiniteMeasure μ] : Integrable (fun x => C.cdfDeviation x ^ 2) μ :=
  integrable_continuous_cube μ (C.continuous_cdfDeviation.pow 2)

theorem integrable_abs_cdfDeviation (C : Copula 2) (μ : Measure (Fin 2 → I))
    [IsFiniteMeasure μ] : Integrable (fun x => |C.cdfDeviation x|) μ :=
  integrable_continuous_cube μ C.continuous_cdfDeviation.abs

@[simp] theorem cdfDeviation_independence (x : Fin 2 → I) :
    (independence 2).cdfDeviation x = 0 := by
  simp [cdfDeviation, cdf_independence, Fin.prod_univ_two]

/-- Unscaled population Hoeffding `D = ∫ (C - Π)² dC`. -/
noncomputable def hoeffdingD (C : Copula 2) : ℝ :=
  ∫ x, C.cdfDeviation x ^ 2 ∂C.toMeasure

/-- Hoeffding's coefficient scaled to take value one at the monotone extremes. -/
noncomputable def hoeffdingDNormalized (C : Copula 2) : ℝ := 30 * C.hoeffdingD

/-- Unscaled population Blum–Kiefer–Rosenblatt `R = ∫ (C - Π)² dΠ`. -/
noncomputable def blumKieferRosenblattR (C : Copula 2) : ℝ :=
  ∫ x, C.cdfDeviation x ^ 2 ∂(independence 2).toMeasure

/-- Bergsma–Dassios sign covariance in its atomless-marginal CDF representation.
The unscaled convention has value `2/3` at both monotone extremes. -/
noncomputable def bergsmaDassiosTauStar (C : Copula 2) : ℝ :=
  12 * C.hoeffdingD + 24 * C.blumKieferRosenblattR

/-- Distance correlation of the two uniform copula coordinates, `√Φ²`.
This is rank-transformed distance correlation, not distance correlation of
arbitrary original margins. -/
noncomputable def distanceCorrelation (C : Copula 2) : ℝ :=
  Real.sqrt C.hoeffdingPhiSq

/-- Hoeffding's `Φ²` is the normalized Blum–Kiefer–Rosenblatt coefficient `90 R`. -/
theorem hoeffdingPhiSq_eq_ninety_mul_blumKieferRosenblattR (C : Copula 2) :
    C.hoeffdingPhiSq = 90 * C.blumKieferRosenblattR := rfl

/-- The Schweizer–Wolff `σ` in terms of `cdfDeviation`. -/
theorem schweizerWolff_eq_integral_abs_cdfDeviation (C : Copula 2) :
    C.schweizerWolff = 12 * ∫ x, |C.cdfDeviation x| ∂(independence 2).toMeasure := rfl

theorem hoeffdingD_nonneg (C : Copula 2) : 0 ≤ C.hoeffdingD :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem blumKieferRosenblattR_nonneg (C : Copula 2) : 0 ≤ C.blumKieferRosenblattR :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem bergsmaDassiosTauStar_nonneg (C : Copula 2) : 0 ≤ C.bergsmaDassiosTauStar :=
  add_nonneg (mul_nonneg (by norm_num) C.hoeffdingD_nonneg)
    (mul_nonneg (by norm_num) C.blumKieferRosenblattR_nonneg)

theorem distanceCorrelation_nonneg (C : Copula 2) : 0 ≤ C.distanceCorrelation :=
  Real.sqrt_nonneg _

theorem distanceCorrelation_sq (C : Copula 2) :
    C.distanceCorrelation ^ 2 = C.hoeffdingPhiSq :=
  Real.sq_sqrt C.hoeffdingPhiSq_nonneg

@[simp] theorem hoeffdingD_independence : (independence 2).hoeffdingD = 0 := by
  simp [hoeffdingD]

@[simp] theorem blumKieferRosenblattR_independence :
    (independence 2).blumKieferRosenblattR = 0 := by simp [blumKieferRosenblattR]

@[simp] theorem bergsmaDassiosTauStar_independence :
    (independence 2).bergsmaDassiosTauStar = 0 := by simp [bergsmaDassiosTauStar]

@[simp] theorem distanceCorrelation_independence :
    (independence 2).distanceCorrelation = 0 := by simp [distanceCorrelation]

/-- Integrals against the bivariate independence copula are iterated Lebesgue integrals,
with the first coordinate outside. -/
theorem integral_independence_two (f : (Fin 2 → I) → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂(independence 2).toMeasure) = ∫ u : I, ∫ v : I, f ![u, v] := by
  rw [Copula.toMeasure_independence]
  have hm := ((volume_preserving_finTwoArrow I).symm MeasurableEquiv.finTwoArrow).integral_comp
    MeasurableEquiv.finTwoArrow.symm.measurableEmbedding f
  have hi : Integrable (fun p : I × I => f ![p.1, p.2]) ((volume : Measure I).prod volume) :=
    (hf.comp (by fun_prop)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ x : Fin 2 → I, f x) = _
  rw [← hm]
  exact integral_prod _ hi

/-- The uniform squared CDF discrepancy detects independence, including for singular
copulas. -/
theorem blumKieferRosenblattR_eq_zero_iff (C : Copula 2) :
    C.blumKieferRosenblattR = 0 ↔ C = independence 2 := by
  rw [← C.hoeffdingPhiSq_eq_zero_iff, hoeffdingPhiSq_eq_ninety_mul_blumKieferRosenblattR]
  constructor
  · intro h; rw [h, mul_zero]
  · intro h; linarith

theorem bergsmaDassiosTauStar_eq_zero_iff (C : Copula 2) :
    C.bergsmaDassiosTauStar = 0 ↔ C = independence 2 := by
  constructor
  · intro h
    apply C.blumKieferRosenblattR_eq_zero_iff.mp
    unfold bergsmaDassiosTauStar at h
    nlinarith [C.hoeffdingD_nonneg, C.blumKieferRosenblattR_nonneg]
  · rintro rfl
    exact bergsmaDassiosTauStar_independence

theorem distanceCorrelation_eq_zero_iff (C : Copula 2) :
    C.distanceCorrelation = 0 ↔ C = independence 2 := by
  rw [distanceCorrelation, Real.sqrt_eq_zero C.hoeffdingPhiSq_nonneg, hoeffdingPhiSq_eq_zero_iff]

end ProbabilityTheory.Copula
