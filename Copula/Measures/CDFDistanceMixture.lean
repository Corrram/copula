/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Measures.CDFDistance
import Copula.Rank.MixtureMeasure

/-! # Dilution by independence

For the mixture `a C + (1 - a) Π` the deviation from independence scales by `a`, so `σ`
scales by `a`, `Φ²` and `R` by `a²`. Hoeffding's `D` and Blum–Kiefer–Rosenblatt `R` have
different mixture laws because their integrating measures differ; the identities below
distinguish the two definitions even when they happen to agree on a particular parametric
family.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem cdfDeviation_mix_independence (C : Copula 2) (a : I) (x : Fin 2 → I) :
    (C.mix (independence 2) a).cdfDeviation x = (a : ℝ) * C.cdfDeviation x := by
  simp only [cdfDeviation, cdf_mix, cdf_independence, Fin.prod_univ_two]
  ring

theorem blumKieferRosenblattR_mix_independence (C : Copula 2) (a : I) :
    (C.mix (independence 2) a).blumKieferRosenblattR = (a : ℝ) ^ 2 * C.blumKieferRosenblattR := by
  simp only [blumKieferRosenblattR, cdfDeviation_mix_independence, mul_pow, integral_const_mul]

theorem hoeffdingD_mix_independence (C : Copula 2) (a : I) :
    (C.mix (independence 2) a).hoeffdingD =
      (a : ℝ) ^ 3 * C.hoeffdingD + (a : ℝ) ^ 2 * (1 - (a : ℝ)) * C.blumKieferRosenblattR := by
  simp only [hoeffdingD, cdfDeviation_mix_independence, mul_pow]
  rw [integral_mix C (independence 2) a (f := fun x => (a : ℝ) ^ 2 * C.cdfDeviation x ^ 2)
    (continuous_const.mul (C.continuous_cdfDeviation.pow 2))]
  simp only [integral_const_mul, blumKieferRosenblattR]
  ring

/-- `σ(a C + (1 - a) Π) = a σ(C)`. -/
theorem schweizerWolff_mix_independence (C : Copula 2) (a : I) :
    (C.mix (independence 2) a).schweizerWolff = (a : ℝ) * C.schweizerWolff := by
  simp only [schweizerWolff_eq_integral_abs_cdfDeviation, cdfDeviation_mix_independence, abs_mul,
    abs_of_nonneg a.property.1, integral_const_mul]
  ring

/-- `Φ²(a C + (1 - a) Π) = a² Φ²(C)`. -/
theorem hoeffdingPhiSq_mix_independence (C : Copula 2) (a : I) :
    (C.mix (independence 2) a).hoeffdingPhiSq = (a : ℝ) ^ 2 * C.hoeffdingPhiSq := by
  rw [hoeffdingPhiSq_eq_ninety_mul_blumKieferRosenblattR,
    hoeffdingPhiSq_eq_ninety_mul_blumKieferRosenblattR, blumKieferRosenblattR_mix_independence]
  ring

theorem distanceCorrelation_mix_independence (C : Copula 2) (a : I) :
    (C.mix (independence 2) a).distanceCorrelation = (a : ℝ) * C.distanceCorrelation := by
  unfold distanceCorrelation
  rw [hoeffdingPhiSq_mix_independence, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq a.property.1]

end ProbabilityTheory.Copula
