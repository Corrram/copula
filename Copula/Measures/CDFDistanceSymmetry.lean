/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Measures.CDFDistance

/-! # Symmetries of the CDF discrepancy coefficients

The coefficients of `Copula.Measures.CDFDistance` (Hoeffding's `D`, Blum–Kiefer–Rosenblatt `R`,
Bergsma–Dassios `τ*`, distance correlation) as well as the Schweizer–Wolff `σ` and Hoeffding's
`Φ²` are invariant under transposition and under reflecting one coordinate (Nelsen,
*An Introduction to Copulas*, 2nd ed., §5.3: measures of dependence are invariant under
`(U,V) ↦ (U, 1 - V)`).
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem cdfDeviation_transpose (C : Copula 2) (u v : I) :
    C.transpose.cdfDeviation ![u, v] = C.cdfDeviation ![v, u] := by
  simp only [cdfDeviation, cdf_transpose, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem cdfDeviation_reflect_second (C : Copula 2) (u v : I) :
    (C.reflect {1}).cdfDeviation ![u, v] = -C.cdfDeviation ![u, unitInterval.symm v] := by
  simp only [cdfDeviation, cdf_reflect_second, Matrix.cons_val_zero, Matrix.cons_val_one,
    unitInterval.coe_symm_eq]
  ring

@[simp] theorem hoeffdingD_transpose (C : Copula 2) : C.transpose.hoeffdingD = C.hoeffdingD := by
  rw [hoeffdingD, C.integral_transpose (fun x => C.transpose.cdfDeviation x ^ 2)
    (C.transpose.continuous_cdfDeviation.pow 2).measurable]
  simp only [cdfDeviation_transpose]
  have he (x : Fin 2 → I) : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
  simp only [he, hoeffdingD]

@[simp] theorem blumKieferRosenblattR_transpose (C : Copula 2) :
    C.transpose.blumKieferRosenblattR = C.blumKieferRosenblattR := by
  have h := C.hoeffdingPhiSq_transpose
  rw [hoeffdingPhiSq_eq_ninety_mul_blumKieferRosenblattR,
    hoeffdingPhiSq_eq_ninety_mul_blumKieferRosenblattR] at h
  linarith

@[simp] theorem bergsmaDassiosTauStar_transpose (C : Copula 2) :
    C.transpose.bergsmaDassiosTauStar = C.bergsmaDassiosTauStar := by
  simp [bergsmaDassiosTauStar]

@[simp] theorem distanceCorrelation_transpose (C : Copula 2) :
    C.transpose.distanceCorrelation = C.distanceCorrelation := by
  simp [distanceCorrelation]

theorem hoeffdingD_reflect_second (C : Copula 2) :
    (C.reflect {1}).hoeffdingD = C.hoeffdingD := by
  rw [hoeffdingD, C.integral_reflect {1} (fun x => (C.reflect {1}).cdfDeviation x ^ 2)
    ((C.reflect {1}).continuous_cdfDeviation.pow 2).measurable]
  have he (x : Fin 2 → I) : reflectPoint {1} x = ![x 0, unitInterval.symm (x 1)] := by
    ext i
    fin_cases i <;> simp [reflectPoint]
  have hx (x : Fin 2 → I) : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
  simp only [he, cdfDeviation_reflect_second, unitInterval.symm_symm, neg_sq, hx, hoeffdingD]

theorem blumKieferRosenblattR_reflect_second (C : Copula 2) :
    (C.reflect {1}).blumKieferRosenblattR = C.blumKieferRosenblattR := by
  simp only [blumKieferRosenblattR]
  rw [integral_independence_two (fun x => (C.reflect {1}).cdfDeviation x ^ 2)
      ((C.reflect {1}).continuous_cdfDeviation.pow 2),
    integral_independence_two (fun x => C.cdfDeviation x ^ 2) (C.continuous_cdfDeviation.pow 2)]
  simp only [cdfDeviation_reflect_second, neg_sq]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  exact unitInterval.measurePreserving_symm.integral_comp
    unitInterval.symmMeasurableEquiv.measurableEmbedding (fun v => C.cdfDeviation ![u, v] ^ 2)

/-- The Schweizer–Wolff `σ` is invariant under reflecting the second coordinate. -/
theorem schweizerWolff_reflect_second (C : Copula 2) :
    (C.reflect {1}).schweizerWolff = C.schweizerWolff := by
  simp only [schweizerWolff_eq_integral_abs_cdfDeviation]
  rw [integral_independence_two (fun x => |(C.reflect {1}).cdfDeviation x|)
      (C.reflect {1}).continuous_cdfDeviation.abs,
    integral_independence_two (fun x => |C.cdfDeviation x|) C.continuous_cdfDeviation.abs]
  simp only [cdfDeviation_reflect_second, abs_neg]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  exact unitInterval.measurePreserving_symm.integral_comp
    unitInterval.symmMeasurableEquiv.measurableEmbedding (fun v => |C.cdfDeviation ![u, v]|)

/-- The Schweizer–Wolff `σ` is invariant under reflecting the first coordinate. -/
theorem schweizerWolff_reflect_first (C : Copula 2) :
    (C.reflect {0}).schweizerWolff = C.schweizerWolff := by
  rw [← schweizerWolff_transpose, transpose_reflect_first, schweizerWolff_reflect_second,
    schweizerWolff_transpose]

/-- Hoeffding's `Φ²` is invariant under reflecting the second coordinate. -/
theorem hoeffdingPhiSq_reflect_second (C : Copula 2) :
    (C.reflect {1}).hoeffdingPhiSq = C.hoeffdingPhiSq := by
  rw [hoeffdingPhiSq_eq_ninety_mul_blumKieferRosenblattR,
    hoeffdingPhiSq_eq_ninety_mul_blumKieferRosenblattR, blumKieferRosenblattR_reflect_second]

/-- Hoeffding's `Φ²` is invariant under reflecting the first coordinate. -/
theorem hoeffdingPhiSq_reflect_first (C : Copula 2) :
    (C.reflect {0}).hoeffdingPhiSq = C.hoeffdingPhiSq := by
  rw [← hoeffdingPhiSq_transpose, transpose_reflect_first, hoeffdingPhiSq_reflect_second,
    hoeffdingPhiSq_transpose]

theorem bergsmaDassiosTauStar_reflect_second (C : Copula 2) :
    (C.reflect {1}).bergsmaDassiosTauStar = C.bergsmaDassiosTauStar := by
  simp [bergsmaDassiosTauStar, hoeffdingD_reflect_second, blumKieferRosenblattR_reflect_second]

theorem distanceCorrelation_reflect_second (C : Copula 2) :
    (C.reflect {1}).distanceCorrelation = C.distanceCorrelation := by
  simp [distanceCorrelation, hoeffdingPhiSq_reflect_second]

end ProbabilityTheory.Copula
