/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Measures.CDFDistanceSymmetry
import Copula.Rank.FGMChatterjee

/-! # Benchmarks for CDF discrepancy coefficients

The singular Fréchet–Hoeffding bounds `M`, `W` and the absolutely continuous FGM family check
the normalizations of Hoeffding's `D`, Blum–Kiefer–Rosenblatt `R`, Hoeffding's `Φ²`,
Bergsma–Dassios `τ*` and distance correlation. In particular `Φ²(M) = Φ²(W) = 1`
(Nelsen, *An Introduction to Copulas*, 2nd ed., §5.3.1).
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem integral_unit_bridge_sq (u : I) :
    (∫ v : I, (min (u : ℝ) (v : ℝ) - (u : ℝ) * (v : ℝ)) ^ 2) =
      (u : ℝ) ^ 2 * (1 - (u : ℝ)) ^ 2 / 3 := by
  rw [integral_unitInterval (fun v : ℝ => (min (u : ℝ) v - (u : ℝ) * v) ^ 2)]
  have hc : Continuous (fun v : ℝ => (min (u : ℝ) v - (u : ℝ) * v) ^ 2) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (a := 0) (b := (u : ℝ)))
    (hc.intervalIntegrable (a := (u : ℝ)) (b := 1))]
  have hL : (∫ v in (0 : ℝ)..(u : ℝ), (min (u : ℝ) v - (u : ℝ) * v) ^ 2) =
      (1 - (u : ℝ)) ^ 2 * ∫ v in (0 : ℝ)..(u : ℝ), v ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le u.property.1] at hv
    change (min (u : ℝ) v - (u : ℝ) * v) ^ 2 = (1 - (u : ℝ)) ^ 2 * v ^ 2
    rw [min_eq_right hv.2]
    ring
  have hR : (∫ v in (u : ℝ)..1, (min (u : ℝ) v - (u : ℝ) * v) ^ 2) =
      (u : ℝ) ^ 2 * ∫ v in (u : ℝ)..1, (1 - 2 * v + v ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le u.property.2] at hv
    change (min (u : ℝ) v - (u : ℝ) * v) ^ 2 = (u : ℝ) ^ 2 * (1 - 2 * v + v ^ 2)
    rw [min_eq_left hv.1]
    ring
  rw [hL, hR, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, integral_id,
    integral_pow, integral_pow]
  · ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

@[simp] theorem hoeffdingD_comonotonic : (comonotonic 2).hoeffdingD = 1 / 30 := by
  rw [hoeffdingD, integral_comonotonic (fun x => (comonotonic 2).cdfDeviation x ^ 2)
    ((comonotonic 2).continuous_cdfDeviation.pow 2).measurable]
  simp only [cdfDeviation, cdf_comonotonic_two, min_self]
  convert integral_unit_sq_mul_one_sub_sq using 1
  congr 1
  funext u
  ring

@[simp] theorem hoeffdingD_countermonotonic : countermonotonic.hoeffdingD = 1 / 30 := by
  rw [hoeffdingD, integral_countermonotonic (fun x => countermonotonic.cdfDeviation x ^ 2)
    (countermonotonic.continuous_cdfDeviation.pow 2).measurable]
  simp only [cdfDeviation, cdf_countermonotonic, Matrix.cons_val_zero, Matrix.cons_val_one,
    unitInterval.coe_symm_eq]
  have he : (fun u : I => (max 0 ((u : ℝ) + (1 - (u : ℝ)) - 1) -
      (u : ℝ) * (1 - (u : ℝ))) ^ 2) =
      fun u : I => (u : ℝ) ^ 2 * (1 - (u : ℝ)) ^ 2 := by
    funext u
    rw [show (u : ℝ) + (1 - (u : ℝ)) - 1 = 0 by ring]
    simp [mul_pow]
  rw [he, integral_unit_sq_mul_one_sub_sq]

@[simp] theorem blumKieferRosenblattR_comonotonic :
    (comonotonic 2).blumKieferRosenblattR = 1 / 90 := by
  rw [blumKieferRosenblattR, integral_independence_two (fun x => (comonotonic 2).cdfDeviation x ^ 2)
    ((comonotonic 2).continuous_cdfDeviation.pow 2)]
  simp only [cdfDeviation, cdf_comonotonic_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [integral_unit_bridge_sq]
  rw [integral_div, integral_unit_sq_mul_one_sub_sq]
  norm_num

theorem cdfDeviation_fgm (θ : ℝ) (hθ : |θ| ≤ 1) (x : Fin 2 → I) :
    (fgm θ hθ).cdfDeviation x =
      θ * ((x 0 : ℝ) * (1 - (x 0 : ℝ))) * ((x 1 : ℝ) * (1 - (x 1 : ℝ))) := by
  simp only [cdfDeviation, cdf_fgm, fgmCDF]
  ring

theorem blumKieferRosenblattR_fgm (θ : ℝ) (hθ : |θ| ≤ 1) :
    (fgm θ hθ).blumKieferRosenblattR = θ ^ 2 / 900 := by
  unfold blumKieferRosenblattR
  have he : (fun x : Fin 2 → I => (fgm θ hθ).cdfDeviation x ^ 2) = fun x =>
      θ ^ 2 * (((x 0 : ℝ) ^ 2 * (1 - (x 0 : ℝ)) ^ 2) *
        ((x 1 : ℝ) ^ 2 * (1 - (x 1 : ℝ)) ^ 2)) := by
    funext x
    rw [cdfDeviation_fgm]
    ring
  rw [he, integral_const_mul,
    integral_independence_mul (fun u : I => (u : ℝ) ^ 2 * (1 - (u : ℝ)) ^ 2)
      (fun u : I => (u : ℝ) ^ 2 * (1 - (u : ℝ)) ^ 2), integral_unit_sq_mul_one_sub_sq]
  ring

/-- Hoeffding's `Φ²` of the upper Fréchet–Hoeffding bound is one. -/
@[simp] theorem hoeffdingPhiSq_comonotonic : (comonotonic 2).hoeffdingPhiSq = 1 := by
  rw [hoeffdingPhiSq_eq_ninety_mul_blumKieferRosenblattR, blumKieferRosenblattR_comonotonic]
  norm_num

@[simp] theorem distanceCorrelation_comonotonic : (comonotonic 2).distanceCorrelation = 1 := by
  simp [distanceCorrelation]

@[simp] theorem bergsmaDassiosTauStar_comonotonic :
    (comonotonic 2).bergsmaDassiosTauStar = 2 / 3 := by
  norm_num [bergsmaDassiosTauStar]

@[simp] theorem blumKieferRosenblattR_countermonotonic :
    countermonotonic.blumKieferRosenblattR = 1 / 90 := by
  rw [← reflect_comonotonic_eq_countermonotonic, blumKieferRosenblattR_reflect_second,
    blumKieferRosenblattR_comonotonic]

/-- Hoeffding's `Φ²` of the lower Fréchet–Hoeffding bound is one. -/
@[simp] theorem hoeffdingPhiSq_countermonotonic : countermonotonic.hoeffdingPhiSq = 1 := by
  rw [hoeffdingPhiSq_eq_ninety_mul_blumKieferRosenblattR, blumKieferRosenblattR_countermonotonic]
  norm_num

@[simp] theorem distanceCorrelation_countermonotonic : countermonotonic.distanceCorrelation = 1 := by
  simp [distanceCorrelation]

@[simp] theorem bergsmaDassiosTauStar_countermonotonic :
    countermonotonic.bergsmaDassiosTauStar = 2 / 3 := by
  norm_num [bergsmaDassiosTauStar]

@[simp] theorem hoeffdingDNormalized_independence : (independence 2).hoeffdingDNormalized = 0 := by
  simp [hoeffdingDNormalized]

@[simp] theorem hoeffdingDNormalized_comonotonic : (comonotonic 2).hoeffdingDNormalized = 1 := by
  norm_num [hoeffdingDNormalized]

@[simp] theorem hoeffdingDNormalized_countermonotonic : countermonotonic.hoeffdingDNormalized = 1 := by
  norm_num [hoeffdingDNormalized]

end ProbabilityTheory.Copula
