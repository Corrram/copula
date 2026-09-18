/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Spearman

/-! # Independence, concordance and countermonotonicity benchmarks -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem integral_unit_min_symm : (∫ t : I, min (t : ℝ) (1 - (t : ℝ))) = 1 / 4 := by
  rw [integral_unitInterval (fun t : ℝ => min t (1 - t))]
  have hc : Continuous (fun t : ℝ => min t (1 - t)) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (a := 0) (b := 1 / 2)) (hc.intervalIntegrable (a := 1 / 2) (b := 1))]
  have hleft : (∫ t in (0 : ℝ)..(1 / 2), min t (1 - t)) = ∫ t in (0 : ℝ)..(1 / 2), t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    exact min_eq_left (by linarith [ht.2])
  have hright : (∫ t in (1 / 2 : ℝ)..1, min t (1 - t)) = ∫ t in (1 / 2 : ℝ)..1, (1 - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    exact min_eq_right (by linarith [ht.1])
  rw [hleft, hright, intervalIntegral.integral_sub
    (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => t)
    (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _),
    integral_id, integral_id, intervalIntegral.integral_const]
  norm_num

theorem integral_unit_max_two_mul_sub_one :
    (∫ t : I, max 0 (2 * (t : ℝ) - 1)) = 1 / 4 := by
  have he : (fun t : I => max 0 (2 * (t : ℝ) - 1)) =
      fun t : I => (t : ℝ) - min (t : ℝ) (1 - (t : ℝ)) := by
    funext t
    rcases le_total (t : ℝ) (1 - (t : ℝ)) with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]; ring
    · rw [min_eq_right h, max_eq_right (by linarith)]; ring
  rw [he, integral_sub (integrable_continuous_unit volume (by fun_prop))
    (integrable_continuous_unit volume (by fun_prop)), integral_unit_id, integral_unit_min_symm]
  norm_num

@[simp] theorem blomqvistBeta_independence : (independence 2).blomqvistBeta = 0 := by
  norm_num [blomqvistBeta, cdf_independence, Fin.prod_univ_two, unitHalf]

@[simp] theorem blomqvistBeta_comonotonic : (comonotonic 2).blomqvistBeta = 1 := by
  rw [blomqvistBeta, cdf_comonotonic_two]
  norm_num [unitHalf]

@[simp] theorem blomqvistBeta_countermonotonic : countermonotonic.blomqvistBeta = -1 := by
  norm_num [blomqvistBeta, cdf_countermonotonic, unitHalf]

@[simp] theorem kendallTau_independence : (independence 2).kendallTau = 0 := by
  unfold kendallTau
  simp only [cdf_independence, Fin.prod_univ_two]
  rw [integral_independence_mul, integral_unit_id]
  norm_num

@[simp] theorem kendallTau_comonotonic : (comonotonic 2).kendallTau = 1 := by
  rw [kendallTau, integral_comonotonic _ (comonotonic 2).continuous_cdf.measurable]
  simp only [cdf_comonotonic_two, min_self]
  rw [integral_unit_id]
  norm_num

@[simp] theorem kendallTau_countermonotonic : countermonotonic.kendallTau = -1 := by
  rw [kendallTau, integral_countermonotonic _ countermonotonic.continuous_cdf.measurable]
  simp [unitInterval.coe_symm_eq]

@[simp] theorem spearmanFootrule_independence : (independence 2).spearmanFootrule = 0 := by
  unfold spearmanFootrule
  simp only [cdf_independence, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    ← sq]
  rw [integral_unit_pow]
  norm_num

@[simp] theorem spearmanFootrule_comonotonic : (comonotonic 2).spearmanFootrule = 1 := by
  unfold spearmanFootrule
  simp only [cdf_comonotonic_two, Matrix.cons_val_zero, Matrix.cons_val_one, min_self]
  rw [integral_unit_id]
  norm_num

@[simp] theorem spearmanFootrule_countermonotonic : countermonotonic.spearmanFootrule = -1 / 2 := by
  unfold spearmanFootrule
  simp only [cdf_countermonotonic, Matrix.cons_val_zero, Matrix.cons_val_one, ← two_mul]
  rw [integral_unit_max_two_mul_sub_one]
  norm_num

@[simp] theorem giniGamma_independence : (independence 2).giniGamma = 0 := by
  have hd : (∫ t : I, (independence 2).cdf ![t, t]) = 1 / 3 := by
    have h := spearmanFootrule_independence
    unfold spearmanFootrule at h
    linarith
  have he : (fun t : I => (independence 2).cdf ![t, unitInterval.symm t]) =
      fun t : I => (t : ℝ) - (t : ℝ) ^ 2 := by
    funext t
    simp [cdf_independence, Fin.prod_univ_two, unitInterval.coe_symm_eq]
    ring
  rw [giniGamma, hd, he, integral_sub (integrable_continuous_unit volume (by fun_prop))
    (integrable_continuous_unit volume (by fun_prop)), integral_unit_id, integral_unit_pow]
  norm_num

@[simp] theorem giniGamma_comonotonic : (comonotonic 2).giniGamma = 1 := by
  unfold giniGamma
  simp only [cdf_comonotonic_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    unitInterval.coe_symm_eq, min_self]
  rw [integral_unit_id, integral_unit_min_symm]
  norm_num

@[simp] theorem giniGamma_countermonotonic : countermonotonic.giniGamma = -1 := by
  have hd : (∫ t : I, countermonotonic.cdf ![t, t]) = 1 / 4 := by
    have h := spearmanFootrule_countermonotonic
    unfold spearmanFootrule at h
    linarith
  rw [giniGamma, hd]
  simp [unitInterval.coe_symm_eq]
  norm_num

theorem spearmanFootrule_mem_Icc (C : Copula 2) : C.spearmanFootrule ∈ Icc (-1 / 2) 1 := by
  have hl := spearmanFootrule_mono C.cdf_countermonotonic_le
  have hu := spearmanFootrule_mono C.cdf_le_comonotonic
  simpa using And.intro hl hu

theorem giniGamma_mem_Icc (C : Copula 2) : C.giniGamma ∈ Icc (-1) 1 := by
  have hl := giniGamma_mono C.cdf_countermonotonic_le
  have hu := giniGamma_mono C.cdf_le_comonotonic
  simpa using And.intro hl hu

end ProbabilityTheory.Copula
