/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Symmetry
import Copula.Rank.Mixture

/-! # Symmetry identities for population concordance coefficients -/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem integral_reflect {d : ℕ} (C : Copula d) (s : Finset (Fin d))
    (f : (Fin d → I) → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂(C.reflect s).toMeasure) = ∫ x, f (reflectPoint s x) ∂C.toMeasure := by
  rw [toMeasure_reflect]
  exact integral_map (measurable_reflectPoint s).aemeasurable hf.aestronglyMeasurable

theorem integral_transpose (C : Copula 2) (f : (Fin 2 → I) → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂C.transpose.toMeasure) = ∫ x, f ![x 1, x 0] ∂C.toMeasure := by
  rw [transpose, toMeasure_reindex]
  have hm : Measurable (fun x : Fin 2 → I => fun i => x (![1, 0] i)) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]
  congr 1
  funext x
  congr 1
  ext i; fin_cases i <;> rfl

@[simp] theorem spearmanRho_transpose (C : Copula 2) : C.transpose.spearmanRho = C.spearmanRho := by
  unfold spearmanRho
  rw [C.integral_transpose _ (by fun_prop)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_comm]

@[simp] theorem kendallTau_transpose (C : Copula 2) : C.transpose.kendallTau = C.kendallTau := by
  unfold kendallTau
  rw [C.integral_transpose _ C.transpose.continuous_cdf.measurable]
  simp only [cdf_transpose]
  have he (x : Fin 2 → I) : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
  simp only [he]

@[simp] theorem spearmanFootrule_transpose (C : Copula 2) :
    C.transpose.spearmanFootrule = C.spearmanFootrule := by simp [spearmanFootrule]

@[simp] theorem blomqvistBeta_transpose (C : Copula 2) :
    C.transpose.blomqvistBeta = C.blomqvistBeta := by simp [blomqvistBeta]

@[simp] theorem giniGamma_transpose (C : Copula 2) : C.transpose.giniGamma = C.giniGamma := by
  unfold giniGamma
  simp only [cdf_transpose]
  have hi := unitInterval.measurePreserving_symm.integral_comp
    unitInterval.symmMeasurableEquiv.measurableEmbedding (fun t : I => C.cdf ![t, unitInterval.symm t])
  simpa only [unitInterval.symm_symm] using congrArg
    (fun z : ℝ => 4 * ((∫ t : I, C.cdf ![t, t]) + z) - 2) hi

theorem spearmanRho_reflect_first (C : Copula 2) :
    (C.reflect {0}).spearmanRho = -C.spearmanRho := by
  unfold spearmanRho
  rw [C.integral_reflect _ _ (by fun_prop)]
  simp only [reflectPoint, Finset.mem_singleton, ite_true, show (1 : Fin 2) ≠ 0 by decide,
    ite_false, unitInterval.coe_symm_eq]
  have he : (fun x : Fin 2 → I => (1 - (x 0 : ℝ)) * (x 1 : ℝ)) =
      fun x => (x 1 : ℝ) - (x 0 : ℝ) * (x 1 : ℝ) := by funext x; ring
  rw [he, integral_sub (integrable_continuous_cube C.toMeasure (by fun_prop))
    (integrable_continuous_cube C.toMeasure (by fun_prop)), C.integral_coe_eval]
  ring

theorem kendallTau_reflect_first (C : Copula 2) :
    (C.reflect {0}).kendallTau = -C.kendallTau := by
  unfold kendallTau
  rw [C.integral_reflect _ _ (C.reflect {0}).continuous_cdf.measurable]
  have he (x : Fin 2 → I) : (C.reflect {0}).cdf (reflectPoint {0} x) =
      (x 1 : ℝ) - C.cdf x := by
    have hx : reflectPoint {0} x = ![unitInterval.symm (x 0), x 1] := by
      ext i; fin_cases i <;> simp [reflectPoint]
    rw [hx, cdf_reflect_first, unitInterval.symm_symm]
    have he : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
    rw [he]
  simp_rw [he]
  rw [integral_sub (integrable_continuous_cube C.toMeasure (by fun_prop))
    (C.integrable_cdf C.toMeasure), C.integral_coe_eval]
  ring

theorem blomqvistBeta_reflect_first (C : Copula 2) :
    (C.reflect {0}).blomqvistBeta = -C.blomqvistBeta := by
  have he : unitInterval.symm unitHalf = unitHalf := by
    apply Subtype.ext
    norm_num [unitHalf, unitInterval.coe_symm_eq]
  simp only [blomqvistBeta]
  rw [cdf_reflect_first, he]
  change 4 * (1 / 2 - C.cdf ![unitHalf, unitHalf]) - 1 =
    -(4 * C.cdf ![unitHalf, unitHalf] - 1)
  ring

theorem spearmanRho_reflect_second (C : Copula 2) :
    (C.reflect {1}).spearmanRho = -C.spearmanRho := by
  have h := C.transpose.spearmanRho_reflect_first
  rw [← spearmanRho_transpose (C.transpose.reflect {0}), transpose_reflect_first,
    transpose_transpose, spearmanRho_transpose] at h
  exact h

theorem kendallTau_reflect_second (C : Copula 2) :
    (C.reflect {1}).kendallTau = -C.kendallTau := by
  have h := C.transpose.kendallTau_reflect_first
  rw [← kendallTau_transpose (C.transpose.reflect {0}), transpose_reflect_first,
    transpose_transpose, kendallTau_transpose] at h
  exact h

theorem blomqvistBeta_reflect_second (C : Copula 2) :
    (C.reflect {1}).blomqvistBeta = -C.blomqvistBeta := by
  have h := C.transpose.blomqvistBeta_reflect_first
  rw [← blomqvistBeta_transpose (C.transpose.reflect {0}), transpose_reflect_first,
    transpose_transpose, blomqvistBeta_transpose] at h
  exact h

theorem giniGamma_reflect_first (C : Copula 2) :
    (C.reflect {0}).giniGamma = -C.giniGamma := by
  have hd := unitInterval.measurePreserving_symm.integral_comp
    unitInterval.symmMeasurableEquiv.measurableEmbedding (fun t : I => C.cdf ![t, t])
  have ha := unitInterval.measurePreserving_symm.integral_comp
    unitInterval.symmMeasurableEquiv.measurableEmbedding (fun t : I => C.cdf ![t, unitInterval.symm t])
  simp only [unitInterval.symm_symm] at ha
  unfold giniGamma
  simp only [cdf_reflect_first, unitInterval.coe_symm_eq]
  rw [integral_sub, integral_sub, integral_sub, integral_unit_id, hd, ha]
  · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  all_goals exact integrable_continuous_unit volume (by fun_prop)

theorem giniGamma_reflect_second (C : Copula 2) :
    (C.reflect {1}).giniGamma = -C.giniGamma := by
  have h := C.transpose.giniGamma_reflect_first
  rw [← giniGamma_transpose (C.transpose.reflect {0}), transpose_reflect_first,
    transpose_transpose, giniGamma_transpose] at h
  exact h

@[simp] theorem spearmanRho_survivalCopula (C : Copula 2) :
    C.survivalCopula.spearmanRho = C.spearmanRho := by
  rw [← reflect_first_second, spearmanRho_reflect_second, spearmanRho_reflect_first, neg_neg]

@[simp] theorem kendallTau_survivalCopula (C : Copula 2) :
    C.survivalCopula.kendallTau = C.kendallTau := by
  rw [← reflect_first_second, kendallTau_reflect_second, kendallTau_reflect_first, neg_neg]

@[simp] theorem blomqvistBeta_survivalCopula (C : Copula 2) :
    C.survivalCopula.blomqvistBeta = C.blomqvistBeta := by
  rw [← reflect_first_second, blomqvistBeta_reflect_second, blomqvistBeta_reflect_first, neg_neg]

@[simp] theorem giniGamma_survivalCopula (C : Copula 2) :
    C.survivalCopula.giniGamma = C.giniGamma := by
  rw [← reflect_first_second, giniGamma_reflect_second, giniGamma_reflect_first, neg_neg]

@[simp] theorem spearmanFootrule_survivalCopula (C : Copula 2) :
    C.survivalCopula.spearmanFootrule = C.spearmanFootrule := by
  have hd := unitInterval.measurePreserving_symm.integral_comp
    unitInterval.symmMeasurableEquiv.measurableEmbedding (fun t : I => C.cdf ![t, t])
  unfold spearmanFootrule
  simp only [cdf_survivalCopula]
  rw [integral_add, integral_sub, integral_add, integral_unit_id, hd]
  · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  all_goals exact integrable_continuous_unit volume (by fun_prop)

end ProbabilityTheory.Copula
