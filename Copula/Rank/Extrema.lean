/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Support
import Copula.Diagonal
import Copula.Rank.Symmetry
import Copula.Rank.Benchmarks
import Copula.UnitInterval

/-! # Equality cases for population rank coefficients

Rho, tau and gamma attain their upper and lower bounds only at the
corresponding Fréchet copulas. Footrule attains its upper bound only at
comonotonicity; its lower bound characterizes the diagonal section instead.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem spearmanRho_eq_one_iff (C : Copula 2) :
    C.spearmanRho = 1 ↔ C = comonotonic 2 := by
  refine ⟨fun h => ?_, fun h => h ▸ spearmanRho_comonotonic⟩
  have hz : (∫ x, ((x 0 : ℝ) - x 1) ^ 2 ∂C.toMeasure) = 0 := by
    linarith [C.spearmanRho_eq_one_sub]
  have he := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ((x 0 : ℝ) - x 1))
    (integrable_continuous_cube C.toMeasure (by fun_prop))).1 hz
  apply C.eq_comonotonic_iff_ae_eval_eq.mpr
  filter_upwards [he] with x hx
  exact Subtype.ext (sub_eq_zero.mp (sq_eq_zero_iff.mp hx))

theorem spearmanRho_eq_neg_one_iff (C : Copula 2) :
    C.spearmanRho = -1 ↔ C = countermonotonic := by
  refine ⟨fun h => ?_, fun h => h ▸ spearmanRho_countermonotonic⟩
  have hz : (∫ x, ((x 0 : ℝ) + (x 1 : ℝ) - 1) ^ 2 ∂C.toMeasure) = 0 := by
    linarith [C.spearmanRho_eq_neg_one_add]
  have he := (integral_eq_zero_iff_of_nonneg (fun x =>
    sq_nonneg ((x 0 : ℝ) + (x 1 : ℝ) - 1))
    (integrable_continuous_cube C.toMeasure (by fun_prop))).1 hz
  apply C.eq_countermonotonic_iff_ae_add_eq_one.mpr
  filter_upwards [he] with x hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)

theorem kendallTau_eq_one_iff (C : Copula 2) :
    C.kendallTau = 1 ↔ C = comonotonic 2 := by
  refine ⟨fun h => ?_, fun h => h ▸ kendallTau_comonotonic⟩
  have hi : (∫ x, C.cdf x ∂C.toMeasure) = 1 / 2 := by
    unfold kendallTau at h
    linarith
  have he (i : Fin 2) : C.cdf =ᵐ[C.toMeasure] fun x => (x i : ℝ) := by
    apply (integral_eq_iff_of_ae_le (C.integrable_cdf C.toMeasure)
      (integrable_continuous_cube C.toMeasure (by fun_prop))
      (Filter.Eventually.of_forall fun x => C.cdf_le_coord x i)).1
    rw [hi, C.integral_coe_eval]
  apply C.eq_comonotonic_iff_ae_eval_eq.mpr
  filter_upwards [he 0, he 1] with x h0 h1
  exact Subtype.ext (h0.symm.trans h1)

theorem kendallTau_eq_neg_one_iff (C : Copula 2) :
    C.kendallTau = -1 ↔ C = countermonotonic := by
  refine ⟨fun h => ?_, fun h => h ▸ kendallTau_countermonotonic⟩
  have he : C.reflect {1} = comonotonic 2 :=
    (kendallTau_eq_one_iff _).1 (by rw [kendallTau_reflect_second, h]; norm_num)
  have hr := congrArg (fun D : Copula 2 => D.reflect {1}) he
  simpa only [reflect_reflect, reflect_comonotonic_eq_countermonotonic] using hr

theorem spearmanFootrule_eq_one_iff (C : Copula 2) :
    C.spearmanFootrule = 1 ↔ C = comonotonic 2 := by
  refine ⟨fun h => ?_, fun h => h ▸ spearmanFootrule_comonotonic⟩
  have he : (fun t : I => C.cdf ![t, t]) =ᵐ[volume] fun t => (t : ℝ) := by
    apply (integral_eq_iff_of_ae_le C.integrable_diagonal_cdf
      (integrable_continuous_unit volume continuous_subtype_val)
      (Filter.Eventually.of_forall fun t => C.cdf_le_coord ![t, t] 0)).1
    rw [integral_unit_id]
    unfold spearmanFootrule at h
    linarith
  have hf := Measure.eq_of_ae_eq he
    (C.continuous_cdf.comp (by fun_prop)) continuous_subtype_val
  exact C.diagonal_eq_id_iff.mp (congrFun hf)

theorem spearmanFootrule_eq_neg_half_iff (C : Copula 2) :
    C.spearmanFootrule = -1 / 2 ↔ ∀ t : I, C.diagonal t = max 0 (2 * (t : ℝ) - 1) := by
  constructor
  · intro h
    have he : (fun t : I => countermonotonic.cdf ![t, t]) =ᵐ[volume]
        fun t => C.cdf ![t, t] := by
      apply (integral_eq_iff_of_ae_le countermonotonic.integrable_diagonal_cdf
        C.integrable_diagonal_cdf
        (Filter.Eventually.of_forall fun t => C.cdf_countermonotonic_le ![t, t])).1
      have hw := spearmanFootrule_countermonotonic
      unfold spearmanFootrule at h hw
      linarith
    have hf := Measure.eq_of_ae_eq he
      (countermonotonic.continuous_cdf.comp (by fun_prop)) (C.continuous_cdf.comp (by fun_prop))
    intro t
    simpa [diagonal, cdf_countermonotonic, two_mul] using (congrFun hf t).symm
  · intro h
    have he : (fun t : I => C.cdf ![t, t]) = fun t : I => max 0 (2 * (t : ℝ) - 1) :=
      funext h
    rw [spearmanFootrule, he, integral_unit_max_two_mul_sub_one]
    norm_num

theorem giniGamma_eq_one_iff (C : Copula 2) :
    C.giniGamma = 1 ↔ C = comonotonic 2 := by
  refine ⟨fun h => ?_, fun h => h ▸ giniGamma_comonotonic⟩
  apply C.spearmanFootrule_eq_one_iff.mp
  have hd := C.spearmanFootrule_mem_Icc.2
  have ha := integral_mono C.integrable_antidiagonal_cdf
    (comonotonic 2).integrable_antidiagonal_cdf
    (fun t => C.cdf_le_comonotonic ![t, unitInterval.symm t])
  simp only [cdf_comonotonic_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    unitInterval.coe_symm_eq, integral_unit_min_symm] at ha
  unfold giniGamma at h
  unfold spearmanFootrule at hd ⊢
  linarith

theorem giniGamma_eq_neg_one_iff (C : Copula 2) :
    C.giniGamma = -1 ↔ C = countermonotonic := by
  refine ⟨fun h => ?_, fun h => h ▸ giniGamma_countermonotonic⟩
  have he : C.reflect {1} = comonotonic 2 :=
    (giniGamma_eq_one_iff _).1 (by rw [giniGamma_reflect_second, h]; norm_num)
  have hr := congrArg (fun D : Copula 2 => D.reflect {1}) he
  simpa only [reflect_reflect, reflect_comonotonic_eq_countermonotonic] using hr

theorem spearmanRho_lt_one_iff (C : Copula 2) :
    C.spearmanRho < 1 ↔ C ≠ comonotonic 2 := by
  rw [lt_iff_le_and_ne, and_iff_right C.spearmanRho_mem_Icc.2]
  exact not_congr C.spearmanRho_eq_one_iff

theorem neg_one_lt_spearmanRho_iff (C : Copula 2) :
    -1 < C.spearmanRho ↔ C ≠ countermonotonic := by
  rw [lt_iff_le_and_ne, and_iff_right C.spearmanRho_mem_Icc.1, ne_comm]
  exact not_congr C.spearmanRho_eq_neg_one_iff

theorem kendallTau_lt_one_iff (C : Copula 2) :
    C.kendallTau < 1 ↔ C ≠ comonotonic 2 := by
  rw [lt_iff_le_and_ne, and_iff_right C.kendallTau_mem_Icc.2]
  exact not_congr C.kendallTau_eq_one_iff

theorem neg_one_lt_kendallTau_iff (C : Copula 2) :
    -1 < C.kendallTau ↔ C ≠ countermonotonic := by
  rw [lt_iff_le_and_ne, and_iff_right C.kendallTau_mem_Icc.1, ne_comm]
  exact not_congr C.kendallTau_eq_neg_one_iff

theorem spearmanFootrule_lt_one_iff (C : Copula 2) :
    C.spearmanFootrule < 1 ↔ C ≠ comonotonic 2 := by
  rw [lt_iff_le_and_ne, and_iff_right C.spearmanFootrule_mem_Icc.2]
  exact not_congr C.spearmanFootrule_eq_one_iff

theorem giniGamma_lt_one_iff (C : Copula 2) :
    C.giniGamma < 1 ↔ C ≠ comonotonic 2 := by
  rw [lt_iff_le_and_ne, and_iff_right C.giniGamma_mem_Icc.2]
  exact not_congr C.giniGamma_eq_one_iff

theorem neg_one_lt_giniGamma_iff (C : Copula 2) :
    -1 < C.giniGamma ↔ C ≠ countermonotonic := by
  rw [lt_iff_le_and_ne, and_iff_right C.giniGamma_mem_Icc.1, ne_comm]
  exact not_congr C.giniGamma_eq_neg_one_iff

end ProbabilityTheory.Copula
