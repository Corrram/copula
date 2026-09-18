/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Order.Rank
import Copula.Rank.Mixture

/-! # The bivariate concordance function

The symmetric function `Q(C,D) = 4 ∫ C dD - 1` polarizes Kendall's tau.
Pairing with independence recovers one third of Spearman's rho, while the
two Fréchet bounds connect it with footrule and Gini's gamma.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The concordance function of two bivariate copulas. -/
noncomputable def concordanceQ (C D : Copula 2) : ℝ := 4 * (∫ x, C.cdf x ∂D.toMeasure) - 1

theorem concordanceQ_comm (C D : Copula 2) : C.concordanceQ D = D.concordanceQ C := by
  rw [concordanceQ, concordanceQ, integral_cdf_swap]

@[simp] theorem concordanceQ_self (C : Copula 2) : C.concordanceQ C = C.kendallTau := rfl

theorem concordanceQ_mem_Icc (C D : Copula 2) : C.concordanceQ D ∈ Icc (-1) 1 := by
  have hn : 0 ≤ ∫ x, C.cdf x ∂D.toMeasure := integral_nonneg C.cdf_nonneg
  have hu := integral_mono (C.integrable_cdf D.toMeasure)
    (integrable_continuous_cube D.toMeasure (show Continuous (fun x : Fin 2 → I => (x 0 : ℝ)) by
      fun_prop)) (fun x => C.cdf_le_coord x 0)
  rw [D.integral_coe_eval] at hu
  constructor <;> unfold concordanceQ <;> linarith

theorem LowerOrthantLE.concordanceQ_le_left {C D : Copula 2} (h : C.LowerOrthantLE D)
    (E : Copula 2) : C.concordanceQ E ≤ D.concordanceQ E := by
  have hi := integral_mono (C.integrable_cdf E.toMeasure) (D.integrable_cdf E.toMeasure) h
  unfold concordanceQ
  linarith

theorem LowerOrthantLE.concordanceQ_le_right {C D : Copula 2} (h : C.LowerOrthantLE D)
    (E : Copula 2) : E.concordanceQ C ≤ E.concordanceQ D := by
  simpa only [concordanceQ_comm] using h.concordanceQ_le_left E

theorem concordanceQ_independence (C : Copula 2) :
    C.concordanceQ (independence 2) = C.spearmanRho / 3 := by
  rw [concordanceQ, spearmanRho_eq_integral_cdf]
  ring

theorem concordanceQ_comonotonic (C : Copula 2) :
    C.concordanceQ (comonotonic 2) = (2 * C.spearmanFootrule + 1) / 3 := by
  rw [concordanceQ, integral_comonotonic _ C.continuous_cdf.measurable]
  have he (t : I) : (fun _ : Fin 2 => t) = ![t, t] := by ext i; fin_cases i <;> rfl
  simp_rw [he]
  unfold spearmanFootrule
  ring

theorem concordanceQ_countermonotonic (C : Copula 2) :
    C.concordanceQ countermonotonic = C.giniGamma - (2 * C.spearmanFootrule + 1) / 3 := by
  rw [concordanceQ, integral_countermonotonic _ C.continuous_cdf.measurable]
  unfold giniGamma spearmanFootrule
  ring

theorem giniGamma_eq_concordanceQ (C : Copula 2) :
    C.giniGamma = C.concordanceQ (comonotonic 2) + C.concordanceQ countermonotonic := by
  rw [concordanceQ_comonotonic, concordanceQ_countermonotonic]
  ring

@[simp] theorem concordanceQ_comonotonic_countermonotonic :
    (comonotonic 2).concordanceQ countermonotonic = 0 := by
  rw [concordanceQ_countermonotonic]
  norm_num

theorem concordanceQ_finiteMixture_left {n : ℕ} (C : Fin n → Copula 2) (w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) (D : Copula 2) :
    (finiteMixture C w hw hsum).concordanceQ D = ∑ j, w j * (C j).concordanceQ D := by
  simp only [concordanceQ, cdf_finiteMixture]
  rw [integral_finsetSum _ (fun j _ => ((C j).integrable_cdf D.toMeasure).const_mul (w j))]
  simp only [integral_const_mul]
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, hsum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem concordanceQ_finiteMixture_right {n : ℕ} (C : Fin n → Copula 2) (w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) (D : Copula 2) :
    D.concordanceQ (finiteMixture C w hw hsum) = ∑ j, w j * D.concordanceQ (C j) := by
  simpa only [concordanceQ_comm] using concordanceQ_finiteMixture_left C w hw hsum D

theorem concordanceQ_mix_left (C D E : Copula 2) (a : I) :
    (C.mix D a).concordanceQ E =
      (a : ℝ) * C.concordanceQ E + (1 - (a : ℝ)) * D.concordanceQ E := by
  simpa only [mix, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
    concordanceQ_finiteMixture_left ![C, D] ![(a : ℝ), 1 - (a : ℝ)] _ _ E

theorem concordanceQ_mix_right (C D E : Copula 2) (a : I) :
    C.concordanceQ (D.mix E a) =
      (a : ℝ) * C.concordanceQ D + (1 - (a : ℝ)) * C.concordanceQ E := by
  simpa only [concordanceQ_comm] using concordanceQ_mix_left D E C a

end ProbabilityTheory.Copula
