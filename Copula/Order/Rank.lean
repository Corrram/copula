/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Order.Orthant
import Copula.Dependence.Rank

/-! # Concordance order and rank coefficients -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The bivariate cross-concordance integral is symmetric. -/
theorem integral_cdf_swap (C D : Copula 2) :
    (∫ x, C.cdf x ∂D.toMeasure) = ∫ x, D.cdf x ∂C.toMeasure := by
  classical
  have hf : Integrable (fun p : (Fin 2 → I) × (Fin 2 → I) =>
      if p.2 ≤ p.1 then (1 : ℝ) else 0) (D.toMeasure.prod C.toMeasure) := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (measurable_const.ite (measurableSet_le measurable_snd measurable_fst)
        measurable_const).aestronglyMeasurable
    · split_ifs <;> norm_num
  have hc (x : Fin 2 → I) : C.cdf x =
      ∫ y, if y ≤ x then (1 : ℝ) else 0 ∂C.toMeasure := by
    symm
    simpa [Set.indicator, cdf] using
      integral_indicator_one (μ := C.toMeasure) (s := Iic x) measurableSet_Iic
  have hd (y : Fin 2 → I) :
      (∫ x, if y ≤ x then (1 : ℝ) else 0 ∂D.toMeasure) = D.survival y := by
    simpa [Set.indicator, survival] using
      integral_indicator_one (μ := D.toMeasure) (s := Ici y) measurableSet_Ici
  calc
    _ = ∫ x, ∫ y, if y ≤ x then (1 : ℝ) else 0 ∂C.toMeasure ∂D.toMeasure := by simp_rw [hc]
    _ = ∫ y, ∫ x, if y ≤ x then (1 : ℝ) else 0 ∂D.toMeasure ∂C.toMeasure :=
      integral_integral_swap hf
    _ = ∫ y, 1 - (y 0 : ℝ) - (y 1 : ℝ) + D.cdf y ∂C.toMeasure := by
      simp_rw [hd, survival_two]
    _ = _ := by
      rw [integral_add, integral_sub, integral_sub, C.integral_coe_eval, C.integral_coe_eval]
      · norm_num
      all_goals exact integrable_continuous_cube C.toMeasure (by fun_prop)

theorem LowerOrthantLE.kendallTau_le {C D : Copula 2} (h : C.LowerOrthantLE D) :
    C.kendallTau ≤ D.kendallTau := by
  have h₁ := integral_mono (C.integrable_cdf C.toMeasure) (D.integrable_cdf C.toMeasure) h
  have h₂ := integral_mono (C.integrable_cdf D.toMeasure) (D.integrable_cdf D.toMeasure) h
  rw [integral_cdf_swap D C] at h₁
  unfold kendallTau
  linarith

theorem LowerOrthantLE.spearmanRho_le {C D : Copula 2} (h : C.LowerOrthantLE D) :
    C.spearmanRho ≤ D.spearmanRho := spearmanRho_mono h

theorem LowerOrthantLE.spearmanFootrule_le {C D : Copula 2} (h : C.LowerOrthantLE D) :
    C.spearmanFootrule ≤ D.spearmanFootrule := spearmanFootrule_mono h

theorem LowerOrthantLE.giniGamma_le {C D : Copula 2} (h : C.LowerOrthantLE D) :
    C.giniGamma ≤ D.giniGamma := giniGamma_mono h

theorem LowerOrthantLE.blomqvistBeta_le {C D : Copula 2} (h : C.LowerOrthantLE D) :
    C.blomqvistBeta ≤ D.blomqvistBeta := blomqvistBeta_mono h

theorem isPQD_iff_lowerOrthantLE (C : Copula 2) :
    C.IsPQD ↔ (independence 2).LowerOrthantLE C := isPQD_iff_independence_le C

theorem lowerOrthantLE_countermonotonic (C : Copula 2) : countermonotonic.LowerOrthantLE C :=
  cdf_countermonotonic_le C

theorem lowerOrthantLE_comonotonic (C : Copula 2) : C.LowerOrthantLE (comonotonic 2) :=
  cdf_le_comonotonic C

theorem concordanceLE_countermonotonic (C : Copula 2) : countermonotonic.ConcordanceLE C :=
  (concordanceLE_iff_lowerOrthantLE _ _).2 (lowerOrthantLE_countermonotonic C)

theorem concordanceLE_comonotonic (C : Copula 2) : C.ConcordanceLE (comonotonic 2) :=
  (concordanceLE_iff_lowerOrthantLE _ _).2 (lowerOrthantLE_comonotonic C)

end ProbabilityTheory.Copula
