/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.Measure
import Copula.OrdinalSum.Properties
import Copula.Rank.Concordance

/-! # Rank coefficients of binary ordinal sums

The deficits from one scale cubically for Spearman's rho and quadratically
for Kendall's tau and Spearman's footrule. A more general identity gives
concordance between two ordinal sums with the same split. Every formula
includes the endpoint splits and singular component copulas.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

open OrdinalSum

theorem cdf_ordinalSum_lowerEmbed_vec (C D : Copula 2) (a : I) (x : Fin 2 → I) (ha : 0 < a) :
    (C.ordinalSum D a).cdf (fun i => lowerEmbed a (x i)) = (a : ℝ) * C.cdf x := by
  have he : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  have hf : (fun i => lowerEmbed a (x i)) = ![lowerEmbed a (x 0), lowerEmbed a (x 1)] := by
    ext i; fin_cases i <;> rfl
  rw [hf, cdf_ordinalSum_lowerEmbed C D a (x 0) (x 1) ha, ← he]

theorem cdf_ordinalSum_upperEmbed_vec (C D : Copula 2) (a : I) (x : Fin 2 → I) (ha : a < 1) :
    (C.ordinalSum D a).cdf (fun i => upperEmbed a (x i)) =
      (a : ℝ) + (1 - (a : ℝ)) * D.cdf x := by
  have he : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  have hf : (fun i => upperEmbed a (x i)) = ![upperEmbed a (x 0), upperEmbed a (x 1)] := by
    ext i; fin_cases i <;> rfl
  rw [hf, cdf_ordinalSum_upperEmbed C D a (x 0) (x 1) ha, ← he]

/-- Concordance of two ordinal sums with a common split. -/
theorem concordanceQ_ordinalSum (C D E F : Copula 2) (a : I) :
    (C.ordinalSum D a).concordanceQ (E.ordinalSum F a) =
      1 - (a : ℝ) ^ 2 * (1 - C.concordanceQ E) -
        (1 - (a : ℝ)) ^ 2 * (1 - D.concordanceQ F) := by
  by_cases ha0 : a = 0
  · simp [ha0]
  by_cases ha1 : a = 1
  · simp [ha1]
  have hp : 0 < a := lt_of_le_of_ne a.property.1 (Ne.symm ha0)
  have hl : a < 1 := lt_of_le_of_ne a.property.2 ha1
  rw [concordanceQ, integral_ordinalSum E F a (C.ordinalSum D a).continuous_cdf]
  simp_rw [cdf_ordinalSum_lowerEmbed_vec C D a _ hp, cdf_ordinalSum_upperEmbed_vec C D a _ hl]
  rw [integral_const_mul, integral_add (integrable_const _) ((D.integrable_cdf F.toMeasure).const_mul _),
    integral_const, integral_const_mul]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  unfold concordanceQ
  ring

theorem kendallTau_ordinalSum (C D : Copula 2) (a : I) :
    (C.ordinalSum D a).kendallTau =
      1 - (a : ℝ) ^ 2 * (1 - C.kendallTau) - (1 - (a : ℝ)) ^ 2 * (1 - D.kendallTau) :=
  concordanceQ_ordinalSum C D C D a

theorem spearmanFootrule_ordinalSum (C D : Copula 2) (a : I) :
    (C.ordinalSum D a).spearmanFootrule =
      1 - (a : ℝ) ^ 2 * (1 - C.spearmanFootrule) -
        (1 - (a : ℝ)) ^ 2 * (1 - D.spearmanFootrule) := by
  have h := concordanceQ_ordinalSum C D (comonotonic 2) (comonotonic 2) a
  rw [ordinalSum_comonotonic] at h
  simp only [concordanceQ_comonotonic] at h
  nlinarith only [h]

theorem spearmanRho_ordinalSum (C D : Copula 2) (a : I) :
    (C.ordinalSum D a).spearmanRho =
      1 - (a : ℝ) ^ 3 * (1 - C.spearmanRho) -
        (1 - (a : ℝ)) ^ 3 * (1 - D.spearmanRho) := by
  have hlo : (fun x : Fin 2 → I => ((lowerEmbed a (x 0) : ℝ) - lowerEmbed a (x 1)) ^ 2) =
      fun x => (a : ℝ) ^ 2 * ((x 0 : ℝ) - x 1) ^ 2 := by
    funext x
    change ((a : ℝ) * x 0 - (a : ℝ) * x 1) ^ 2 = _
    ring
  have hup : (fun x : Fin 2 → I => ((upperEmbed a (x 0) : ℝ) - upperEmbed a (x 1)) ^ 2) =
      fun x => (1 - (a : ℝ)) ^ 2 * ((x 0 : ℝ) - x 1) ^ 2 := by
    funext x
    change ((a : ℝ) + (1 - (a : ℝ)) * x 0 - ((a : ℝ) + (1 - (a : ℝ)) * x 1)) ^ 2 = _
    ring
  rw [spearmanRho_eq_one_sub, integral_ordinalSum C D a (by fun_prop)]
  change 1 - 6 * ((a : ℝ) * (∫ x, ((lowerEmbed a (x 0) : ℝ) - lowerEmbed a (x 1)) ^ 2 ∂C.toMeasure) +
    (1 - (a : ℝ)) * ∫ x, ((upperEmbed a (x 0) : ℝ) - upperEmbed a (x 1)) ^ 2 ∂D.toMeasure) = _
  rw [hlo, hup, integral_const_mul, integral_const_mul,
    C.spearmanRho_eq_one_sub, D.spearmanRho_eq_one_sub]
  ring

end ProbabilityTheory.Copula
