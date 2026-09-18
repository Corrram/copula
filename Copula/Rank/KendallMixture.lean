/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Concordance

/-! # Kendall's tau of mixtures

Tau is a quadratic functional, with cross terms given by the concordance
function. In particular, dilution by independence involves both tau and rho.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem kendallTau_finiteMixture {n : ℕ} (C : Fin n → Copula 2) (w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) :
    (finiteMixture C w hw hsum).kendallTau =
      ∑ i, ∑ j, w i * w j * (C i).concordanceQ (C j) := by
  rw [← concordanceQ_self, concordanceQ_finiteMixture_left]
  simp_rw [concordanceQ_finiteMixture_right, Finset.mul_sum, mul_assoc]

theorem kendallTau_mix (C D : Copula 2) (a : I) :
    (C.mix D a).kendallTau = (a : ℝ) ^ 2 * C.kendallTau +
      (1 - (a : ℝ)) ^ 2 * D.kendallTau + 2 * (a : ℝ) * (1 - (a : ℝ)) * C.concordanceQ D := by
  rw [← concordanceQ_self, concordanceQ_mix_left]
  simp only [concordanceQ_mix_right, concordanceQ_self]
  rw [concordanceQ_comm D C]
  ring

theorem kendallTau_mix_independence (C : Copula 2) (a : I) :
    (C.mix (independence 2) a).kendallTau =
      (a : ℝ) ^ 2 * C.kendallTau + 2 / 3 * (a : ℝ) * (1 - (a : ℝ)) * C.spearmanRho := by
  rw [kendallTau_mix, concordanceQ_independence, kendallTau_independence]
  ring

theorem kendallTau_mix_comonotonic (C : Copula 2) (a : I) :
    (C.mix (comonotonic 2) a).kendallTau = (a : ℝ) ^ 2 * C.kendallTau +
      (1 - (a : ℝ)) ^ 2 +
        2 / 3 * (a : ℝ) * (1 - (a : ℝ)) * (2 * C.spearmanFootrule + 1) := by
  rw [kendallTau_mix, concordanceQ_comonotonic, kendallTau_comonotonic]
  ring

theorem kendallTau_mix_countermonotonic (C : Copula 2) (a : I) :
    (C.mix countermonotonic a).kendallTau = (a : ℝ) ^ 2 * C.kendallTau -
      (1 - (a : ℝ)) ^ 2 + 2 * (a : ℝ) * (1 - (a : ℝ)) *
        (C.giniGamma - (2 * C.spearmanFootrule + 1) / 3) := by
  rw [kendallTau_mix, concordanceQ_countermonotonic, kendallTau_countermonotonic]
  ring

theorem kendallTau_mix_comonotonic_countermonotonic (a : I) :
    ((comonotonic 2).mix countermonotonic a).kendallTau = 2 * (a : ℝ) - 1 := by
  rw [kendallTau_mix, concordanceQ_comonotonic_countermonotonic,
    kendallTau_comonotonic, kendallTau_countermonotonic]
  ring

/-- Tau is not affine on the convex set of copulas. -/
theorem kendallTau_not_affine :
    ¬ ∀ (C D : Copula 2) (a : I), (C.mix D a).kendallTau =
      (a : ℝ) * C.kendallTau + (1 - (a : ℝ)) * D.kendallTau := by
  intro h
  have he := h (comonotonic 2) (independence 2) unitHalf
  rw [kendallTau_mix_independence] at he
  norm_num [unitHalf] at he

end ProbabilityTheory.Copula
