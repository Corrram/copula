/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Extrema
import Copula.OrdinalSum.Properties

/-! # Median concordance and nonunique extremal coefficients

Beta is extremal exactly when the midpoint CDF attains its corresponding
bound. Its negative extreme is also equivalent to minimal footrule and
the lower Fréchet diagonal. Explicit ordinal sums show that neither extreme
of beta, nor the lower extreme of footrule, determines a unique copula.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem blomqvistBeta_eq_one_iff (C : Copula 2) :
    C.blomqvistBeta = 1 ↔ C.cdf ![unitHalf, unitHalf] = 1 / 2 := by
  unfold blomqvistBeta
  constructor <;> intro h <;> linarith

theorem blomqvistBeta_eq_neg_one_iff (C : Copula 2) :
    C.blomqvistBeta = -1 ↔ C.cdf ![unitHalf, unitHalf] = 0 := by
  unfold blomqvistBeta
  constructor <;> intro h <;> linarith

theorem diagonal_eq_lower_iff_blomqvistBeta_eq_neg_one (C : Copula 2) :
    (∀ t : I, C.diagonal t = max 0 (2 * (t : ℝ) - 1)) ↔ C.blomqvistBeta = -1 := by
  rw [C.blomqvistBeta_eq_neg_one_iff]
  constructor
  · intro h
    simpa only [diagonal, unitHalf, max_self, show (2 : ℝ) * (1 / 2) - 1 = 0 by norm_num]
      using h unitHalf
  · intro h t
    have hz : C.diagonal unitHalf = 0 := h
    apply le_antisymm _ (C.diagonal_lower_bound t)
    rcases le_total t unitHalf with ht | ht
    · have hu := C.monotone_diagonal ht
      rw [hz] at hu
      exact hu.trans (le_max_left _ _)
    · have hu := (C.diagonal_sub_mem_Icc ht).2
      rw [hz] at hu
      have hb : C.diagonal t ≤ 2 * (t : ℝ) - 1 := by
        change C.diagonal t - 0 ≤ 2 * ((t : ℝ) - 1 / 2) at hu
        linarith
      exact hb.trans (le_max_right _ _)

theorem spearmanFootrule_eq_neg_half_iff_blomqvistBeta_eq_neg_one (C : Copula 2) :
    C.spearmanFootrule = -1 / 2 ↔ C.blomqvistBeta = -1 := by
  rw [C.spearmanFootrule_eq_neg_half_iff, C.diagonal_eq_lower_iff_blomqvistBeta_eq_neg_one]

theorem neg_half_lt_spearmanFootrule_iff (C : Copula 2) :
    -1 / 2 < C.spearmanFootrule ↔ C.blomqvistBeta ≠ -1 := by
  rw [lt_iff_le_and_ne, and_iff_right C.spearmanFootrule_mem_Icc.1, ne_comm]
  exact not_congr C.spearmanFootrule_eq_neg_half_iff_blomqvistBeta_eq_neg_one

theorem blomqvistBeta_ordinalSum_half (C D : Copula 2) :
    (C.ordinalSum D unitHalf).blomqvistBeta = 1 := by
  rw [blomqvistBeta, cdf_ordinalSum_split]
  norm_num [unitHalf]

theorem blomqvistBeta_reflect_ordinalSum_half (C D : Copula 2) :
    ((C.ordinalSum D unitHalf).reflect {1}).blomqvistBeta = -1 := by
  rw [blomqvistBeta_reflect_second, blomqvistBeta_ordinalSum_half]

theorem spearmanFootrule_reflect_ordinalSum_half (C D : Copula 2) :
    ((C.ordinalSum D unitHalf).reflect {1}).spearmanFootrule = -1 / 2 :=
  (spearmanFootrule_eq_neg_half_iff_blomqvistBeta_eq_neg_one _).mpr
    (blomqvistBeta_reflect_ordinalSum_half C D)

theorem ordinalSum_independence_half_ne_comonotonic :
    (independence 2).ordinalSum (independence 2) unitHalf ≠ comonotonic 2 := by
  intro h
  have he := ((ordinalSum_eq_comonotonic_iff _ _ unitHalf
    (by change (0 : ℝ) < 1 / 2; norm_num)
    (by change (1 / 2 : ℝ) < 1; norm_num)).mp h).1
  have hr := congrArg spearmanRho he
  norm_num at hr

/-- Maximal median concordance does not characterize comonotonicity. -/
theorem exists_blomqvistBeta_eq_one_ne_comonotonic :
    ∃ C : Copula 2, C.blomqvistBeta = 1 ∧ C ≠ comonotonic 2 :=
  ⟨(independence 2).ordinalSum (independence 2) unitHalf,
    blomqvistBeta_ordinalSum_half _ _, ordinalSum_independence_half_ne_comonotonic⟩

/-- Minimal median concordance does not characterize countermonotonicity. -/
theorem exists_blomqvistBeta_eq_neg_one_ne_countermonotonic :
    ∃ C : Copula 2, C.blomqvistBeta = -1 ∧ C ≠ countermonotonic := by
  refine ⟨((independence 2).ordinalSum (independence 2) unitHalf).reflect {1},
    blomqvistBeta_reflect_ordinalSum_half _ _, fun h => ?_⟩
  exact ordinalSum_independence_half_ne_comonotonic
    (reflect_injective {1} (h.trans reflect_comonotonic_eq_countermonotonic.symm))

/-- Minimal footrule does not characterize countermonotonicity. -/
theorem exists_spearmanFootrule_eq_neg_half_ne_countermonotonic :
    ∃ C : Copula 2, C.spearmanFootrule = -1 / 2 ∧ C ≠ countermonotonic := by
  obtain ⟨C, h, hne⟩ := exists_blomqvistBeta_eq_neg_one_ne_countermonotonic
  exact ⟨C, C.spearmanFootrule_eq_neg_half_iff_blomqvistBeta_eq_neg_one.mpr h, hne⟩

end ProbabilityTheory.Copula
