/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.Decomposition
import Copula.OrdinalSum.RankExamples
import Copula.Rank.MedianExtrema

/-! # Consequences of diagonal cuts

The decomposition theorem transfers fixed-split rank bounds to any copula
with a diagonal fixed point. At the median this gives a structural
characterization of maximal Blomqvist beta and sharp bounds on three other
rank coefficients. Component diagonals retain the remaining cuts.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

open OrdinalSum

theorem diagonal_lowerOrdinalComponent (C : Copula 2) (a : I) (ha0 : 0 < a)
    (ha : C.diagonal a = a) (t : I) :
    (C.lowerOrdinalComponent a ha0 ha).diagonal t = C.diagonal (lowerEmbed a t) / a := by
  simp [diagonal]

theorem diagonal_upperOrdinalComponent (C : Copula 2) (a : I) (ha1 : a < 1)
    (ha : C.diagonal a = a) (t : I) :
    (C.upperOrdinalComponent a ha1 ha).diagonal t =
      (C.diagonal (upperEmbed a t) - a) / (1 - a) := by
  simp [diagonal]

theorem diagonal_lowerOrdinalComponent_eq_iff (C : Copula 2) (a : I) (ha0 : 0 < a)
    (ha : C.diagonal a = a) (t : I) :
    (C.lowerOrdinalComponent a ha0 ha).diagonal t = t ↔
      C.diagonal (lowerEmbed a t) = (lowerEmbed a t : ℝ) := by
  rw [diagonal_lowerOrdinalComponent, div_eq_iff (ne_of_gt (show (0 : ℝ) < a from ha0))]
  change C.diagonal (lowerEmbed a t) = (t : ℝ) * a ↔ C.diagonal (lowerEmbed a t) = (a : ℝ) * t
  rw [mul_comm (t : ℝ)]

theorem diagonal_upperOrdinalComponent_eq_iff (C : Copula 2) (a : I) (ha1 : a < 1)
    (ha : C.diagonal a = a) (t : I) :
    (C.upperOrdinalComponent a ha1 ha).diagonal t = t ↔
      C.diagonal (upperEmbed a t) = (upperEmbed a t : ℝ) := by
  rw [diagonal_upperOrdinalComponent,
    div_eq_iff (ne_of_gt (sub_pos.mpr (show (a : ℝ) < 1 from ha1)))]
  change C.diagonal (upperEmbed a t) - a = (t : ℝ) * (1 - (a : ℝ)) ↔
    C.diagonal (upperEmbed a t) = (a : ℝ) + (1 - (a : ℝ)) * t
  constructor <;> intro h <;> nlinarith only [h]

theorem kendallTau_lower_bound_of_diagonal_eq (C : Copula 2) (a : I)
    (ha0 : 0 < a) (ha1 : a < 1) (ha : C.diagonal a = a) :
    4 * (a : ℝ) * (1 - (a : ℝ)) - 1 ≤ C.kendallTau := by
  simpa only [C.ordinalSum_components a ha0 ha1 ha] using
    kendallTau_ordinalSum_lower_bound (C.lowerOrdinalComponent a ha0 ha)
      (C.upperOrdinalComponent a ha1 ha) a

theorem spearmanRho_lower_bound_of_diagonal_eq (C : Copula 2) (a : I)
    (ha0 : 0 < a) (ha1 : a < 1) (ha : C.diagonal a = a) :
    6 * (a : ℝ) * (1 - (a : ℝ)) - 1 ≤ C.spearmanRho := by
  simpa only [C.ordinalSum_components a ha0 ha1 ha] using
    spearmanRho_ordinalSum_lower_bound (C.lowerOrdinalComponent a ha0 ha)
      (C.upperOrdinalComponent a ha1 ha) a

theorem spearmanFootrule_lower_bound_of_diagonal_eq (C : Copula 2) (a : I)
    (ha0 : 0 < a) (ha1 : a < 1) (ha : C.diagonal a = a) :
    3 * (a : ℝ) * (1 - (a : ℝ)) - 1 / 2 ≤ C.spearmanFootrule := by
  simpa only [C.ordinalSum_components a ha0 ha1 ha] using
    spearmanFootrule_ordinalSum_lower_bound (C.lowerOrdinalComponent a ha0 ha)
      (C.upperOrdinalComponent a ha1 ha) a

private theorem unitHalf_pos : 0 < unitHalf := by change (0 : ℝ) < 1 / 2; norm_num

private theorem unitHalf_lt_one : unitHalf < 1 := by change (1 / 2 : ℝ) < 1; norm_num

theorem blomqvistBeta_eq_one_iff_exists_ordinalSum (C : Copula 2) :
    C.blomqvistBeta = 1 ↔ ∃ D E : Copula 2, D.ordinalSum E unitHalf = C := by
  rw [C.blomqvistBeta_eq_one_iff, ← C.diagonal_eq_iff_exists_ordinalSum
    unitHalf unitHalf_pos unitHalf_lt_one]
  rfl

theorem blomqvistBeta_eq_one_iff_existsUnique_ordinalSum (C : Copula 2) :
    C.blomqvistBeta = 1 ↔ ∃! p : Copula 2 × Copula 2, p.1.ordinalSum p.2 unitHalf = C := by
  rw [C.blomqvistBeta_eq_one_iff, ← C.diagonal_eq_iff_existsUnique_ordinalSum
    unitHalf unitHalf_pos unitHalf_lt_one]
  rfl

theorem kendallTau_nonneg_of_blomqvistBeta_eq_one (C : Copula 2) (h : C.blomqvistBeta = 1) :
    0 ≤ C.kendallTau := by
  have ha : C.diagonal unitHalf = (unitHalf : ℝ) := C.blomqvistBeta_eq_one_iff.mp h
  have hb := C.kendallTau_lower_bound_of_diagonal_eq unitHalf unitHalf_pos unitHalf_lt_one ha
  norm_num [unitHalf] at hb
  exact hb

theorem half_le_spearmanRho_of_blomqvistBeta_eq_one (C : Copula 2) (h : C.blomqvistBeta = 1) :
    1 / 2 ≤ C.spearmanRho := by
  have ha : C.diagonal unitHalf = (unitHalf : ℝ) := C.blomqvistBeta_eq_one_iff.mp h
  have hb := C.spearmanRho_lower_bound_of_diagonal_eq unitHalf unitHalf_pos unitHalf_lt_one ha
  norm_num [unitHalf] at hb
  exact hb

theorem quarter_le_spearmanFootrule_of_blomqvistBeta_eq_one (C : Copula 2) (h : C.blomqvistBeta = 1) :
    1 / 4 ≤ C.spearmanFootrule := by
  have ha : C.diagonal unitHalf = (unitHalf : ℝ) := C.blomqvistBeta_eq_one_iff.mp h
  have hb := C.spearmanFootrule_lower_bound_of_diagonal_eq unitHalf unitHalf_pos unitHalf_lt_one ha
  norm_num [unitHalf] at hb
  exact hb

theorem blomqvistBeta_eq_neg_one_iff_exists_reflected_ordinalSum (C : Copula 2) :
    C.blomqvistBeta = -1 ↔ ∃ D E : Copula 2, (D.ordinalSum E unitHalf).reflect {1} = C := by
  constructor
  · intro h
    have hr : (C.reflect {1}).blomqvistBeta = 1 := by
      rw [blomqvistBeta_reflect_second, h]
      norm_num
    obtain ⟨D, E, he⟩ := (blomqvistBeta_eq_one_iff_exists_ordinalSum _).mp hr
    refine ⟨D, E, ?_⟩
    simpa only [reflect_reflect] using congrArg (fun K : Copula 2 => K.reflect {1}) he
  · rintro ⟨D, E, rfl⟩
    exact blomqvistBeta_reflect_ordinalSum_half D E

theorem kendallTau_nonpos_of_blomqvistBeta_eq_neg_one (C : Copula 2) (h : C.blomqvistBeta = -1) :
    C.kendallTau ≤ 0 := by
  have hr : (C.reflect {1}).blomqvistBeta = 1 := by
    rw [blomqvistBeta_reflect_second, h]
    norm_num
  have hb := (C.reflect {1}).kendallTau_nonneg_of_blomqvistBeta_eq_one hr
  rw [kendallTau_reflect_second] at hb
  linarith

theorem spearmanRho_le_neg_half_of_blomqvistBeta_eq_neg_one (C : Copula 2) (h : C.blomqvistBeta = -1) :
    C.spearmanRho ≤ -1 / 2 := by
  have hr : (C.reflect {1}).blomqvistBeta = 1 := by
    rw [blomqvistBeta_reflect_second, h]
    norm_num
  have hb := (C.reflect {1}).half_le_spearmanRho_of_blomqvistBeta_eq_one hr
  rw [spearmanRho_reflect_second] at hb
  linarith

end ProbabilityTheory.Copula
