/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.Components

/-! # The converse ordinal-sum theorem

At each interior diagonal fixed point a copula is the ordinal sum of its
two rescaled restrictions. The pair of components is unique for that fixed
split. This is the binary form of Nelsen's Theorem 3.2.1; the split itself
need not be unique.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

open OrdinalSum

theorem ordinalSum_components (C : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1)
    (ha : C.diagonal a = a) :
    (C.lowerOrdinalComponent a ha0 ha).ordinalSum (C.upperOrdinalComponent a ha1 ha) a = C := by
  have hp : (0 : ℝ) < a := ha0
  have hq : 0 < 1 - (a : ℝ) := sub_pos.mpr ha1
  apply ext_cdf_two
  intro u v
  rcases le_total u a with hu | hu <;> rcases le_total v a with hv | hv
  · rw [cdf_ordinalSum_lower _ _ a u v hu hv, cdf_lowerOrdinalComponent]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      lowerEmbed_lowerCoord a u hu, lowerEmbed_lowerCoord a v hv]
    field_simp [hp.ne']
  · rw [cdf_ordinalSum_lower_upper _ _ a u v hu hv, C.cdf_cross_cut_lower_upper a u v ha hu hv]
  · rw [cdf_ordinalSum_upper_lower _ _ a u v hu hv, C.cdf_cross_cut_upper_lower a u v ha hu hv]
  · rw [cdf_ordinalSum_upper _ _ a u v hu hv, cdf_upperOrdinalComponent]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      upperEmbed_upperCoord a u hu, upperEmbed_upperCoord a v hv]
    field_simp [hq.ne']
    ring

@[simp] theorem lowerOrdinalComponent_ordinalSum (C D : Copula 2) (a : I) (ha0 : 0 < a) :
    (C.ordinalSum D a).lowerOrdinalComponent a ha0 (diagonal_ordinalSum_split C D a) = C := by
  apply ext_cdf
  intro u
  rw [cdf_lowerOrdinalComponent, cdf_ordinalSum_lowerEmbed C D a (u 0) (u 1) ha0]
  have he : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
  rw [he]
  have hp : (0 : ℝ) < a := ha0
  field_simp [hp.ne']

@[simp] theorem upperOrdinalComponent_ordinalSum (C D : Copula 2) (a : I) (ha1 : a < 1) :
    (C.ordinalSum D a).upperOrdinalComponent a ha1 (diagonal_ordinalSum_split C D a) = D := by
  apply ext_cdf
  intro u
  rw [cdf_upperOrdinalComponent, cdf_ordinalSum_upperEmbed C D a (u 0) (u 1) ha1]
  have he : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
  rw [he]
  have hp : 0 < 1 - (a : ℝ) := sub_pos.mpr ha1
  field_simp [hp.ne']
  ring

@[simp] theorem lowerOrdinalComponent_one (C : Copula 2) :
    C.lowerOrdinalComponent 1 zero_lt_one C.diagonal_one = C := by
  apply ext_cdf
  intro u
  have he : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
  have hl (t : I) : lowerEmbed 1 t = t := by apply Subtype.ext; simp [lowerEmbed]
  rw [cdf_lowerOrdinalComponent, hl, hl, he]
  simp

@[simp] theorem upperOrdinalComponent_zero (C : Copula 2) :
    C.upperOrdinalComponent 0 zero_lt_one C.diagonal_zero = C := by
  apply ext_cdf
  intro u
  have he : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
  have hu (t : I) : upperEmbed 0 t = t := by apply Subtype.ext; simp [upperEmbed]
  rw [cdf_upperOrdinalComponent, hu, hu, he]
  simp

/-- A prescribed interior point is an ordinal-sum split exactly when the diagonal is fixed there. -/
theorem diagonal_eq_iff_exists_ordinalSum (C : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    C.diagonal a = a ↔ ∃ D E : Copula 2, D.ordinalSum E a = C := by
  refine ⟨fun ha => ⟨C.lowerOrdinalComponent a ha0 ha, C.upperOrdinalComponent a ha1 ha,
    C.ordinalSum_components a ha0 ha1 ha⟩, ?_⟩
  rintro ⟨D, E, rfl⟩
  exact diagonal_ordinalSum_split D E a

/-- For a fixed interior split, the two components are uniquely determined. -/
theorem diagonal_eq_iff_existsUnique_ordinalSum (C : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    C.diagonal a = a ↔ ∃! p : Copula 2 × Copula 2, p.1.ordinalSum p.2 a = C := by
  constructor
  · intro ha
    refine ⟨⟨C.lowerOrdinalComponent a ha0 ha, C.upperOrdinalComponent a ha1 ha⟩,
      C.ordinalSum_components a ha0 ha1 ha, ?_⟩
    intro p hp
    have he := (ordinalSum_eq_iff _ _ _ _ a ha0 ha1).mp
      (hp.trans (C.ordinalSum_components a ha0 ha1 ha).symm)
    exact Prod.ext he.1 he.2
  · rintro ⟨p, hp, _⟩
    exact (C.diagonal_eq_iff_exists_ordinalSum a ha0 ha1).mpr ⟨p.1, p.2, hp⟩

/-- The binary ordinal-sum characterization, Nelsen, second edition, Theorem 3.2.1. -/
theorem exists_ordinalSum_iff_exists_diagonal_fixedPoint (C : Copula 2) :
    (∃ (a : I) (D E : Copula 2), 0 < a ∧ a < 1 ∧ D.ordinalSum E a = C) ↔
      ∃ a : I, 0 < a ∧ a < 1 ∧ C.diagonal a = a := by
  constructor
  · rintro ⟨a, D, E, ha0, ha1, he⟩
    exact ⟨a, ha0, ha1, (C.diagonal_eq_iff_exists_ordinalSum a ha0 ha1).mpr ⟨D, E, he⟩⟩
  · rintro ⟨a, ha0, ha1, ha⟩
    exact ⟨a, C.lowerOrdinalComponent a ha0 ha, C.upperOrdinalComponent a ha1 ha,
      ha0, ha1, C.ordinalSum_components a ha0 ha1 ha⟩

theorem IsNQD.not_exists_ordinalSum {C : Copula 2} (h : C.IsNQD) :
    ¬ ∃ (a : I) (D E : Copula 2), 0 < a ∧ a < 1 ∧ D.ordinalSum E a = C := by
  rw [exists_ordinalSum_iff_exists_diagonal_fixedPoint]
  rintro ⟨a, ha0, ha1, ha⟩
  exact (h.diagonal_lt a ha0 ha1).ne ha

end ProbabilityTheory.Copula
