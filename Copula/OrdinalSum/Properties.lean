/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.Basic
import Copula.Order.Orthant
import Copula.Symmetry
import Copula.Diagonal

/-! # Order, recovery and symmetry of ordinal sums -/

open scoped unitInterval

namespace ProbabilityTheory.Copula

open OrdinalSum

theorem LowerOrthantLE.ordinalSum {C D E F : Copula 2}
    (h : C.LowerOrthantLE E) (k : D.LowerOrthantLE F) (a : I) :
    (C.ordinalSum D a).LowerOrthantLE (E.ordinalSum F a) := by
  intro u
  simp only [cdf_ordinalSum, ordinalSumCDF]
  exact add_le_add (mul_le_mul_of_nonneg_left (h _) a.property.1)
    (mul_le_mul_of_nonneg_left (k _) (sub_nonneg.mpr a.property.2))

/-- Each positive-length component can be compared by restricting to its own block. -/
theorem lowerOrthantLE_ordinalSum_iff (C D E F : Copula 2) (a : I)
    (ha0 : 0 < a) (ha1 : a < 1) :
    (C.ordinalSum D a).LowerOrthantLE (E.ordinalSum F a) ↔ C.LowerOrthantLE E ∧ D.LowerOrthantLE F := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => h.1.ordinalSum h.2 a⟩
  · intro u
    have he : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
    have hc := h ![lowerEmbed a (u 0), lowerEmbed a (u 1)]
    rw [cdf_ordinalSum_lowerEmbed C D a _ _ ha0,
      cdf_ordinalSum_lowerEmbed E F a _ _ ha0, he] at hc
    exact le_of_mul_le_mul_left hc (show (0 : ℝ) < a from ha0)
  · intro u
    have he : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
    have hd := h ![upperEmbed a (u 0), upperEmbed a (u 1)]
    rw [cdf_ordinalSum_upperEmbed C D a _ _ ha1,
      cdf_ordinalSum_upperEmbed E F a _ _ ha1, he, add_le_add_iff_left] at hd
    exact le_of_mul_le_mul_left hd (sub_pos.mpr (show (a : ℝ) < 1 from ha1))

theorem ordinalSum_eq_iff (C D E F : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    C.ordinalSum D a = E.ordinalSum F a ↔ C = E ∧ D = F := by
  constructor
  · intro h
    have hf := (lowerOrthantLE_ordinalSum_iff C D E F a ha0 ha1).1 (fun _ => (congrArg cdf h ▸ le_rfl))
    have hb := (lowerOrthantLE_ordinalSum_iff E F C D a ha0 ha1).1 (fun _ => (congrArg cdf h.symm ▸ le_rfl))
    exact ⟨hf.1.antisymm hb.1, hf.2.antisymm hb.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem transpose_ordinalSum (C D : Copula 2) (a : I) :
    (C.ordinalSum D a).transpose = C.transpose.ordinalSum D.transpose a := by
  apply ext_cdf_two
  intro u v
  simp [ordinalSumCDF]

theorem IsExchangeable.ordinalSum {C D : Copula 2} (hC : C.IsExchangeable)
    (hD : D.IsExchangeable) (a : I) : (C.ordinalSum D a).IsExchangeable := by
  unfold IsExchangeable at *
  rw [transpose_ordinalSum, hC, hD]

theorem isExchangeable_ordinalSum_iff (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    (C.ordinalSum D a).IsExchangeable ↔ C.IsExchangeable ∧ D.IsExchangeable := by
  unfold IsExchangeable
  rw [transpose_ordinalSum, ordinalSum_eq_iff _ _ _ _ a ha0 ha1]

@[simp] theorem diagonal_ordinalSum_split (C D : Copula 2) (a : I) :
    (C.ordinalSum D a).diagonal a = a := cdf_ordinalSum_split C D a

theorem diagonal_ordinalSum_lower (C D : Copula 2) (a t : I) (ht : t ≤ a) :
    (C.ordinalSum D a).diagonal t = (a : ℝ) * C.diagonal (lowerCoord a t) :=
  cdf_ordinalSum_lower C D a t t ht ht

theorem diagonal_ordinalSum_upper (C D : Copula 2) (a t : I) (ht : a ≤ t) :
    (C.ordinalSum D a).diagonal t = (a : ℝ) + (1 - (a : ℝ)) * D.diagonal (upperCoord a t) :=
  cdf_ordinalSum_upper C D a t t ht ht

/-- A nontrivial ordinal sum can never be independence. -/
theorem ordinalSum_ne_independence (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    C.ordinalSum D a ≠ independence 2 := by
  intro h
  have he := cdf_ordinalSum_split C D a
  rw [h, cdf_independence] at he
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at he
  have ha0' : (0 : ℝ) < a := ha0
  have ha1' : (a : ℝ) < 1 := ha1
  nlinarith [mul_pos ha0' (sub_pos.mpr ha1')]

theorem not_isNQD_ordinalSum (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    ¬ (C.ordinalSum D a).IsNQD := by
  intro h
  have he := h a a
  rw [cdf_ordinalSum_split] at he
  have ha0' : (0 : ℝ) < a := ha0
  have ha1' : (a : ℝ) < 1 := ha1
  nlinarith [mul_pos ha0' (sub_pos.mpr ha1')]

@[simp] theorem ordinalSum_comonotonic (a : I) :
    (comonotonic 2).ordinalSum (comonotonic 2) a = comonotonic 2 := by
  apply ext_cdf_two
  intro u v
  rcases le_total u a with hu | hu <;> rcases le_total v a with hv | hv
  · rw [cdf_ordinalSum_lower _ _ a u v hu hv, cdf_comonotonic_two, cdf_comonotonic_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_min_of_nonneg _ _ a.property.1, weight_lowerCoord, weight_lowerCoord,
      min_eq_right (show (u : ℝ) ≤ a from hu), min_eq_right (show (v : ℝ) ≤ a from hv)]
  · rw [cdf_ordinalSum_lower_upper _ _ a u v hu hv, cdf_comonotonic_two]
    exact (min_eq_left (show (u : ℝ) ≤ v from hu.trans hv)).symm
  · rw [cdf_ordinalSum_upper_lower _ _ a u v hu hv, cdf_comonotonic_two]
    exact (min_eq_right (show (v : ℝ) ≤ u from hv.trans hu)).symm
  · rw [cdf_ordinalSum_upper _ _ a u v hu hv, cdf_comonotonic_two, cdf_comonotonic_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_min_of_nonneg _ _ (sub_nonneg.mpr a.property.2), weight_upperCoord, weight_upperCoord,
      max_eq_right (sub_nonneg.mpr (show (a : ℝ) ≤ u from hu)),
      max_eq_right (sub_nonneg.mpr (show (a : ℝ) ≤ v from hv)), ← min_add_add_left]
    congr 1 <;> ring

theorem ordinalSum_eq_comonotonic_iff (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    C.ordinalSum D a = comonotonic 2 ↔ C = comonotonic 2 ∧ D = comonotonic 2 := by
  rw [← ordinalSum_eq_iff C D (comonotonic 2) (comonotonic 2) a ha0 ha1, ordinalSum_comonotonic]

end ProbabilityTheory.Copula
