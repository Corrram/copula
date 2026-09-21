/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Patchwork.Basic

/-! # Finite interval partitions and clipped local coordinates -/

open Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

/-- A strictly increasing finite partition of the whole unit interval.
Positive cell lengths exclude division by zero; a partition with no cells
cannot satisfy the two endpoint requirements. -/
structure IntervalPartition (n : ℕ) where
  point : Fin (n + 1) → I
  strictMono : StrictMono point
  zero : point 0 = 0
  one : point (Fin.last n) = 1

namespace IntervalPartition

variable {n : ℕ}

/-- Length of a partition cell. -/
def width (P : IntervalPartition n) (i : Fin n) : ℝ :=
  (P.point i.succ : ℝ) - P.point i.castSucc

theorem width_pos (P : IntervalPartition n) (i : Fin n) : 0 < P.width i :=
  sub_pos.mpr (P.strictMono Fin.castSucc_lt_succ)

/-- Inverse affine coordinate in a cell, clipped to the unit interval. -/
noncomputable def coord (P : IntervalPartition n) (i : Fin n) (u : I) : I :=
  projIcc 0 1 zero_le_one (((u : ℝ) - P.point i.castSucc) / P.width i)

theorem coord_mono (P : IntervalPartition n) (i : Fin n) : Monotone (P.coord i) := by
  intro u v huv
  change (u : ℝ) ≤ v at huv
  exact monotone_projIcc zero_le_one
    (div_le_div_of_nonneg_right (sub_le_sub_right huv _) (P.width_pos i).le)

theorem coord_of_le (P : IntervalPartition n) (i : Fin n) (u : I)
    (hu : u ≤ P.point i.castSucc) : P.coord i u = 0 :=
  projIcc_of_le_left zero_le_one
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu) (P.width_pos i).le)

theorem coord_of_ge (P : IntervalPartition n) (i : Fin n) (u : I)
    (hu : P.point i.succ ≤ u) : P.coord i u = 1 := by
  change (P.point i.succ : ℝ) ≤ u at hu
  apply projIcc_of_right_le zero_le_one
  apply (one_le_div (P.width_pos i)).2
  exact sub_le_sub_right hu _

@[simp] theorem coord_zero (P : IntervalPartition n) (i : Fin n) : P.coord i 0 = 0 :=
  P.coord_of_le i 0 (P.point i.castSucc).property.1

@[simp] theorem coord_one (P : IntervalPartition n) (i : Fin n) : P.coord i 1 = 1 :=
  P.coord_of_ge i 1 (P.point i.succ).property.2

theorem coe_coord_of_mem (P : IntervalPartition n) (i : Fin n) (u : I)
    (hl : P.point i.castSucc ≤ u) (hr : u ≤ P.point i.succ) :
    (P.coord i u : ℝ) = ((u : ℝ) - P.point i.castSucc) / P.width i := by
  change (P.point i.castSucc : ℝ) ≤ u at hl
  change (u : ℝ) ≤ P.point i.succ at hr
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one
    ⟨div_nonneg (sub_nonneg.mpr hl) (P.width_pos i).le,
      (div_le_one (P.width_pos i)).2 (sub_le_sub_right hr _)⟩)

theorem width_mul_coord (P : IntervalPartition n) (i : Fin n) (u : I) :
    P.width i * (P.coord i u : ℝ) =
      min (u : ℝ) (P.point i.succ) - min (u : ℝ) (P.point i.castSucc) := by
  have hab : P.point i.castSucc ≤ P.point i.succ :=
    (P.strictMono Fin.castSucc_lt_succ).le
  rcases le_total u (P.point i.castSucc) with hu | hu
  · rw [P.coord_of_le i u hu]
    change (u : ℝ) ≤ P.point i.castSucc at hu
    change (P.point i.castSucc : ℝ) ≤ P.point i.succ at hab
    rw [min_eq_left (hu.trans hab), min_eq_left hu]
    simp
  · rcases le_total u (P.point i.succ) with hv | hv
    · rw [P.coe_coord_of_mem i u hu hv]
      change (P.point i.castSucc : ℝ) ≤ u at hu
      change (u : ℝ) ≤ P.point i.succ at hv
      rw [min_eq_left hv, min_eq_right hu]
      exact mul_div_cancel₀ _ (P.width_pos i).ne'
    · rw [P.coord_of_ge i u hv]
      change (P.point i.castSucc : ℝ) ≤ u at hu
      change (P.point i.succ : ℝ) ≤ u at hv
      rw [min_eq_right hv, min_eq_right hu]
      change P.width i * 1 = _
      rw [mul_one]
      rfl

/-- Telescoping over consecutive endpoints, including the empty sum. -/
theorem sum_differences (f : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (f i.succ - f i.castSucc)) = f (Fin.last n) - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have ht := ih (fun i => f i.succ)
    change f 1 - f 0 + ∑ i : Fin n, (f i.succ.succ - f i.castSucc.succ) = _
    rw [ht]
    change f 1 - f 0 + (f (Fin.last (n + 1)) - f 1) = _
    ring

theorem sum_width_mul_coord (P : IntervalPartition n) (u : I) :
    (∑ i, P.width i * (P.coord i u : ℝ)) = u := by
  simp_rw [P.width_mul_coord]
  rw [sum_differences (fun i => min (u : ℝ) (P.point i))]
  simp [P.one, P.zero, min_eq_left u.property.2, min_eq_right u.property.1]

@[simp] theorem sum_width (P : IntervalPartition n) : ∑ i, P.width i = 1 := by
  simpa using P.sum_width_mul_coord 1

/-- The equally spaced partition into `n` cells, for `n > 0`. -/
noncomputable def uniform (n : ℕ) (hn : 0 < n) : IntervalPartition n where
  point i := ⟨(i : ℝ) / n, div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    (div_le_one (Nat.cast_pos.mpr hn)).2 (by exact_mod_cast i.is_le)⟩
  strictMono := by
    intro i j hij
    change (i : ℝ) / n < (j : ℝ) / n
    exact (div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hn)).2 (by exact_mod_cast hij)
  zero := by apply Subtype.ext; simp
  one := by apply Subtype.ext; simp [Nat.ne_of_gt hn]

@[simp] theorem width_uniform (n : ℕ) (hn : 0 < n) (i : Fin n) :
    (uniform n hn).width i = 1 / (n : ℝ) := by
  simp [width, uniform, Nat.cast_add, add_div]

end IntervalPartition

end ProbabilityTheory.Copula
