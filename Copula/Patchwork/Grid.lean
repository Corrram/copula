/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Patchwork.Partition
import Copula.Countermonotonic

/-! # Checkerboard, check-min and local-copula grid constructions

Entries are cell probabilities: row sums are row widths and column sums
are column widths. The grid can be rectangular and nonuniform. In
particular, no implicit matrix normalization or equal-marginal assumption
is hidden in a constructor.
-/

open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

variable {m n : ℕ}

/-- A nonnegative matrix of cell probabilities with prescribed uniform marginals. -/
structure CellMass (P : IntervalPartition m) (Q : IntervalPartition n) where
  mass : Fin m → Fin n → ℝ
  nonneg : ∀ i j, 0 ≤ mass i j
  row_sum : ∀ i, ∑ j, mass i j = P.width i
  col_sum : ∀ j, ∑ i, mass i j = Q.width j

namespace CellMass

variable {P : IntervalPartition m} {Q : IntervalPartition n}

/-- The coordinate and weight data attached to a matrix of cell masses. -/
noncomputable def patchworkData (A : CellMass P Q) : PatchworkData (Fin m × Fin n) where
  weight ij := A.mass ij.1 ij.2
  nonneg ij := A.nonneg ij.1 ij.2
  first ij := P.coord ij.1
  second ij := Q.coord ij.2
  first_mono ij := P.coord_mono ij.1
  second_mono ij := Q.coord_mono ij.2
  first_zero ij := P.coord_zero ij.1
  second_zero ij := Q.coord_zero ij.2
  first_one ij := P.coord_one ij.1
  second_one ij := Q.coord_one ij.2
  first_margin u := by
    simp only [Fintype.sum_prod_type, ← Finset.sum_mul, A.row_sum]
    exact P.sum_width_mul_coord u
  second_margin v := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, A.col_sum]
    exact Q.sum_width_mul_coord v

/-- Fill every cell with an independently specified local copula. -/
noncomputable def patchwork (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) : Copula 2 :=
  A.patchworkData.copula (fun ij => C ij.1 ij.2)

@[simp] theorem cdf_patchwork (A : CellMass P Q) (C : Fin m → Fin n → Copula 2)
    (u : Fin 2 → I) :
    (A.patchwork C).cdf u =
      ∑ i, ∑ j, A.mass i j * (C i j).cdf ![P.coord i (u 0), Q.coord j (u 1)] := by
  simp [patchwork, PatchworkData.cdf, patchworkData, Fintype.sum_prod_type]

/-- Checkerboard copula: independent local coordinates in every cell. -/
noncomputable def checkerboard (A : CellMass P Q) : Copula 2 :=
  A.patchwork (fun _ _ => independence 2)

/-- Check-min copula: comonotonic local coordinates in every cell. -/
noncomputable def checkMin (A : CellMass P Q) : Copula 2 :=
  A.patchwork (fun _ _ => comonotonic 2)

/-- Check-W copula: countermonotonic local coordinates in every cell. -/
noncomputable def checkW (A : CellMass P Q) : Copula 2 :=
  A.patchwork (fun _ _ => countermonotonic)

theorem cdf_checkerboard (A : CellMass P Q) (u v : I) :
    A.checkerboard.cdf ![u, v] =
      ∑ i, ∑ j, A.mass i j * ((P.coord i u : ℝ) * (Q.coord j v : ℝ)) := by
  simp [checkerboard, cdf_independence, Fin.prod_univ_two]

theorem cdf_checkMin (A : CellMass P Q) (u v : I) :
    A.checkMin.cdf ![u, v] =
      ∑ i, ∑ j, A.mass i j * min (P.coord i u : ℝ) (Q.coord j v : ℝ) := by
  simp only [checkMin, cdf_patchwork, cdf_comonotonic_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]

theorem cdf_checkW (A : CellMass P Q) (u v : I) :
    A.checkW.cdf ![u, v] =
      ∑ i, ∑ j, A.mass i j * max ((P.coord i u : ℝ) + (Q.coord j v : ℝ) - 1) 0 := by
  simp [checkW, cdf_countermonotonic, max_comm]

theorem checkerboard_le_checkMin (A : CellMass P Q) (u : Fin 2 → I) :
    A.checkerboard.cdf u ≤ A.checkMin.cdf u := by
  simp only [checkerboard, checkMin, patchwork, PatchworkData.cdf_copula]
  apply A.patchworkData.cdf_mono
  intro ij v
  simpa only [cdf_comonotonic] using (independence 2).cdf_le_frechet_upper v

/-- The product matrix produces global independence under checkerboard filling. -/
def product (P : IntervalPartition m) (Q : IntervalPartition n) : CellMass P Q where
  mass i j := P.width i * Q.width j
  nonneg i j := mul_nonneg (P.width_pos i).le (Q.width_pos j).le
  row_sum i := by simp [← Finset.mul_sum]
  col_sum j := by simp [← Finset.sum_mul]

@[simp] theorem checkerboard_product (P : IntervalPartition m) (Q : IntervalPartition n) :
    (product P Q).checkerboard = independence 2 := by
  apply ext_cdf
  intro u
  have hu : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
  rw [← hu, cdf_checkerboard]
  simp only [product, cdf_independence, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  calc
    _ = (∑ i, P.width i * (P.coord i (u 0) : ℝ)) *
        (∑ j, Q.width j * (Q.coord j (u 1) : ℝ)) := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring
    _ = _ := by rw [P.sum_width_mul_coord, Q.sum_width_mul_coord]

end CellMass

/-- Sample the actual rectangle probabilities of a copula on a finite grid. -/
noncomputable def cellMass (C : Copula 2) (P : IntervalPartition m)
    (Q : IntervalPartition n) : CellMass P Q where
  mass i j := C.cdf ![P.point i.succ, Q.point j.succ] -
    C.cdf ![P.point i.castSucc, Q.point j.succ] -
    C.cdf ![P.point i.succ, Q.point j.castSucc] +
    C.cdf ![P.point i.castSucc, Q.point j.castSucc]
  nonneg i j := by
    have h := C.rectangleIncrement_cdf_nonneg
      ![P.point i.castSucc, Q.point j.castSucc] ![P.point i.succ, Q.point j.succ] (by
        intro k; fin_cases k
        · exact (P.strictMono Fin.castSucc_lt_succ).le
        · exact (Q.strictMono Fin.castSucc_lt_succ).le)
    simpa only [rectangleIncrement_two, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  row_sum i := by
    simp_rw [show ∀ j : Fin n,
      C.cdf ![P.point i.succ, Q.point j.succ] - C.cdf ![P.point i.castSucc, Q.point j.succ] -
        C.cdf ![P.point i.succ, Q.point j.castSucc] + C.cdf ![P.point i.castSucc, Q.point j.castSucc] =
      (C.cdf ![P.point i.succ, Q.point j.succ] - C.cdf ![P.point i.castSucc, Q.point j.succ]) -
        (C.cdf ![P.point i.succ, Q.point j.castSucc] - C.cdf ![P.point i.castSucc, Q.point j.castSucc])
      from fun _ => by ring]
    rw [IntervalPartition.sum_differences (fun j =>
      C.cdf ![P.point i.succ, Q.point j] - C.cdf ![P.point i.castSucc, Q.point j])]
    simp [Q.zero, Q.one, IntervalPartition.width]
  col_sum j := by
    simp_rw [show ∀ i : Fin m,
      C.cdf ![P.point i.succ, Q.point j.succ] - C.cdf ![P.point i.castSucc, Q.point j.succ] -
        C.cdf ![P.point i.succ, Q.point j.castSucc] + C.cdf ![P.point i.castSucc, Q.point j.castSucc] =
      (C.cdf ![P.point i.succ, Q.point j.succ] - C.cdf ![P.point i.succ, Q.point j.castSucc]) -
        (C.cdf ![P.point i.castSucc, Q.point j.succ] - C.cdf ![P.point i.castSucc, Q.point j.castSucc])
      from fun _ => by ring]
    rw [IntervalPartition.sum_differences (fun i =>
      C.cdf ![P.point i, Q.point j.succ] - C.cdf ![P.point i, Q.point j.castSucc])]
    simp [P.zero, P.one, IntervalPartition.width]

/-- Checkerboard approximation on the chosen grid. -/
noncomputable def checkerboard (C : Copula 2) (P : IntervalPartition m)
    (Q : IntervalPartition n) : Copula 2 := (C.cellMass P Q).checkerboard

/-- Check-min approximation on the chosen grid. -/
noncomputable def checkMin (C : Copula 2) (P : IntervalPartition m)
    (Q : IntervalPartition n) : Copula 2 := (C.cellMass P Q).checkMin

end ProbabilityTheory.Copula
