/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Patchwork.Partition

/-! # Finite ordinal sums on arbitrary interval partitions -/

open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

variable {n : ℕ}

/-- Ordered diagonal blocks associated with a finite interval partition. -/
noncomputable def IntervalPartition.ordinalData (P : IntervalPartition n) :
    PatchworkData (Fin n) where
  weight := P.width
  nonneg i := (P.width_pos i).le
  first := P.coord
  second := P.coord
  first_mono := P.coord_mono
  second_mono := P.coord_mono
  first_zero := P.coord_zero
  second_zero := P.coord_zero
  first_one := P.coord_one
  second_one := P.coord_one
  first_margin := P.sum_width_mul_coord
  second_margin := P.sum_width_mul_coord

/-- A finite ordinal sum with arbitrary positive block lengths and local copulas. -/
noncomputable def finiteOrdinalSum (P : IntervalPartition n) (C : Fin n → Copula 2) : Copula 2 :=
  P.ordinalData.copula C

@[simp] theorem cdf_finiteOrdinalSum (P : IntervalPartition n) (C : Fin n → Copula 2)
    (u : Fin 2 → I) :
    (finiteOrdinalSum P C).cdf u =
      ∑ i, P.width i * (C i).cdf ![P.coord i (u 0), P.coord i (u 1)] :=
  P.ordinalData.cdf_copula C u

/-- Finite ordinal sum of copies of the independence copula `Π`. -/
noncomputable def ordinalSumPi (P : IntervalPartition n) : Copula 2 :=
  finiteOrdinalSum P (fun _ => independence 2)

theorem cdf_ordinalSumPi (P : IntervalPartition n) (u v : I) :
    (ordinalSumPi P).cdf ![u, v] =
      ∑ i, P.width i * ((P.coord i u : ℝ) * (P.coord i v : ℝ)) := by
  simp [ordinalSumPi, cdf_independence, Fin.prod_univ_two]

/-- Any finite ordinal sum of copies of `M` is `M`. -/
@[simp] theorem finiteOrdinalSum_comonotonic (P : IntervalPartition n) :
    finiteOrdinalSum P (fun _ => comonotonic 2) = comonotonic 2 := by
  apply ext_cdf
  intro u
  simp only [cdf_finiteOrdinalSum, cdf_comonotonic_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases le_total (u 0) (u 1) with h | h
  · simp_rw [min_eq_left (show (P.coord _ (u 0) : ℝ) ≤ P.coord _ (u 1) from P.coord_mono _ h)]
    rw [P.sum_width_mul_coord, min_eq_left (show (u 0 : ℝ) ≤ u 1 from h)]
  · simp_rw [min_eq_right (show (P.coord _ (u 1) : ℝ) ≤ P.coord _ (u 0) from P.coord_mono _ h)]
    rw [P.sum_width_mul_coord, min_eq_right (show (u 1 : ℝ) ≤ u 0 from h)]

/-- A two-cell partition at an interior split. -/
def IntervalPartition.binary (a : I) (ha0 : 0 < a) (ha1 : a < 1) : IntervalPartition 2 where
  point := ![0, a, 1]
  strictMono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  zero := rfl
  one := rfl

/-- The finite construction agrees with the existing binary ordinal-sum API. -/
theorem finiteOrdinalSum_binary (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    finiteOrdinalSum (IntervalPartition.binary a ha0 ha1) ![C, D] = C.ordinalSum D a := by
  apply ext_cdf
  intro u
  simp [cdf_finiteOrdinalSum, Fin.sum_univ_two, IntervalPartition.binary,
    IntervalPartition.width, IntervalPartition.coord, ordinalSumCDF,
    OrdinalSum.lowerCoord, OrdinalSum.upperCoord]

end ProbabilityTheory.Copula
