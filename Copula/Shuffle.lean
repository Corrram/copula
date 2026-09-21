/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.Finite
import Copula.Countermonotonic

/-! # Finite shuffles of min

Two partitions and a permutation describe the source and target strips.
Corresponding strips must have equal lengths. A Boolean for each strip
allows its diagonal to be reflected, giving both orientations of the
classical shuffle construction. Equal-width straight shuffles are included.
-/

open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

variable {n : ℕ}

/-- Coordinate data of a length-preserving permutation of interval strips. -/
noncomputable def shuffleData (P Q : IntervalPartition n) (perm : Equiv.Perm (Fin n))
    (hwidth : ∀ i, P.width i = Q.width (perm i)) : PatchworkData (Fin n) where
  weight := P.width
  nonneg i := (P.width_pos i).le
  first := P.coord
  second i := Q.coord (perm i)
  first_mono := P.coord_mono
  second_mono i := Q.coord_mono (perm i)
  first_zero := P.coord_zero
  second_zero i := Q.coord_zero (perm i)
  first_one := P.coord_one
  second_one i := Q.coord_one (perm i)
  first_margin := P.sum_width_mul_coord
  second_margin v := by
    simp_rw [hwidth]
    rw [Equiv.sum_comp perm (fun i => Q.width i * (Q.coord i v : ℝ))]
    exact Q.sum_width_mul_coord v

/-- A shuffle of `M`, with optional reflection of each segment. -/
noncomputable def shuffleOfMin (P Q : IntervalPartition n) (perm : Equiv.Perm (Fin n))
    (hwidth : ∀ i, P.width i = Q.width (perm i)) (flipped : Fin n → Bool) : Copula 2 :=
  (shuffleData P Q perm hwidth).copula
    (fun i => if flipped i then countermonotonic else comonotonic 2)

theorem cdf_shuffleOfMin (P Q : IntervalPartition n) (perm : Equiv.Perm (Fin n))
    (hwidth : ∀ i, P.width i = Q.width (perm i)) (flipped : Fin n → Bool) (u v : I) :
    (shuffleOfMin P Q perm hwidth flipped).cdf ![u, v] =
      ∑ i, P.width i * if flipped i then
        max ((P.coord i u : ℝ) + (Q.coord (perm i) v : ℝ) - 1) 0
      else min (P.coord i u : ℝ) (Q.coord (perm i) v : ℝ) := by
  simp only [shuffleOfMin, PatchworkData.cdf_copula, PatchworkData.cdf,
    shuffleData, Matrix.cons_val_zero, Matrix.cons_val_one]
  apply Finset.sum_congr rfl
  intro i _
  split
  · rw [cdf_countermonotonic, max_comm]
    rfl
  · rw [cdf_comonotonic_two]
    rfl

/-- Equal-width straight shuffle, requiring only a positive order and a permutation. -/
noncomputable def uniformShuffleOfMin (n : ℕ) (hn : 0 < n) (perm : Equiv.Perm (Fin n)) :
    Copula 2 :=
  shuffleOfMin (IntervalPartition.uniform n hn) (IntervalPartition.uniform n hn) perm
    (by intro i; simp) (fun _ => false)

@[simp] theorem shuffleOfMin_refl (P : IntervalPartition n) :
    shuffleOfMin P P (Equiv.refl _) (fun _ => rfl) (fun _ => false) = comonotonic 2 := by
  change finiteOrdinalSum P (fun _ => comonotonic 2) = comonotonic 2
  exact finiteOrdinalSum_comonotonic P

end ProbabilityTheory.Copula
