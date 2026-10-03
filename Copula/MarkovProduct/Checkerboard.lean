/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.MarkovProduct.Laws
import Copula.Checkerboard
import Copula.Rank.ConditionalCDF

/-! # Markov products of checkerboard copulas

A checkerboard copula with cell masses `A = (aᵢⱼ)` on the grid `P × Q` has the piecewise constant
density `aᵢⱼ / (|Pᵢ| |Qⱼ|)` on the cell `Pᵢ × Qⱼ`. Its conditional distribution functions are
therefore

`∂₁C(s, v) = ∑ᵢ 1_{Pᵢ}(s)/|Pᵢ| · ∑ⱼ aᵢⱼ coordⱼ(v)` for almost every `s`

(`conditionalCDF_checkerboard`), and the Darsow–Nguyen–Olsen product of two checkerboards over a
common middle grid `Q` is again a checkerboard, with the (width-normalized) matrix product of the
cell masses (`checkerboard_markovProduct_checkerboard`):

`(A ⋆ B)ᵢₖ = ∑ⱼ aᵢⱼ bⱼₖ / |Qⱼ|`.

On uniform `n`-grids, with the doubly stochastic matrices `n aᵢⱼ`, this is the ordinary matrix
product (Durante and Sempi 2016, §5.2 and §4.1; Darsow, Nguyen and Olsen 1992). We also record
the transpose of a checkerboard (`transpose_checkerboard`).
-/

open MeasureTheory Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

variable {m n l : ℕ}

namespace IntervalPartition

/-- The normalized indicator `1_{(pᵢ, pᵢ₊₁]} / |Pᵢ|` of a cell: the uniform density on it. -/
noncomputable def cellDensity (P : IntervalPartition n) (i : Fin n) : I → ℝ :=
  (Ioc (P.point i.castSucc) (P.point i.succ)).indicator (fun _ => 1 / P.width i)

theorem cellDensity_nonneg (P : IntervalPartition n) (i : Fin n) (s : I) :
    0 ≤ P.cellDensity i s := by
  unfold cellDensity
  exact indicator_nonneg (fun _ _ => (one_div_pos.mpr (P.width_pos i)).le) s

theorem measurable_cellDensity (P : IntervalPartition n) (i : Fin n) :
    Measurable (P.cellDensity i) :=
  measurable_const.indicator measurableSet_Ioc

theorem integrable_cellDensity (P : IntervalPartition n) (i : Fin n) :
    Integrable (P.cellDensity i) :=
  (integrable_const _).indicator measurableSet_Ioc

/-- The cell density integrates to the clipped local coordinate:
`∫_{[0,u]} 1_{Pᵢ}/|Pᵢ| = coordᵢ(u)`. -/
theorem setIntegral_cellDensity (P : IntervalPartition n) (i : Fin n) (u : I) :
    (∫ t in Iic u, P.cellDensity i t) = P.coord i u := by
  unfold cellDensity
  rw [setIntegral_indicator measurableSet_Ioc, setIntegral_const, inter_comm, Ioc_inter_Iic,
    Measure.real, unitInterval.volume_Ioc, ENNReal.toReal_ofReal', smul_eq_mul]
  have hw := P.width_mul_coord i u
  have hpos := P.width_pos i
  have hab : (P.point i.castSucc : ℝ) ≤ P.point i.succ :=
    (P.strictMono Fin.castSucc_lt_succ).le
  rw [Set.Icc.coe_inf]
  have hc : (P.coord i u : ℝ) = (min (u : ℝ) (P.point i.succ) - min (u : ℝ) (P.point i.castSucc)) /
      P.width i := by
    rw [← hw]; field_simp
  rw [hc, min_comm (P.point i.succ : ℝ)]
  rcases le_total (u : ℝ) (P.point i.castSucc) with h | h
  · rw [min_eq_left h, min_eq_left (h.trans hab), max_eq_right (by linarith)]
    simp
  · rw [min_eq_right h, max_eq_left (by
      rcases le_total (u : ℝ) (P.point i.succ) with h' | h'
      · rw [min_eq_left h']; linarith
      · rw [min_eq_right h']; linarith)]
    field_simp

/-- The total mass of a cell density is one. -/
theorem integral_cellDensity (P : IntervalPartition n) (i : Fin n) :
    (∫ t, P.cellDensity i t) = 1 := by
  have h := P.setIntegral_cellDensity i 1
  have hu : Iic (1 : I) = univ := eq_univ_of_forall fun x => x.2.2
  rw [coord_one, hu, Measure.restrict_univ] at h
  exact_mod_cast h

/-- Distinct cells are disjoint: `1_{Pᵢ} 1_{Pⱼ} / (|Pᵢ||Pⱼ|)` vanishes for `i ≠ j`. -/
theorem cellDensity_mul (P : IntervalPartition n) (i j : Fin n) (s : I) :
    P.cellDensity i s * P.cellDensity j s =
      if i = j then P.cellDensity i s / P.width i else 0 := by
  split_ifs with h
  · subst h
    unfold cellDensity
    by_cases hs : s ∈ Ioc (P.point i.castSucc) (P.point i.succ)
    · simp only [indicator_of_mem hs]; ring
    · simp [indicator_of_notMem hs]
  · unfold cellDensity
    by_cases hi : s ∈ Ioc (P.point i.castSucc) (P.point i.succ)
    · by_cases hj : s ∈ Ioc (P.point j.castSucc) (P.point j.succ)
      · exfalso
        rcases lt_or_gt_of_ne h with hij | hij
        · have : P.point i.succ ≤ P.point j.castSucc :=
            P.strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hij)
          exact absurd (hi.2.trans this) (not_le.mpr hj.1)
        · have : P.point j.succ ≤ P.point i.castSucc :=
            P.strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hij)
          exact absurd (hj.2.trans this) (not_le.mpr hi.1)
      · simp [indicator_of_notMem hj]
    · simp [indicator_of_notMem hi]

end IntervalPartition

namespace CellMass

variable {P : IntervalPartition m} {Q : IntervalPartition n} {R : IntervalPartition l}

/-- The transposed cell masses on the grid `Q × P`. -/
def transpose (A : CellMass P Q) : CellMass Q P where
  mass j i := A.mass i j
  nonneg j i := A.nonneg i j
  row_sum j := A.col_sum j
  col_sum i := A.row_sum i

/-- The width-normalized matrix product `∑ⱼ aᵢⱼ bⱼₖ / |Qⱼ|` of cell masses. -/
noncomputable def mul (A : CellMass P Q) (B : CellMass Q R) : CellMass P R where
  mass i k := ∑ j, A.mass i j * B.mass j k / Q.width j
  nonneg i k := Finset.sum_nonneg fun j _ =>
    div_nonneg (mul_nonneg (A.nonneg i j) (B.nonneg j k)) (Q.width_pos j).le
  row_sum i := by
    rw [Finset.sum_comm]
    have h : ∀ j, ∑ k, A.mass i j * B.mass j k / Q.width j = A.mass i j := by
      intro j
      rw [← Finset.sum_div, ← Finset.mul_sum, B.row_sum, mul_div_assoc,
        div_self (Q.width_pos j).ne', mul_one]
    simp_rw [h, A.row_sum]
  col_sum k := by
    rw [Finset.sum_comm]
    have h : ∀ j, ∑ i, A.mass i j * B.mass j k / Q.width j = B.mass j k := by
      intro j
      rw [← Finset.sum_div, ← Finset.sum_mul, A.col_sum,
        mul_div_cancel_left₀ _ (Q.width_pos j).ne']
    simp_rw [h, B.col_sum]

/-- The transpose of a checkerboard copula is the checkerboard of the transposed masses. -/
theorem transpose_checkerboard (A : CellMass P Q) :
    A.checkerboard.transpose = A.transpose.checkerboard := by
  apply ext_cdf_two
  intro u v
  rw [cdf_transpose, cdf_checkerboard, cdf_checkerboard, Finset.sum_comm]
  simp only [transpose]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro i _
  ring

/-- The conditional distribution functions of a checkerboard copula:
`∂₁C(s,v) = ∑ᵢ 1_{Pᵢ}(s)/|Pᵢ| ∑ⱼ aᵢⱼ coordⱼ(v)` for almost every `s`. -/
theorem conditionalCDF_checkerboard (A : CellMass P Q) (v : I) :
    (fun s => A.checkerboard.conditionalCDF s v) =ᵐ[volume]
      fun s => ∑ i, P.cellDensity i s * ∑ j, A.mass i j * (Q.coord j v : ℝ) := by
  apply conditionalCDF_ae_eq_of_integral
  · exact integrable_finsetSum _ fun i _ => (P.integrable_cellDensity i).mul_const _
  · intro t
    exact Finset.sum_nonneg fun i _ => mul_nonneg (P.cellDensity_nonneg i t)
      (Finset.sum_nonneg fun j _ => mul_nonneg (A.nonneg i j) (Q.coord j v).2.1)
  · intro u
    rw [integral_finsetSum _ fun i _ =>
      ((P.integrable_cellDensity i).mul_const _).integrableOn]
    simp_rw [integral_mul_const, P.setIntegral_cellDensity, cdf_checkerboard, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring

/-- The Markov product of two checkerboard copulas over a common middle grid is the
checkerboard copula of the width-normalized matrix product of their cell masses. -/
theorem checkerboard_markovProduct_checkerboard (A : CellMass P Q) (B : CellMass Q R) :
    A.checkerboard.markovProduct B.checkerboard = (A.mul B).checkerboard := by
  apply ext_cdf_two
  intro u v
  rw [cdf_markovProduct_eq_integral, transpose_checkerboard, cdf_checkerboard]
  set X : Fin n → ℝ := fun j => ∑ i, A.mass i j * (P.coord i u : ℝ) with hX
  set Y : Fin n → ℝ := fun j => ∑ k, B.mass j k * (R.coord k v : ℝ) with hY
  have h : (fun s => A.transpose.checkerboard.conditionalCDF s u *
      B.checkerboard.conditionalCDF s v) =ᵐ[volume]
      fun s => ∑ j, Q.cellDensity j s * (X j * Y j / Q.width j) := by
    filter_upwards [A.transpose.conditionalCDF_checkerboard u,
      B.conditionalCDF_checkerboard v] with s h1 h2
    rw [h1, h2, Finset.sum_mul_sum]
    simp only [transpose]
    have : ∀ j j' : Fin n, Q.cellDensity j s * X j * (Q.cellDensity j' s * Y j') =
        if j = j' then Q.cellDensity j s * (X j * Y j / Q.width j) else 0 := by
      intro j j'
      rw [show Q.cellDensity j s * X j * (Q.cellDensity j' s * Y j') =
        (Q.cellDensity j s * Q.cellDensity j' s) * (X j * Y j') by ring,
        Q.cellDensity_mul j j' s]
      split_ifs with hjj
      · subst hjj; ring
      · ring
    simp only [hX, hY] at this
    simp_rw [this, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rfl
  rw [integral_congr_ae h, integral_finsetSum _ fun j _ =>
    (Q.integrable_cellDensity j).mul_const _]
  simp_rw [integral_mul_const, Q.integral_cellDensity, one_mul]
  simp only [mul, hX, hY, Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
  conv_rhs =>
    arg 2; ext i
    rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs =>
    arg 2; ext j
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro i _
  ring

end CellMass

end ProbabilityTheory.Copula
