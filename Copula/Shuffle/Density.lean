/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Shuffle.Weights
import Copula.Patchwork.Approximation
import Copula.Topology.UniformDistance

/-! # Shuffles of `M` are dense in the bivariate copulas

This file formalizes Nelsen, *An Introduction to Copulas*, 2nd ed., Theorem 3.2.2
(Mikusiński, Sherwood and Taylor, 1992): for every copula `C` and every `ε > 0` there is a
straight shuffle of `M` whose CDF is uniformly within `ε` of `C`.

The construction follows the classical proof. Fix a partition `P` of `[0,1]` into `n` cells
and let `m i j` be the `C`-mass of the cell `P_i × P_j` (a `CellMass P P`). Split the vertical
strip `P_i` into consecutive pieces of lengths `m i 0, m i 1, …` and the horizontal strip `P_j`
into consecutive pieces of lengths `m 0 j, m 1 j, …`; the piece `(i, j)` of the first strip is
sent by a translation onto the piece `(i, j)` of the second one. In the terminology of
`Copula.Shuffle.Weights` the source order of the pieces is lexicographic in `(i, j)` and the
target order is lexicographic in `(j, i)`; zero-mass pieces are discarded automatically.

The resulting straight shuffle `A.shuffle` puts mass `m i j` into every cell, so it agrees with
`C` at all grid vertices (`cdf_gridShuffle_point`); both CDFs are monotone and Lipschitz, which
gives `|S(u,v) - C(u,v)| ≤ 2/n` on the uniform grid (`abs_cdf_gridShuffle_uniform_sub_le`).

## Main results

* `CellMass.shuffle`, `cdf_cellMass_shuffle_point`: exact grid interpolation by a shuffle.
* `abs_cdf_sub_le_of_eq_on_grid`: two copulas that agree on a grid are close.
* `uniformCDFDistance_gridShuffle_le`: `d∞(S_n, C) ≤ 2/n`.
* `tendstoUniformly_gridShuffle`: uniform convergence along refining uniform grids.
* `exists_isStraightShuffleOfMin_uniformCDFDistance_lt`: Nelsen, Theorem 3.2.2.
* `dense_isStraightShuffleOfMin`, `dense_isShuffleOfMin`: density in the uniform metric
  `uniformMetricSpace 2`.
-/

open Filter Set
open scoped unitInterval BigOperators Topology

namespace ProbabilityTheory.Copula

/-! ### Copulas agreeing on a grid -/

section Grid

variable {m n : ℕ}

/-- Two copulas whose CDFs agree at all vertices of a grid differ by at most the mesh sizes. -/
theorem abs_cdf_sub_le_of_eq_on_grid (S C : Copula 2) (P : IntervalPartition m)
    (Q : IntervalPartition n)
    (h : ∀ k l, S.cdf ![P.point k, Q.point l] = C.cdf ![P.point k, Q.point l])
    (dx dy : ℝ) (hx : ∀ i, P.width i ≤ dx) (hy : ∀ j, Q.width j ≤ dy) (u v : I) :
    |S.cdf ![u, v] - C.cdf ![u, v]| ≤ dx + dy := by
  obtain ⟨i, hu⟩ := P.exists_cell u
  obtain ⟨j, hv⟩ := Q.exists_cell v
  have hl : ![P.point i.castSucc, Q.point j.castSucc] ≤ ![u, v] := by
    intro k; fin_cases k
    · exact hu.1
    · exact hv.1
  have hr : ![u, v] ≤ ![P.point i.succ, Q.point j.succ] := by
    intro k; fin_cases k
    · exact hu.2
    · exact hv.2
  have hSl := S.monotone_cdf hl
  have hSr := S.monotone_cdf hr
  rw [h] at hSl hSr
  have hCl := C.monotone_cdf hl
  have hCr := C.monotone_cdf hr
  have hbound := C.cdf_sub_le_sum_abs
    ![P.point i.succ, Q.point j.succ] ![P.point i.castSucc, Q.point j.castSucc]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hbound
  change _ ≤ |P.width i| + |Q.width j| at hbound
  rw [abs_of_pos (P.width_pos i), abs_of_pos (Q.width_pos j)] at hbound
  have := hx i
  have := hy j
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Grid

/-! ### Lexicographic offsets of the pieces -/

section Offsets

variable {n : ℕ}

/-- The lexicographic rank of the cell `(i, j)` among the `n × n` cells (`i` is the major key). -/
def lexRank (q : Fin n × Fin n) : ℕ := (finProdFinEquiv q : Fin (n * n)).val

theorem lexRank_eq (q : Fin n × Fin n) : lexRank q = q.2.val + n * q.1.val := rfl

/-- The total mass of the cells lexicographically before `(i, j)`. -/
def lexOffset (m : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ q : Fin n × Fin n, if lexRank q < lexRank (i, j) then m q.1 q.2 else 0

theorem lt_lexRank_of_fst_lt {q p : Fin n × Fin n} (h : q.1 < p.1) : lexRank q < lexRank p := by
  rw [lexRank_eq, lexRank_eq]
  have h1 : q.1.val + 1 ≤ p.1.val := h
  have h2 := q.2.isLt
  nlinarith

theorem fst_le_of_lexRank_le {q p : Fin n × Fin n} (h : lexRank q ≤ lexRank p) : q.1 ≤ p.1 := by
  by_contra hlt
  exact absurd h (not_le.mpr (lt_lexRank_of_fst_lt (lt_of_not_ge hlt)))

variable {P : IntervalPartition n} (m : Fin n → Fin n → ℝ) (hm0 : ∀ i j, 0 ≤ m i j)
  (hrow : ∀ i, ∑ j, m i j = P.width i)

include hrow in
/-- Summing the rows before a threshold gives the partition point. -/
theorem sum_rows_lt (k : Fin (n + 1)) :
    (∑ q : Fin n × Fin n, if q.1.val < k.val then m q.1 q.2 else 0) = P.point k := by
  rw [Fintype.sum_prod_type]
  have h := IntervalPartition.sum_prefix_differences (fun l => (P.point l : ℝ)) k
  rw [P.zero, Set.Icc.coe_zero, sub_zero] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rw [hrow]; rfl
  · simp

include hm0 hrow in
theorem point_castSucc_le_lexOffset (i j : Fin n) :
    (P.point i.castSucc : ℝ) ≤ lexOffset m i j := by
  rw [← sum_rows_lt m hrow i.castSucc]
  apply Finset.sum_le_sum
  intro q _
  by_cases h : q.1.val < i.castSucc.val
  · simp only [h, lt_lexRank_of_fst_lt (p := (i, j)) h, ite_true, le_refl]
  · simp only [h, ite_false]
    split_ifs
    exacts [hm0 _ _, le_rfl]

include hm0 hrow in
theorem lexOffset_add_le_point_succ (i j : Fin n) :
    lexOffset m i j + m i j ≤ P.point i.succ := by
  rw [← sum_rows_lt m hrow i.succ]
  have hsplit : lexOffset m i j + m i j =
      ∑ q : Fin n × Fin n, if lexRank q ≤ lexRank (i, j) then m q.1 q.2 else 0 := by
    have hk : m i j = ∑ q : Fin n × Fin n, if q = (i, j) then m q.1 q.2 else 0 := by simp
    rw [lexOffset, hk, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q = (i, j)
    · subst hq; simp
    · have hne : lexRank q ≠ lexRank (i, j) := fun h =>
        hq (finProdFinEquiv.injective (Fin.ext h))
      by_cases hlt : lexRank q < lexRank (i, j)
      · simp [hlt, hlt.le, hq]
      · simp [hlt, hq, show ¬ lexRank q ≤ lexRank (i, j) by omega]
  rw [hsplit]
  apply Finset.sum_le_sum
  intro q _
  by_cases h : lexRank q ≤ lexRank (i, j)
  · have h' : q.1.val < i.succ.val := by
      have := fst_le_of_lexRank_le (p := (i, j)) h
      simp only [Fin.val_succ]
      exact Nat.lt_succ_of_le this
    simp only [h, h', ite_true, le_refl]
  · simp only [h, ite_false]
    split_ifs
    exacts [hm0 _ _, le_rfl]

include hm0 hrow in
/-- At a grid point the clipped length of a piece is all or nothing. -/
theorem clipLength_point_sub_lexOffset (k : Fin (n + 1)) (i j : Fin n) :
    clipLength ((P.point k : ℝ) - lexOffset m i j) (m i j) =
      if i.val < k.val then m i j else 0 := by
  split_ifs with h
  · apply clipLength_of_le _ (hm0 i j)
    have h1 := lexOffset_add_le_point_succ m hm0 hrow i j
    have h2 : (P.point i.succ : ℝ) ≤ P.point k := P.strictMono.monotone (show i.succ ≤ k from h)
    linarith
  · apply clipLength_of_nonpos _ _ (hm0 i j)
    have h1 := point_castSucc_le_lexOffset m hm0 hrow i j
    have h2 : (P.point k : ℝ) ≤ P.point i.castSucc :=
      P.strictMono.monotone (show k ≤ i.castSucc from Nat.le_of_not_gt h)
    linarith

end Offsets

/-! ### The shuffle of a matrix of cell masses -/

namespace CellMass

variable {n : ℕ} {P : IntervalPartition n}

/-- The masses listed in lexicographic order of the cells. -/
def lexWeights (A : CellMass P P) (k : Fin (n * n)) : ℝ :=
  A.mass (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

theorem lexWeights_nonneg (A : CellMass P P) (k : Fin (n * n)) : 0 ≤ A.lexWeights k :=
  A.nonneg _ _

theorem sum_lexWeights (A : CellMass P P) : ∑ k, A.lexWeights k = 1 := by
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [lexWeights, Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [A.row_sum]
  exact P.sum_width

/-- The permutation of the cells from lexicographic `(i, j)` order to lexicographic `(j, i)`
order. -/
def transposeRank (n : ℕ) : Equiv.Perm (Fin (n * n)) :=
  finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans finProdFinEquiv)

theorem transposeRank_apply (q : Fin n × Fin n) :
    transposeRank n (finProdFinEquiv q) = finProdFinEquiv (q.2, q.1) := by
  simp only [transposeRank, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodComm_apply]
  rfl

/-- The straight shuffle of `M` that puts the mass `A.mass i j` into the cell `P_i × P_j`
(Nelsen, proof of Theorem 3.2.2). -/
noncomputable def shuffle (A : CellMass P P) : Copula 2 :=
  weightShuffle A.lexWeights A.lexWeights_nonneg A.sum_lexWeights (transposeRank n)

theorem isStraightShuffleOfMin_shuffle (A : CellMass P P) : A.shuffle.IsStraightShuffleOfMin :=
  isStraightShuffleOfMin_weightShuffle _ _ _ _

theorem prefixSum_lexWeights (A : CellMass P P) (q : Fin n × Fin n) :
    prefixSum A.lexWeights (finProdFinEquiv q).val = lexOffset A.mass q.1 q.2 := by
  simp only [prefixSum, lexOffset]
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp [lexWeights, lexRank]

theorem targetOffset_lexWeights (A : CellMass P P) (q : Fin n × Fin n) :
    targetOffset A.lexWeights (transposeRank n) (finProdFinEquiv q) =
      lexOffset (fun j i => A.mass i j) q.2 q.1 := by
  rw [targetOffset_eq, ← Equiv.sum_comp finProdFinEquiv, lexOffset,
    ← Equiv.sum_comp (Equiv.prodComm (Fin n) (Fin n))]
  simp [transposeRank_apply, lexWeights, lexRank]

/-- The shuffle of a matrix of cell masses has the prescribed cumulative masses at every grid
vertex. -/
theorem cdf_shuffle_point (A : CellMass P P) (k l : Fin (n + 1)) :
    A.shuffle.cdf ![P.point k, P.point l] =
      ∑ i, if i.val < k.val then (∑ j, if j.val < l.val then A.mass i j else 0) else 0 := by
  rw [shuffle, cdf_weightShuffle, ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  have hrowT : ∀ j, ∑ i, (fun j i => A.mass i j) j i = P.width j := A.col_sum
  simp only [prefixSum_lexWeights, targetOffset_lexWeights]
  have hw (j : Fin n) : A.lexWeights (finProdFinEquiv (i, j)) = A.mass i j := by
    simp [lexWeights]
  simp_rw [hw]
  simp_rw [clipLength_point_sub_lexOffset A.mass A.nonneg A.row_sum k i]
  have hT (j : Fin n) :
      clipLength ((P.point l : ℝ) - lexOffset (fun j i => A.mass i j) j i) (A.mass i j) =
        if j.val < l.val then A.mass i j else 0 :=
    clipLength_point_sub_lexOffset (fun j i => A.mass i j) (fun j i => A.nonneg i j) hrowT l j i
  simp_rw [hT]
  by_cases hik : i.val < k.val
  · simp only [hik, ite_true]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · exact min_self _
    · exact min_eq_right (A.nonneg i j)
  · simp only [hik, ite_false]
    apply Finset.sum_eq_zero
    intro j _
    split_ifs
    · exact min_eq_left (A.nonneg i j)
    · exact min_self _

end CellMass

/-! ### Grid shuffles of a copula -/

variable {n : ℕ}

/-- The straight shuffle of `M` carrying the `C`-mass of every cell of the grid `P × P`. -/
noncomputable def gridShuffle (C : Copula 2) (P : IntervalPartition n) : Copula 2 :=
  (C.cellMass P P).shuffle

theorem isStraightShuffleOfMin_gridShuffle (C : Copula 2) (P : IntervalPartition n) :
    (C.gridShuffle P).IsStraightShuffleOfMin :=
  CellMass.isStraightShuffleOfMin_shuffle _

theorem isShuffleOfMin_gridShuffle (C : Copula 2) (P : IntervalPartition n) :
    (C.gridShuffle P).IsShuffleOfMin :=
  (C.isStraightShuffleOfMin_gridShuffle P).isShuffleOfMin

/-- The grid shuffle agrees with `C` at every vertex of the grid. -/
theorem cdf_gridShuffle_point (C : Copula 2) (P : IntervalPartition n) (k l : Fin (n + 1)) :
    (C.gridShuffle P).cdf ![P.point k, P.point l] = C.cdf ![P.point k, P.point l] := by
  rw [gridShuffle, CellMass.cdf_shuffle_point, ← cdf_checkMin_point C P P k l, checkMin,
    CellMass.checkMin, CellMass.cdf_patchwork_point]

/-- The CDF error of a grid shuffle is at most twice the mesh. -/
theorem abs_cdf_gridShuffle_sub_le (C : Copula 2) (P : IntervalPartition n) (δ : ℝ)
    (hδ : ∀ i, P.width i ≤ δ) (u v : I) :
    |(C.gridShuffle P).cdf ![u, v] - C.cdf ![u, v]| ≤ 2 * δ := by
  rw [two_mul]
  exact abs_cdf_sub_le_of_eq_on_grid _ C P P (cdf_gridShuffle_point C P) δ δ hδ hδ u v

/-- On the uniform grid with `n` cells, the grid shuffle is within `2/n` of `C`. -/
theorem abs_cdf_gridShuffle_uniform_sub_le (C : Copula 2) (hn : 0 < n) (u v : I) :
    |(C.gridShuffle (IntervalPartition.uniform n hn)).cdf ![u, v] - C.cdf ![u, v]| ≤
      2 / (n : ℝ) := by
  have h := abs_cdf_gridShuffle_sub_le C (IntervalPartition.uniform n hn) (1 / (n : ℝ))
    (fun i => by simp) u v
  rwa [mul_one_div] at h

theorem uniformCDFDistance_gridShuffle_le (C : Copula 2) (hn : 0 < n) :
    (C.gridShuffle (IntervalPartition.uniform n hn)).uniformCDFDistance C ≤ 2 / (n : ℝ) := by
  apply (uniformCDFDistance_le_iff _ _ _).2
  intro x
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  rw [hx]
  exact abs_cdf_gridShuffle_uniform_sub_le C hn _ _

/-- Grid shuffles along refining uniform grids converge uniformly to `C`. -/
theorem tendsto_uniformCDFDistance_gridShuffle (C : Copula 2) :
    Tendsto (fun k : ℕ =>
      (C.gridShuffle (IntervalPartition.uniform (k + 1) k.succ_pos)).uniformCDFDistance C)
      atTop (𝓝 0) := by
  have h : Tendsto (fun k : ℕ => 2 / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := h1.const_mul 2
    simp only [mul_zero] at h2
    refine h2.congr fun k => ?_
    push_cast
    ring
  refine squeeze_zero (fun k => uniformCDFDistance_nonneg _ _) (fun k => ?_) h
  exact uniformCDFDistance_gridShuffle_le C _

theorem tendstoUniformly_gridShuffle (C : Copula 2) :
    TendstoUniformly (fun k : ℕ =>
      (C.gridShuffle (IntervalPartition.uniform (k + 1) k.succ_pos)).cdf) C.cdf atTop :=
  (tendsto_uniformCDFDistance_iff _ C atTop).1 (tendsto_uniformCDFDistance_gridShuffle C)

/-- **Nelsen, Theorem 3.2.2** (Mikusiński–Sherwood–Taylor): every bivariate copula is
uniformly approximated by straight shuffles of `M`. -/
theorem exists_isStraightShuffleOfMin_uniformCDFDistance_lt (C : Copula 2) {ε : ℝ}
    (hε : 0 < ε) : ∃ S : Copula 2, S.IsStraightShuffleOfMin ∧ S.uniformCDFDistance C < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / ε)
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_trans (by positivity) hn
    exact_mod_cast this
  refine ⟨C.gridShuffle (IntervalPartition.uniform n hn0),
    C.isStraightShuffleOfMin_gridShuffle _, ?_⟩
  refine (uniformCDFDistance_gridShuffle_le C hn0).trans_lt ?_
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [div_lt_iff₀ hnpos]
  rw [div_lt_iff₀ hε] at hn
  linarith

/-- Pointwise form of Nelsen, Theorem 3.2.2. -/
theorem exists_isStraightShuffleOfMin_abs_cdf_sub_lt (C : Copula 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Copula 2, S.IsStraightShuffleOfMin ∧ ∀ u v : I, |S.cdf ![u, v] - C.cdf ![u, v]| < ε := by
  obtain ⟨S, hS, hd⟩ := exists_isStraightShuffleOfMin_uniformCDFDistance_lt C hε
  exact ⟨S, hS, fun u v => (S.abs_cdf_sub_le_uniformCDFDistance C _).trans_lt hd⟩

/-- Straight shuffles of `M` are dense in the bivariate copulas for the uniform metric. -/
theorem dense_isStraightShuffleOfMin :
    letI := uniformMetricSpace 2
    Dense {S : Copula 2 | S.IsStraightShuffleOfMin} := by
  let _ := uniformMetricSpace 2
  rw [Metric.dense_iff]
  intro C r hr
  obtain ⟨S, hS, hd⟩ := exists_isStraightShuffleOfMin_uniformCDFDistance_lt C hr
  exact ⟨S, Metric.mem_ball.2 hd, hS⟩

/-- Shuffles of `M` are dense in the bivariate copulas for the uniform metric. -/
theorem dense_isShuffleOfMin :
    letI := uniformMetricSpace 2
    Dense {S : Copula 2 | S.IsShuffleOfMin} := by
  let _ := uniformMetricSpace 2
  exact dense_isStraightShuffleOfMin.mono fun _ h => IsStraightShuffleOfMin.isShuffleOfMin h

/-- Every bivariate copula is the uniform limit of a sequence of straight shuffles of `M`. -/
theorem exists_seq_isStraightShuffleOfMin_tendstoUniformly (C : Copula 2) :
    ∃ S : ℕ → Copula 2, (∀ k, (S k).IsStraightShuffleOfMin) ∧
      TendstoUniformly (fun k => (S k).cdf) C.cdf atTop :=
  ⟨fun k => C.gridShuffle (IntervalPartition.uniform (k + 1) k.succ_pos),
    fun _ => C.isStraightShuffleOfMin_gridShuffle _, tendstoUniformly_gridShuffle C⟩

end ProbabilityTheory.Copula
