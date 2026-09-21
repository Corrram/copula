/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Patchwork.Grid

/-! # Exact grid interpolation by local-copula patchworks -/

open Filter
open scoped unitInterval BigOperators Topology

namespace ProbabilityTheory.Copula

namespace IntervalPartition

variable {n : ℕ}

/-- A clipped coordinate at a grid point is an exact step function. -/
theorem coord_point (P : IntervalPartition n) (i : Fin n) (k : Fin (n + 1)) :
    P.coord i (P.point k) = if i.val < k.val then 1 else 0 := by
  split_ifs with h
  · apply P.coord_of_ge
    exact P.strictMono.monotone (show i.succ ≤ k by exact h)
  · apply P.coord_of_le
    exact P.strictMono.monotone (show k ≤ i.castSucc from Nat.le_of_not_gt h)

/-- Telescoping a prefix without introducing a second finite index type. -/
theorem sum_prefix_differences (f : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    (∑ i : Fin n, if i.val < k.val then f i.succ - f i.castSucc else 0) = f k - f 0 := by
  induction n with
  | zero => fin_cases k; simp
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) k
    · simp
    · rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, Nat.zero_lt_succ, ite_true, Nat.add_lt_add_iff_right]
      change f 1 - f 0 + (∑ i : Fin n, if i.val < k.val then f i.succ.succ - f i.castSucc.succ else 0) = _
      rw [ih (fun i => f i.succ) k]
      change f 1 - f 0 + (f k.succ - f 1) = _
      ring

end IntervalPartition

variable {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}

/-- All local choices interpolate the same cumulative cell probabilities. -/
theorem CellMass.cdf_patchwork_point (A : CellMass P Q) (D : Fin m → Fin n → Copula 2)
    (k : Fin (m + 1)) (l : Fin (n + 1)) :
    (A.patchwork D).cdf ![P.point k, Q.point l] =
      ∑ i, if i.val < k.val then (∑ j, if j.val < l.val then A.mass i j else 0) else 0 := by
  rw [A.cdf_patchwork]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, IntervalPartition.coord_point]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < k.val
  · simp only [hi, ite_true]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val < l.val <;> simp [hj]
  · simp [hi]

/-- A sampled patchwork agrees with the original copula at every grid vertex. -/
theorem cdf_cellMass_patchwork_point (C : Copula 2) (P : IntervalPartition m)
    (Q : IntervalPartition n) (D : Fin m → Fin n → Copula 2)
    (k : Fin (m + 1)) (l : Fin (n + 1)) :
    ((C.cellMass P Q).patchwork D).cdf ![P.point k, Q.point l] =
      C.cdf ![P.point k, Q.point l] := by
  rw [CellMass.cdf_patchwork_point]
  have h (i : Fin m) :
      (∑ j : Fin n, if j.val < l.val then (C.cellMass P Q).mass i j else 0) =
        C.cdf ![P.point i.succ, Q.point l] - C.cdf ![P.point i.castSucc, Q.point l] := by
    have ht := IntervalPartition.sum_prefix_differences
      (fun j => C.cdf ![P.point i.succ, Q.point j] -
        C.cdf ![P.point i.castSucc, Q.point j]) l
    simp only [Q.zero, cdf_two_zero_right, sub_self, sub_zero] at ht
    rw [← ht]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · dsimp [cellMass]; ring
    · rfl
  simp_rw [h]
  rw [IntervalPartition.sum_prefix_differences (fun i => C.cdf ![P.point i, Q.point l]) k]
  simp [P.zero]

@[simp] theorem cdf_checkerboard_point (C : Copula 2) (P : IntervalPartition m)
    (Q : IntervalPartition n) (k : Fin (m + 1)) (l : Fin (n + 1)) :
    (C.checkerboard P Q).cdf ![P.point k, Q.point l] = C.cdf ![P.point k, Q.point l] :=
  cdf_cellMass_patchwork_point C P Q (fun _ _ => independence 2) k l

@[simp] theorem cdf_checkMin_point (C : Copula 2) (P : IntervalPartition m)
    (Q : IntervalPartition n) (k : Fin (m + 1)) (l : Fin (n + 1)) :
    (C.checkMin P Q).cdf ![P.point k, Q.point l] = C.cdf ![P.point k, Q.point l] :=
  cdf_cellMass_patchwork_point C P Q (fun _ _ => comonotonic 2) k l

/-- Sampling any filled grid recovers exactly the original cell probabilities. -/
theorem CellMass.cellMass_patchwork (A : CellMass P Q) (D : Fin m → Fin n → Copula 2)
    (i : Fin m) (j : Fin n) :
    ((A.patchwork D).cellMass P Q).mass i j = A.mass i j := by
  simp only [cellMass, cdf_patchwork_point]
  have h (f : Fin m → ℝ) :
      (∑ k, if k.val < i.succ.val then f k else 0) -
        (∑ k, if k.val < i.castSucc.val then f k else 0) = f i := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp
    · intro k _ hki
      have hne : k.val ≠ i.val := fun h => hki (Fin.ext h)
      by_cases hlt : k.val < i.val
      · simp [hlt, Nat.lt_succ_of_lt hlt]
      · have hgt : i.val < k.val := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hne)
        simp [hlt, show ¬ k.val < i.val + 1 from Nat.not_lt.mpr hgt]
    · simp
  have h' (f : Fin n → ℝ) :
      (∑ k, if k.val < j.succ.val then f k else 0) -
        (∑ k, if k.val < j.castSucc.val then f k else 0) = f j := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      have hne : k.val ≠ j.val := fun h => hkj (Fin.ext h)
      by_cases hlt : k.val < j.val
      · simp [hlt, Nat.lt_succ_of_lt hlt]
      · have hgt : j.val < k.val := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hne)
        simp [hlt, show ¬ k.val < j.val + 1 from Nat.not_lt.mpr hgt]
    · simp
  rw [h]
  rw [show ∀ a b c : ℝ, a - b + c = a - (b - c) from fun _ _ _ => by ring, h, h']

private theorem exists_between_endpoints {r : ℕ} (f : Fin (r + 1) → I) (u : I)
    (hl : f 0 ≤ u) (hr : u < f (Fin.last r)) :
    ∃ i : Fin r, f i.castSucc ≤ u ∧ u < f i.succ := by
  induction r with
  | zero => exact False.elim ((not_lt_of_ge hl) hr)
  | succ r ih =>
    by_cases h : u < f 1
    · exact ⟨0, hl, h⟩
    · obtain ⟨i, hi⟩ := ih (fun i => f i.succ) (le_of_not_gt h) hr
      exact ⟨i.succ, hi⟩

/-- Every unit-interval point is contained in a closed grid cell. -/
theorem IntervalPartition.exists_cell (P : IntervalPartition m) (u : I) :
    ∃ i : Fin m, P.point i.castSucc ≤ u ∧ u ≤ P.point i.succ := by
  by_cases hu : u < 1
  · obtain ⟨i, hi⟩ := exists_between_endpoints P.point u
      (by simp [P.zero]) (by simpa [P.one] using hu)
    exact ⟨i, hi.1, hi.2.le⟩
  · have hu1 : u = 1 := le_antisymm u.property.2 (le_of_not_gt hu)
    subst u
    cases m with
    | zero =>
      have h : (0 : I) = 1 := P.zero.symm.trans (by simpa using P.one)
      exact False.elim (zero_ne_one h)
    | succ r =>
      exact ⟨Fin.last r, (P.point _).property.2, by rw [Fin.succ_last, P.one]⟩

/-- Any local filling has CDF error at most the sum of the containing cell widths. -/
theorem abs_cdf_cellMass_patchwork_sub_le (C : Copula 2) (P : IntervalPartition m)
    (Q : IntervalPartition n) (D : Fin m → Fin n → Copula 2) (u v : I)
    (i : Fin m) (j : Fin n)
    (hu : P.point i.castSucc ≤ u ∧ u ≤ P.point i.succ)
    (hv : Q.point j.castSucc ≤ v ∧ v ≤ Q.point j.succ) :
    |((C.cellMass P Q).patchwork D).cdf ![u, v] - C.cdf ![u, v]| ≤ P.width i + Q.width j := by
  let E := (C.cellMass P Q).patchwork D
  have hl : ![P.point i.castSucc, Q.point j.castSucc] ≤ ![u, v] := by
    intro k; fin_cases k
    · exact hu.1
    · exact hv.1
  have hr : ![u, v] ≤ ![P.point i.succ, Q.point j.succ] := by
    intro k; fin_cases k
    · exact hu.2
    · exact hv.2
  have hEl := E.monotone_cdf hl
  have hEr := E.monotone_cdf hr
  dsimp [E] at hEl hEr
  rw [cdf_cellMass_patchwork_point] at hEl hEr
  have hCl := C.monotone_cdf hl
  have hCr := C.monotone_cdf hr
  have hbound := C.cdf_sub_le_sum_abs
    ![P.point i.succ, Q.point j.succ] ![P.point i.castSucc, Q.point j.castSucc]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hbound
  change _ ≤ |P.width i| + |Q.width j| at hbound
  rw [abs_of_pos (P.width_pos i), abs_of_pos (Q.width_pos j)] at hbound
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Uniform mesh bound, independent of the choice of local copulas. -/
theorem abs_cdf_cellMass_patchwork_sub_le_mesh (C : Copula 2) (P : IntervalPartition m)
    (Q : IntervalPartition n) (D : Fin m → Fin n → Copula 2) (dx dy : ℝ)
    (hx : ∀ i, P.width i ≤ dx) (hy : ∀ j, Q.width j ≤ dy) (u v : I) :
    |((C.cellMass P Q).patchwork D).cdf ![u, v] - C.cdf ![u, v]| ≤ dx + dy := by
  obtain ⟨i, hi⟩ := P.exists_cell u
  obtain ⟨j, hj⟩ := Q.exists_cell v
  exact (abs_cdf_cellMass_patchwork_sub_le C P Q D u v i j hi hj).trans
    (add_le_add (hx i) (hy j))

/-- Checkerboard approximation error on an `m × n` uniform grid. -/
theorem abs_cdf_checkerboard_uniform_sub_le (C : Copula 2) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) (u v : I) :
    |(C.checkerboard (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn)).cdf
      ![u, v] - C.cdf ![u, v]| ≤ 1 / (m : ℝ) + 1 / (n : ℝ) :=
  abs_cdf_cellMass_patchwork_sub_le_mesh C _ _ (fun _ _ => independence 2) _ _
    (fun _ => by simp) (fun _ => by simp) u v

/-- Check-min approximation has the same uniform CDF error guarantee. -/
theorem abs_cdf_checkMin_uniform_sub_le (C : Copula 2) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) (u v : I) :
    |(C.checkMin (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn)).cdf
      ![u, v] - C.cdf ![u, v]| ≤ 1 / (m : ℝ) + 1 / (n : ℝ) :=
  abs_cdf_cellMass_patchwork_sub_le_mesh C _ _ (fun _ _ => comonotonic 2) _ _
    (fun _ => by simp) (fun _ => by simp) u v

/-- Every choice of local copulas converges uniformly as the uniform grid is refined. -/
theorem tendstoUniformly_cellMass_patchwork (C : Copula 2)
    (D : (k : ℕ) → Fin (k + 1) → Fin (k + 1) → Copula 2) :
    TendstoUniformly (fun k : ℕ =>
      ((C.cellMass (IntervalPartition.uniform (k + 1) (Nat.succ_pos k))
        (IntervalPartition.uniform (k + 1) (Nat.succ_pos k))).patchwork (D k)).cdf)
      C.cdf atTop := by
  have h : Tendsto (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he : ∀ᶠ k : ℕ in atTop, 1 / ((k + 1 : ℕ) : ℝ) + 1 / ((k + 1 : ℕ) : ℝ) < ε :=
    (tendsto_order.1 (h.add h)).2 ε (by simpa using hε)
  filter_upwards [he] with k hk u
  rw [Real.dist_eq, abs_sub_comm]
  have hu : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
  have hb := abs_cdf_cellMass_patchwork_sub_le_mesh C
    (IntervalPartition.uniform (k + 1) (Nat.succ_pos k))
    (IntervalPartition.uniform (k + 1) (Nat.succ_pos k)) (D k)
    (1 / ((k + 1 : ℕ) : ℝ)) (1 / ((k + 1 : ℕ) : ℝ))
    (fun _ => by simp) (fun _ => by simp) (u 0) (u 1)
  rw [hu] at hb
  exact hb.trans_lt hk

/-- Checkerboard copulas converge uniformly along refining uniform grids. -/
theorem tendstoUniformly_checkerboard (C : Copula 2) :
    TendstoUniformly (fun k : ℕ =>
      (C.checkerboard (IntervalPartition.uniform (k + 1) (Nat.succ_pos k))
        (IntervalPartition.uniform (k + 1) (Nat.succ_pos k))).cdf) C.cdf atTop :=
  tendstoUniformly_cellMass_patchwork C (fun _ _ _ => independence 2)

/-- Check-min copulas converge uniformly along refining uniform grids. -/
theorem tendstoUniformly_checkMin (C : Copula 2) :
    TendstoUniformly (fun k : ℕ =>
      (C.checkMin (IntervalPartition.uniform (k + 1) (Nat.succ_pos k))
        (IntervalPartition.uniform (k + 1) (Nat.succ_pos k))).cdf) C.cdf atTop :=
  tendstoUniformly_cellMass_patchwork C (fun _ _ _ => comonotonic 2)

end ProbabilityTheory.Copula
