/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoFootrule.UpperRight
import Copula.Rank.Region.ChainSums

open MeasureTheory
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoFootrule.RightData

open UpperSpline FinitePathCoupling

variable (S : RightData)

noncomputable def phase (k : ℕ) (i : Fin 4) (s : ℝ) : ℝ :=
  (k : ℝ) * period S.N S.v S.w + piecePoint S.N S.v S.w i s

noncomputable def width : Fin 4 → ℝ
  | 0 => S.w
  | 1 => S.N * S.v
  | 2 => S.w
  | 3 => (S.N + 1) * S.v

theorem phase_affine (k : ℕ) (i : Fin 4) (s : ℝ) :
    S.phase k i s = S.phase k i 0 + S.width i * s := by
  fin_cases i <;> simp only [phase, width, piecePoint] <;> ring

theorem integral_piece (f : ℝ → ℝ) (k : ℕ) (i : Fin 4) :
    S.width i * (∫ s : I, f (S.phase k i s)) =
      ∫ x in S.phase k i 0..S.phase k i 1, f x := by
  have hd : S.phase k i 1 - S.phase k i 0 = S.width i := by
    rw [S.phase_affine k i 1]; ring
  convert integral_affine f (S.phase k i 0) (S.phase k i 1) using 1;
    simp only [hd, ← S.phase_affine]

theorem path_density_sum (F : ℕ → Fin 4 → ℝ) :
    (∑ k ∈ Finset.range (S.N + 1), S.w * (F k 0 + F k 2)) +
      (∑ k ∈ Finset.range S.N, (S.N - (k : ℝ)) * S.v * (F k 1 + F k 3)) +
      (∑ k ∈ Finset.range S.N, ((k : ℝ) + 1) * S.v * (F k 3 + F (k + 1) 1)) =
    (∑ k ∈ Finset.range (S.N + 1), (S.w * F k 0 + S.N * S.v * F k 1 + S.w * F k 2)) +
      ∑ k ∈ Finset.range S.N, (S.N + 1) * S.v * F k 3 := by
  have h := weighted_chain_sum S.N (fun k => S.v * F k 1)
  simp only [mul_add, sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_assoc, ← Finset.mul_sum] at h ⊢
  nlinarith only [h]

theorem phase_adjacent (k : ℕ) :
    S.phase k 0 1 = S.phase k 1 0 ∧
    S.phase k 1 1 = S.phase k 2 0 ∧
    S.phase k 2 1 = S.phase k 3 0 ∧
    S.phase k 3 1 = S.phase (k + 1) 0 0 := by
  dsimp [phase, piecePoint, period]
  push_cast
  constructor; · ring
  constructor; · ring
  constructor <;> ring

theorem integral_three (f : ℝ → ℝ) (hf : Continuous f) (k : ℕ) :
    S.w * (∫ s : I, f (S.phase k 0 s)) +
      S.N * S.v * (∫ s : I, f (S.phase k 1 s)) +
      S.w * (∫ s : I, f (S.phase k 2 s)) =
    ∫ x in S.phase k 0 0..S.phase k 2 1, f x := by
  change S.width 0 * _ + S.width 1 * _ + S.width 2 * _ = _
  rw [S.integral_piece, S.integral_piece, S.integral_piece]
  rw [(S.phase_adjacent k).1, (S.phase_adjacent k).2.1]
  rw [intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _),
    intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]

theorem integral_four (f : ℝ → ℝ) (hf : Continuous f) (k : ℕ) :
    (∫ x in S.phase k 0 0..S.phase k 2 1, f x) +
      (S.N + 1) * S.v * (∫ s : I, f (S.phase k 3 s)) =
    ∫ x in S.phase k 0 0..S.phase (k + 1) 0 0, f x := by
  change _ + S.width 3 * _ = _
  rw [S.integral_piece, (S.phase_adjacent k).2.2.1,
    (S.phase_adjacent k).2.2.2,
    intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]

theorem integral_periods (f : ℝ → ℝ) (hf : Continuous f) (m : ℕ) :
    (∑ k ∈ Finset.range m, ∫ x in S.phase k 0 0..S.phase (k + 1) 0 0, f x) =
      ∫ x in 0..S.phase m 0 0, f x := by
  induction m with
  | zero => simp [phase, piecePoint]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih,
      intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]

theorem phase_density_integral (f : ℝ → ℝ) (hf : Continuous f) :
    (∑ k ∈ Finset.range (S.N + 1), S.w * ((∫ s : I, f (S.phase k 0 s)) +
      ∫ s : I, f (S.phase k 2 s))) +
      (∑ k ∈ Finset.range S.N, (S.N - (k : ℝ)) * S.v *
        ((∫ s : I, f (S.phase k 1 s)) + ∫ s : I, f (S.phase k 3 s))) +
      (∑ k ∈ Finset.range S.N, ((k : ℝ) + 1) * S.v *
        ((∫ s : I, f (S.phase k 3 s)) + ∫ s : I, f (S.phase (k + 1) 1 s))) =
    ∫ x in 0..1, f x := by
  rw [S.path_density_sum (fun k i => ∫ s : I, f (S.phase k i s))]
  simp_rw [S.integral_three f hf]
  rw [Finset.sum_range_succ]
  rw [add_right_comm, ← Finset.sum_add_distrib]
  simp_rw [S.integral_four f hf]
  rw [S.integral_periods f hf,
    intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
  have he : S.phase S.N 2 1 = 1 := by
    dsimp [phase, piecePoint]
    nlinarith only [S.end_eq_one]
  rw [he]


theorem symmetric_marginal_sum (j : Fin 2) (f : I → ℝ) :
    (∑ i : S.Index × Bool, S.weight i.1 * ∫ s : I, f (S.symmetricPath i s j)) =
      ∑ i : S.Index, S.weight i * ((∫ s : I, f (S.path i s 0)) +
        ∫ s : I, f (S.path i s 1)) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fintype.sum_bool, symmetricPath, ↓reduceIte, Bool.false_eq_true]
  fin_cases j
  · change S.weight i * (∫ s : I, f (S.path i s 1)) + S.weight i * (∫ s : I, f (S.path i s 0)) = _
    ring
  · change S.weight i * (∫ s : I, f (S.path i s 0)) + S.weight i * (∫ s : I, f (S.path i s 1)) = _
    ring

theorem marginal_integral (j : Fin 2) (f : I → ℝ) (hf : Continuous f) :
    (∑ i : S.Index × Bool, S.weight i.1 * ∫ s : I, f (S.symmetricPath i s j)) =
      ∫ s : I, f s := by
  rw [S.symmetric_marginal_sum]
  have he (u : I) : f u = extend f (u : ℝ) := (extend_coe f u).symm
  simp_rw [he]
  simp only [Fintype.sum_sum_type, weight, path, Matrix.cons_val_zero,
    Matrix.cons_val_one, point]
  change (∑ k : Fin (S.N + 1), S.w * ((∫ s : I, extend f (S.phase k 0 s)) +
      ∫ s : I, extend f (S.phase k 2 s))) +
    ((∑ k : Fin S.N, (S.N - (k : ℝ)) * S.v *
      ((∫ s : I, extend f (S.phase k 1 s)) + ∫ s : I, extend f (S.phase k 3 s))) +
    ∑ k : Fin S.N, ((k : ℝ) + 1) * S.v *
      ((∫ s : I, extend f (S.phase k 3 s)) + ∫ s : I, extend f (S.phase (k + 1) 1 s))) = _
  rw [← add_assoc]
  rw [Fin.sum_univ_eq_sum_range (fun k => S.w *
    ((∫ s : I, extend f (S.phase k 0 s)) + ∫ s : I, extend f (S.phase k 2 s))),
    Fin.sum_univ_eq_sum_range (fun k => (S.N - (k : ℝ)) * S.v *
      ((∫ s : I, extend f (S.phase k 1 s)) + ∫ s : I, extend f (S.phase k 3 s))),
    Fin.sum_univ_eq_sum_range (fun k => ((k : ℝ) + 1) * S.v *
      ((∫ s : I, extend f (S.phase k 3 s)) + ∫ s : I, extend f (S.phase (k + 1) 1 s)))]
  rw [S.phase_density_integral (extend f) (continuous_extend hf)]
  exact (integral_unitInterval (extend f)).symm

/-- The upper-bound transport is a copula, with zero-weight paths permitted. -/
noncomputable def copula : Copula 2 :=
  FinitePathCoupling.copula (fun i : S.Index × Bool => S.weight i.1)
    (fun i => S.weight_nonneg i.1) S.symmetricPath S.continuous_symmetricPath S.marginal_integral

theorem integral_copula {f : (Fin 2 → I) → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂S.copula.toMeasure) =
      ∑ i : S.Index × Bool, S.weight i.1 * ∫ s : I, f (S.symmetricPath i s) :=
  FinitePathCoupling.integral_copula _ _ _ _ _ hf

end ProbabilityTheory.Copula.RankRegion.RhoFootrule.RightData
