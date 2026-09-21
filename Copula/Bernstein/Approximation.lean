/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Bernstein.Basic
import Mathlib.Analysis.Real.Sqrt

/-! # Quantitative Bernstein copula approximation -/

open Filter
open scoped unitInterval BigOperators Topology

namespace ProbabilityTheory.Copula

open Bernstein

/-- Mean absolute grid displacement is bounded by the binomial standard deviation. -/
theorem bernstein_displacement_le (n : ℕ) (hn : 0 < n) (u : I) :
    blend n (fun k => |(u : ℝ) - _root_.bernstein.z k|) u ≤
      Real.sqrt ((u : ℝ) * (1 - u) / n) := by
  apply Real.le_sqrt_of_sq_le
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ) Finset.univ
    (r := fun k : Fin (n + 1) => |(u : ℝ) - _root_.bernstein.z k| * _root_.bernstein n k u)
    (f := fun k : Fin (n + 1) => ((u : ℝ) - _root_.bernstein.z k) ^ 2 * _root_.bernstein n k u)
    (g := fun k : Fin (n + 1) => _root_.bernstein n k u)
    (fun _ _ => mul_nonneg (sq_nonneg _) bernstein_nonneg)
    (fun _ _ => bernstein_nonneg)
    (fun k _ => by rw [mul_pow, sq_abs]; exact le_of_eq (by ring))
  simpa only [blend, _root_.bernstein.probability,
    _root_.bernstein.variance (Nat.ne_of_gt hn), mul_one] using h

/-- Pointwise error controlled by the sum of coordinate binomial standard deviations. -/
theorem abs_bernsteinCDF_sub_le (C : Copula 2) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (u v : I) : |C.bernsteinCDF m n u v - C.cdf ![u, v]| ≤
      Real.sqrt ((u : ℝ) * (1 - u) / m) + Real.sqrt ((v : ℝ) * (1 - v) / n) := by
  have he : C.bernsteinCDF m n u v - C.cdf ![u, v] =
      ∑ i : Fin (m + 1), ∑ j : Fin (n + 1),
        (C.cdf ![_root_.bernstein.z i, _root_.bernstein.z j] - C.cdf ![u, v]) *
          _root_.bernstein m i u * _root_.bernstein n j v := by
    rw [bernsteinCDF_eq_sum]
    simp only [sub_mul, Finset.sum_sub_distrib]
    simp only [mul_assoc, ← Finset.mul_sum, _root_.bernstein.probability, mul_one]
  rw [he]
  calc
    _ ≤ ∑ i : Fin (m + 1), ∑ j : Fin (n + 1),
        |C.cdf ![_root_.bernstein.z i, _root_.bernstein.z j] - C.cdf ![u, v]| *
          _root_.bernstein m i u * _root_.bernstein n j v := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      simpa only [abs_mul, abs_of_nonneg (bernstein_nonneg (n := m)),
        abs_of_nonneg (bernstein_nonneg (n := n))] using
        Finset.abs_sum_le_sum_abs (s := Finset.univ)
          (fun j : Fin (n + 1) =>
            (C.cdf ![_root_.bernstein.z i, _root_.bernstein.z j] - C.cdf ![u, v]) *
              _root_.bernstein m i u * _root_.bernstein n j v)
    _ ≤ ∑ i : Fin (m + 1), ∑ j : Fin (n + 1),
        (|(u : ℝ) - _root_.bernstein.z i| + |(v : ℝ) - _root_.bernstein.z j|) *
          _root_.bernstein m i u * _root_.bernstein n j v := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      apply mul_le_mul_of_nonneg_right _ bernstein_nonneg
      apply mul_le_mul_of_nonneg_right _ bernstein_nonneg
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, abs_sub_comm] using
        C.abs_cdf_sub_le_sum_abs ![_root_.bernstein.z i, _root_.bernstein.z j] ![u, v]
    _ = blend m (fun i => |(u : ℝ) - _root_.bernstein.z i|) u +
        blend n (fun j => |(v : ℝ) - _root_.bernstein.z j|) v := by
      simp only [add_mul, Finset.sum_add_distrib]
      congr 1
      · simp only [mul_assoc, ← Finset.mul_sum, _root_.bernstein.probability, mul_one, blend]
      · rw [Finset.sum_comm]
        simp only [← Finset.sum_mul, ← Finset.mul_sum, _root_.bernstein.probability, mul_one, blend]
    _ ≤ _ := add_le_add (bernstein_displacement_le m hm u) (bernstein_displacement_le n hn v)

/-- A bound independent of the evaluation point; hence an explicit uniform approximation rate. -/
theorem abs_bernsteinCDF_sub_le_uniform (C : Copula 2) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (u v : I) : |C.bernsteinCDF m n u v - C.cdf ![u, v]| ≤
      Real.sqrt (1 / (4 * (m : ℝ))) + Real.sqrt (1 / (4 * (n : ℝ))) := by
  apply (C.abs_bernsteinCDF_sub_le m n hm hn u v).trans
  apply add_le_add
  all_goals
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ((u : ℝ) - 1 / 2), sq_nonneg ((v : ℝ) - 1 / 2)]

/-- Bernstein copulas converge uniformly to the original copula as both degrees increase. -/
theorem tendstoUniformly_bernstein (C : Copula 2) :
    TendstoUniformly (fun k : ℕ => (C.bernstein (k + 1) (k + 1)
      (Nat.succ_pos k) (Nat.succ_pos k)).cdf) C.cdf atTop := by
  have ht : Tendsto (fun k : ℕ => Real.sqrt (1 / (4 * ((k + 1 : ℕ) : ℝ)))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 4)
    have he (k : ℕ) : (1 / 4 : ℝ) * (1 / ((k : ℝ) + 1)) = 1 / (4 * ((k + 1 : ℕ) : ℝ)) := by
      simp only [div_mul_div_comm, one_mul, Nat.cast_add, Nat.cast_one]
    simp_rw [he] at h
    simpa using h.sqrt
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have ht' := ht.add ht
  have he : ∀ᶠ k : ℕ in atTop,
      Real.sqrt (1 / (4 * ((k + 1 : ℕ) : ℝ))) +
        Real.sqrt (1 / (4 * ((k + 1 : ℕ) : ℝ))) < ε :=
    (tendsto_order.1 ht').2 ε (by simpa using hε)
  filter_upwards [he] with k hk u
  rw [Real.dist_eq, abs_sub_comm, cdf_bernstein]
  have hu : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
  have hb := C.abs_bernsteinCDF_sub_le_uniform (k + 1) (k + 1)
    (Nat.succ_pos k) (Nat.succ_pos k) (u 0) (u 1)
  rw [hu] at hb
  exact hb.trans_lt hk

end ProbabilityTheory.Copula
