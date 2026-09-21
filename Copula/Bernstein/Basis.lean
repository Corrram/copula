/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Shape preservation for Bernstein polynomials

The derivative is a nonnegative Bernstein combination of consecutive
coefficient differences. In particular, ordered coefficients give a
monotone function. This is the key step in proving that the tensor
Bernstein approximation of a copula is a copula.
-/

open Polynomial Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.Bernstein

noncomputable section

/-- Polynomial with prescribed Bernstein coefficients. -/
def polynomial (n : ℕ) (f : Fin (n + 1) → ℝ) : ℝ[X] :=
  ∑ k, C (f k) * bernsteinPolynomial ℝ n k

/-- Evaluation of a Bernstein combination on the unit interval. -/
def blend (n : ℕ) (f : Fin (n + 1) → ℝ) (u : I) : ℝ :=
  ∑ k, f k * _root_.bernstein n k u

theorem eval_polynomial (n : ℕ) (f : Fin (n + 1) → ℝ) (u : I) :
    (polynomial n f).eval (u : ℝ) = blend n f u := by
  simp [polynomial, blend, _root_.bernstein, Polynomial.toContinuousMapOn,
    Polynomial.toContinuousMap, eval_finsetSum]

theorem derivative_polynomial (n : ℕ) (f : Fin (n + 2) → ℝ) :
    (polynomial (n + 1) f).derivative =
      C (n + 1 : ℝ) * polynomial n (fun k => f k.succ - f k.castSucc) := by
  have hs : (∑ k : Fin (n + 1), C (f k.succ) * bernsteinPolynomial ℝ n (k.val + 1)) =
      (∑ k : Fin (n + 1), C (f k.castSucc) * bernsteinPolynomial ℝ n k) -
        C (f 0) * bernsteinPolynomial ℝ n 0 := by
    have h := Fin.sum_univ_succ (fun k : Fin (n + 2) => C (f k) * bernsteinPolynomial ℝ n k)
    have h' := Fin.sum_univ_castSucc (fun k : Fin (n + 2) => C (f k) * bernsteinPolynomial ℝ n k)
    simp only [Fin.val_zero, Fin.val_succ] at h
    simp only [Fin.val_castSucc, Fin.val_last,
      bernsteinPolynomial.eq_zero_of_lt ℝ (Nat.lt_succ_self n), mul_zero, add_zero] at h'
    rw [h'] at h
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h.symm)
  simp only [polynomial, derivative_sum, derivative_mul, derivative_C,
    zero_mul, zero_add]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, bernsteinPolynomial.derivative_zero,
    bernsteinPolynomial.derivative_succ_aux, Nat.add_sub_cancel]
  simp only [mul_sub, map_sub]
  simp_rw [mul_left_comm (C (f _)) (↑n + 1)]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, sub_mul]
  rw [hs]
  simp only [map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one]
  ring

theorem blend_mono (n : ℕ) (f : Fin (n + 1) → ℝ) (hf : Monotone f) :
    Monotone (blend n f) := by
  cases n with
  | zero => intro u v huv; simp [blend, _root_.bernstein_apply]
  | succ n =>
    have hm : MonotoneOn (fun x => (polynomial (n + 1) f).eval x) (Icc 0 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (polynomial (n + 1) f).continuous.continuousOn
        (polynomial (n + 1) f).differentiable.differentiableOn
      intro x hx
      rw [Polynomial.deriv, derivative_polynomial, eval_mul, eval_C]
      have hx' : x ∈ Icc (0 : ℝ) 1 := interior_subset hx
      rw [eval_polynomial n _ ⟨x, hx'⟩]
      apply mul_nonneg (by positivity)
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (sub_nonneg.mpr (hf Fin.castSucc_lt_succ.le)) bernstein_nonneg
    intro u v huv
    rw [← eval_polynomial, ← eval_polynomial]
    exact hm u.property v.property huv

@[simp] theorem blend_zero (n : ℕ) (f : Fin (n + 1) → ℝ) : blend n f 0 = f 0 := by
  simp [blend, Fin.sum_univ_succ, _root_.bernstein_apply]

@[simp] theorem blend_one (n : ℕ) (f : Fin (n + 1) → ℝ) :
    blend n f 1 = f (Fin.last n) := by
  simp [blend, Fin.sum_univ_castSucc, _root_.bernstein_apply,
    Nat.sub_eq_zero_iff_le]

theorem blend_const (n : ℕ) (a : ℝ) (u : I) : blend n (fun _ => a) u = a := by
  rw [blend, ← Finset.mul_sum, _root_.bernstein.probability, mul_one]

theorem blend_sub (n : ℕ) (f g : Fin (n + 1) → ℝ) (u : I) :
    blend n (fun k => f k - g k) u = blend n f u - blend n g u := by
  simp [blend, sub_mul, Finset.sum_sub_distrib]

theorem blend_nonneg (n : ℕ) (f : Fin (n + 1) → ℝ) (hf : ∀ k, 0 ≤ f k) (u : I) :
    0 ≤ blend n f u := Finset.sum_nonneg fun k _ => mul_nonneg (hf k) bernstein_nonneg

/-- Bernstein polynomials reproduce the identity for every positive degree. -/
theorem blend_id (n : ℕ) (hn : 0 < n) (u : I) :
    blend n (fun k => (_root_.bernstein.z k : ℝ)) u = u := by
  have h := congrArg (fun p : ℝ[X] => p.eval (u : ℝ)) (bernsteinPolynomial.sum_smul ℝ n)
  simp only [eval_finsetSum, nsmul_eq_mul, eval_mul, eval_natCast, eval_X, Finset.sum_range] at h
  change (∑ k : Fin (n + 1), (k : ℝ) * _root_.bernstein n k u) = (n : ℝ) * u at h
  simp only [blend, _root_.bernstein.z]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, h, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]

end

end ProbabilityTheory.Copula.Bernstein
