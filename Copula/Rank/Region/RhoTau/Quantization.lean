/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.FiniteMoments
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Logic.Equiv.Fin.Basic

open MeasureTheory Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

noncomputable def quantize (n : ℕ) (x : I) : Fin (n + 1) :=
  ⟨⌊(n : ℝ) * x⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le (by
    nlinarith [x.property.2, Nat.cast_nonneg (α := ℝ) n]))⟩

theorem measurable_quantize (n : ℕ) : Measurable (quantize n) := by
  apply measurable_to_countable'
  intro i
  have he : (quantize n) ⁻¹' {i} = {x : I | ⌊(n : ℝ) * x⌋₊ = i.val} := by
    ext x
    simp [quantize, Fin.ext_iff]
  rw [he]
  exact measurableSet_eq_fun (Nat.measurable_floor.comp (by fun_prop)) measurable_const

theorem eventually_quantize_lt {x y : I} (h : x < y) :
    ∀ᶠ n : ℕ in atTop, quantize n x < quantize n y := by
  have hd : 0 < (y : ℝ) - x := sub_pos.mpr h
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ((y : ℝ) - x))
  have hN' : 1 < (N : ℝ) * ((y : ℝ) - x) := (div_lt_iff₀ hd).mp hN
  apply eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hx' := Nat.floor_le (show 0 ≤ (n : ℝ) * (x : ℝ) by exact mul_nonneg (Nat.cast_nonneg n) x.property.1)
  have hy' := Nat.lt_floor_add_one ((n : ℝ) * y)
  change ⌊(n : ℝ) * x⌋₊ < ⌊(n : ℝ) * y⌋₊
  by_contra hh
  have hh' : (⌊(n : ℝ) * y⌋₊ : ℝ) ≤ ⌊(n : ℝ) * x⌋₊ := by
    exact_mod_cast Nat.le_of_not_gt hh
  nlinarith [mul_nonneg (sub_nonneg.mpr hn') hd.le]

noncomputable def gridCode (n : ℕ) (x : Fin 2 → I) : Fin ((n + 1) * (n + 1)) :=
  finProdFinEquiv (quantize n (x 0), quantize n (x 1))

def gridSwap (n : ℕ) : Equiv.Perm (Fin ((n + 1) * (n + 1))) :=
  finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans finProdFinEquiv)

theorem gridSwap_code (n : ℕ) (x : Fin 2 → I) :
    gridSwap n (gridCode n x) = finProdFinEquiv (quantize n (x 1), quantize n (x 0)) := by
  simp [gridSwap, gridCode]

theorem measurable_gridCode (n : ℕ) : Measurable (gridCode n) := by
  exact (measurable_of_finite finProdFinEquiv).comp
    (((measurable_quantize n).comp (measurable_pi_apply 0)).prodMk
      ((measurable_quantize n).comp (measurable_pi_apply 1)))

theorem finProdFinEquiv_lt {m n : ℕ} (a b : Fin m × Fin n) (h : a.1 < b.1) :
    finProdFinEquiv a < finProdFinEquiv b := by
  change a.2.val + n * a.1.val < b.2.val + n * b.1.val
  have h1 : a.1.val + 1 ≤ b.1.val := h
  have h2 := a.2.isLt
  nlinarith

theorem eventually_grid_order {x y : Fin 2 → I} (h : x 0 ≠ y 0) :
    ∀ᶠ n : ℕ in atTop, orderSign (gridCode n x) (gridCode n y) = orderSign (x 0) (y 0) := by
  rcases lt_or_gt_of_ne h with h | h
  · filter_upwards [eventually_quantize_lt h] with n hn
    have hh := finProdFinEquiv_lt (quantize n (x 0), quantize n (x 1))
      (quantize n (y 0), quantize n (y 1)) hn
    simp [orderSign, gridCode, hh, h]
  · filter_upwards [eventually_quantize_lt h] with n hn
    have hh := finProdFinEquiv_lt (quantize n (y 0), quantize n (y 1))
      (quantize n (x 0), quantize n (x 1)) hn
    simp [orderSign, gridCode, hh, h, not_lt_of_ge h.le, not_lt_of_ge hh.le]

theorem eventually_grid_swap_order {x y : Fin 2 → I} (h : x 1 ≠ y 1) :
    ∀ᶠ n : ℕ in atTop,
      orderSign (gridSwap n (gridCode n x)) (gridSwap n (gridCode n y)) =
        orderSign (x 1) (y 1) := by
  simp only [gridSwap_code]
  simpa only [gridCode, Matrix.cons_val_zero, Matrix.cons_val_one] using
    (eventually_grid_order (x := ![x 1, x 0]) (y := ![y 1, y 0]) h)

end ProbabilityTheory.Copula.RankRegion.RhoTau
