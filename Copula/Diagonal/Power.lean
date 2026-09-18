/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.TailDependence.Derivative
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Power diagonal sections

The power-diagonal property does not assume max-stability. Its exponent lies
in `[1,2]`, determines both tail coefficients, and equals one exactly for `M`.
-/

open Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

/-- A copula with diagonal section `δ(t) = t^κ`, including the endpoints. -/
def HasPowerDiagonal (C : Copula 2) (κ : ℝ) : Prop :=
  ∀ t : I, C.diagonal t = (t : ℝ) ^ κ

theorem HasPowerDiagonal.one_le {C : Copula 2} {κ : ℝ} (h : C.HasPowerDiagonal κ) :
    1 ≤ κ := by
  by_contra hn
  have he := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) (lt_of_not_ge hn)
  rw [Real.rpow_one] at he
  have hb := C.diagonal_le unitHalf
  rw [h] at hb
  exact (not_lt_of_ge hb) he

theorem HasPowerDiagonal.hasUpperTailDependence {C : Copula 2} {κ : ℝ}
    (h : C.HasPowerDiagonal κ) : C.HasUpperTailDependence (2 - κ) := by
  apply hasUpperTailDependence_of_hasDerivWithinAt (f := fun t : ℝ => t ^ κ) (fun t => (h t).symm)
  simpa using (Real.hasDerivAt_rpow_const (x := 1) (p := κ) (Or.inl one_ne_zero)).hasDerivWithinAt

theorem HasPowerDiagonal.mem_Icc {C : Copula 2} {κ : ℝ} (h : C.HasPowerDiagonal κ) :
    κ ∈ Icc 1 2 :=
  ⟨h.one_le, by linarith [h.hasUpperTailDependence.mem_Icc.1]⟩

theorem HasPowerDiagonal.hasLowerTailDependence_zero {C : Copula 2} {κ : ℝ}
    (h : C.HasPowerDiagonal κ) (hκ : 1 < κ) : C.HasLowerTailDependence 0 := by
  have hc : Continuous (fun t : I => (t : ℝ) ^ (κ - 1)) :=
    continuous_subtype_val.rpow_const (fun _ => Or.inr (by linarith))
  have ht : Tendsto (fun t : I => (t : ℝ) ^ (κ - 1)) (𝓝[>] (0 : I)) (𝓝 0) := by
    simpa [Real.zero_rpow (show κ - 1 ≠ 0 by linarith)] using
      (hc.tendsto (0 : I)).mono_left (show 𝓝[>] (0 : I) ≤ 𝓝 (0 : I) from nhdsWithin_le_nhds)
  apply ht.congr'
  filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < t)] with t ht
  rw [lowerTailRatio, h, Real.rpow_sub_one (ne_of_gt (show (0 : ℝ) < t from ht))]

theorem hasPowerDiagonal_one_iff (C : Copula 2) :
    C.HasPowerDiagonal 1 ↔ C = comonotonic 2 := by
  simpa only [HasPowerDiagonal, Real.rpow_one] using C.diagonal_eq_id_iff

theorem HasPowerDiagonal.hasLowerTailDependence {C : Copula 2} {κ : ℝ}
    (h : C.HasPowerDiagonal κ) : C.HasLowerTailDependence (if κ = 1 then 1 else 0) := by
  split_ifs with hκ
  · subst κ
    apply hasLowerTailDependence_of_hasDerivWithinAt (f := fun t : ℝ => t)
      (fun t => by simpa using (h t).symm)
    exact (hasDerivAt_id (0 : ℝ)).hasDerivWithinAt
  · exact h.hasLowerTailDependence_zero (lt_of_le_of_ne h.one_le (Ne.symm hκ))

theorem HasPowerDiagonal.unique {C : Copula 2} {a b : ℝ}
    (ha : C.HasPowerDiagonal a) (hb : C.HasPowerDiagonal b) : a = b := by
  have h := ha.hasUpperTailDependence.unique hb.hasUpperTailDependence
  linarith

end ProbabilityTheory.Copula
