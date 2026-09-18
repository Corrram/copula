/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.TailDependence.ExtremeValue

/-! # Rank coefficients determined by power diagonals

Spearman's footrule and Blomqvist's beta depend only on the diagonal. Thus
their closed forms hold for every power-diagonal copula, in particular every
bivariate extreme-value copula, including singular ones.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem HasPowerDiagonal.spearmanFootrule {C : Copula 2} {κ : ℝ}
    (h : C.HasPowerDiagonal κ) : C.spearmanFootrule = 6 / (κ + 1) - 2 := by
  have he : (fun t : I => C.cdf ![t, t]) = fun t : I => (t : ℝ) ^ κ := funext h
  change 6 * (∫ t : I, C.cdf ![t, t]) - 2 = _
  rw [he, integral_unitInterval (fun t : ℝ => t ^ κ),
    integral_rpow (Or.inl (by linarith [h.one_le]))]
  simp only [Real.one_rpow, Real.zero_rpow (show κ + 1 ≠ 0 by linarith [h.one_le]), sub_zero]
  ring

theorem HasPowerDiagonal.blomqvistBeta {C : Copula 2} {κ : ℝ}
    (h : C.HasPowerDiagonal κ) : C.blomqvistBeta = (2 : ℝ) ^ (2 - κ) - 1 := by
  change 4 * C.diagonal unitHalf - 1 = _
  rw [h]
  change 4 * (1 / 2 : ℝ) ^ κ - 1 = _
  rw [Real.div_rpow zero_le_one (by norm_num : (0 : ℝ) ≤ 2), Real.one_rpow,
    Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  norm_num [Real.rpow_two, div_eq_mul_inv]

theorem IsExtremeValue.spearmanFootrule {C : Copula 2} (h : C.IsExtremeValue) :
    C.spearmanFootrule = 6 / (C.extremalCoefficient + 1) - 2 := h.hasPowerDiagonal.spearmanFootrule

theorem IsExtremeValue.blomqvistBeta {C : Copula 2} (h : C.IsExtremeValue) :
    C.blomqvistBeta = (2 : ℝ) ^ (2 - C.extremalCoefficient) - 1 := h.hasPowerDiagonal.blomqvistBeta

theorem spearmanFootrule_marshallOlkin (α β : I) :
    (marshallOlkin α β).spearmanFootrule = 6 / (3 - min (α : ℝ) (β : ℝ)) - 2 := by
  rw [(hasPowerDiagonal_marshallOlkin α β).spearmanFootrule]
  congr 2
  ring

theorem blomqvistBeta_marshallOlkin (α β : I) :
    (marshallOlkin α β).blomqvistBeta = (2 : ℝ) ^ min (α : ℝ) (β : ℝ) - 1 := by
  simpa using (hasPowerDiagonal_marshallOlkin α β).blomqvistBeta

theorem spearmanFootrule_cuadrasAuge (α : I) :
    (cuadrasAuge α).spearmanFootrule = 6 / (3 - (α : ℝ)) - 2 := by
  simpa only [cuadrasAuge, min_self] using spearmanFootrule_marshallOlkin α α

theorem blomqvistBeta_cuadrasAuge (α : I) :
    (cuadrasAuge α).blomqvistBeta = (2 : ℝ) ^ (α : ℝ) - 1 := by
  simpa only [cuadrasAuge, min_self] using blomqvistBeta_marshallOlkin α α

theorem spearmanFootrule_gumbel (θ : ℝ) (hθ : 1 ≤ θ) :
    (gumbel θ hθ).spearmanFootrule = 6 / ((2 : ℝ) ^ θ⁻¹ + 1) - 2 :=
  (hasPowerDiagonal_gumbel θ hθ).spearmanFootrule

theorem blomqvistBeta_gumbel (θ : ℝ) (hθ : 1 ≤ θ) :
    (gumbel θ hθ).blomqvistBeta = (2 : ℝ) ^ (2 - (2 : ℝ) ^ θ⁻¹) - 1 :=
  (hasPowerDiagonal_gumbel θ hθ).blomqvistBeta

theorem spearmanFootrule_tawn (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) :
    (tawn θ hθ α β).spearmanFootrule =
      6 / (3 - (α : ℝ) - (β : ℝ) + ((α : ℝ) ^ θ + (β : ℝ) ^ θ) ^ θ⁻¹) - 2 := by
  rw [(hasPowerDiagonal_tawn θ hθ α β).spearmanFootrule]
  congr 2
  ring

theorem blomqvistBeta_tawn (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) :
    (tawn θ hθ α β).blomqvistBeta =
      (2 : ℝ) ^ ((α : ℝ) + (β : ℝ) - ((α : ℝ) ^ θ + (β : ℝ) ^ θ) ^ θ⁻¹) - 1 := by
  rw [(hasPowerDiagonal_tawn θ hθ α β).blomqvistBeta]
  congr 2
  ring

end ProbabilityTheory.Copula
