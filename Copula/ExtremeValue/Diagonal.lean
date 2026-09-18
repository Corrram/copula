/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.ExtremeValue.Basic
import Copula.Diagonal.Power

/-! # Extremal coefficients and diagonal sections of extreme-value copulas

Max-stability alone implies a power diagonal. This yields the extremal
coefficient in `[1,2]` and both tail limits, without requiring a density or
a Pickands representation. See Gudendorf and Segers, *Extreme-Value Copulas*, §4.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem IsExtremeValue.diagonal_unitPower {C : Copula 2} (hC : C.IsExtremeValue)
    (u : I) (r : ℝ) (hr : 0 < r) :
    C.diagonal (unitPower u r hr.le) = C.diagonal u ^ r := by
  simp only [diagonal]
  rw [← hC ![u, u] r hr]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- Every bivariate extreme-value copula has a power diagonal on the closed interval. -/
theorem IsExtremeValue.exists_hasPowerDiagonal {C : Copula 2} (hC : C.IsExtremeValue) :
    ∃ κ : ℝ, C.HasPowerDiagonal κ := by
  let a : I := ⟨3 / 4, by norm_num, by norm_num⟩
  have ha0 : (0 : ℝ) < a := by norm_num [a]
  have ha1 : (a : ℝ) < 1 := by norm_num [a]
  have hd0 : 0 < C.diagonal a := by
    have hb := C.diagonal_lower_bound a
    norm_num [a] at hb
    linarith
  have hd1 : C.diagonal a < 1 := lt_of_le_of_lt (C.diagonal_le a) ha1
  have hla : Real.log (a : ℝ) < 0 := Real.log_neg ha0 ha1
  let κ := Real.log (C.diagonal a) / Real.log (a : ℝ)
  have hκ : 0 < κ := div_pos_of_neg_of_neg (Real.log_neg hd0 hd1) hla
  refine ⟨κ, fun t => ?_⟩
  by_cases ht0 : t = 0
  · simp [ht0, Real.zero_rpow hκ.ne']
  by_cases ht1 : t = 1
  · simp [ht1]
  have htp : (0 : ℝ) < t := lt_of_le_of_ne t.property.1
    (Ne.symm (fun h => ht0 (Subtype.ext h)))
  have htl : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2
    (fun h => ht1 (Subtype.ext h))
  let r := Real.log (t : ℝ) / Real.log (a : ℝ)
  have hr : 0 < r := div_pos_of_neg_of_neg (Real.log_neg htp htl) hla
  have he : unitPower a r hr.le = t := by
    apply Subtype.ext
    change (a : ℝ) ^ r = (t : ℝ)
    rw [Real.rpow_def_of_pos ha0]
    dsimp [r]
    rw [mul_div_cancel₀ _ hla.ne, Real.exp_log htp]
  rw [← he, hC.diagonal_unitPower a r hr, he]
  rw [Real.rpow_def_of_pos hd0, Real.rpow_def_of_pos htp]
  congr 1
  dsimp [r, κ]
  ring

/-- The diagonal exponent, evaluated at one half. For extreme-value copulas it
is the usual extremal coefficient `2 A(1/2)`. -/
noncomputable def extremalCoefficient (C : Copula 2) : ℝ :=
  Real.log (C.diagonal unitHalf) / Real.log (1 / 2 : ℝ)

theorem HasPowerDiagonal.extremalCoefficient_eq {C : Copula 2} {κ : ℝ}
    (h : C.HasPowerDiagonal κ) : C.extremalCoefficient = κ := by
  rw [extremalCoefficient, h]
  change Real.log ((1 / 2 : ℝ) ^ κ) / Real.log (1 / 2 : ℝ) = κ
  rw [Real.log_rpow (by norm_num), mul_div_cancel_right₀ _
    (Real.log_neg (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)).ne]

theorem IsExtremeValue.hasPowerDiagonal {C : Copula 2} (hC : C.IsExtremeValue) :
    C.HasPowerDiagonal C.extremalCoefficient := by
  obtain ⟨κ, hκ⟩ := hC.exists_hasPowerDiagonal
  rwa [hκ.extremalCoefficient_eq]

theorem IsExtremeValue.extremalCoefficient_mem_Icc {C : Copula 2} (hC : C.IsExtremeValue) :
    C.extremalCoefficient ∈ Icc 1 2 := hC.hasPowerDiagonal.mem_Icc

theorem IsExtremeValue.hasUpperTailDependence {C : Copula 2} (hC : C.IsExtremeValue) :
    C.HasUpperTailDependence (2 - C.extremalCoefficient) := hC.hasPowerDiagonal.hasUpperTailDependence

theorem IsExtremeValue.extremalCoefficient_eq_one_iff {C : Copula 2} (hC : C.IsExtremeValue) :
    C.extremalCoefficient = 1 ↔ C = comonotonic 2 := by
  constructor
  · intro he
    exact (hasPowerDiagonal_one_iff C).1 (he ▸ hC.hasPowerDiagonal)
  · intro he
    exact ((hasPowerDiagonal_one_iff C).2 he).extremalCoefficient_eq

/-- All extreme-value copulas except comonotonicity have independent lower tails. -/
theorem IsExtremeValue.hasLowerTailDependence_zero {C : Copula 2} (hC : C.IsExtremeValue)
    (hne : C ≠ comonotonic 2) : C.HasLowerTailDependence 0 := by
  apply hC.hasPowerDiagonal.hasLowerTailDependence_zero
  exact lt_of_le_of_ne hC.extremalCoefficient_mem_Icc.1
    (Ne.symm (mt hC.extremalCoefficient_eq_one_iff.1 hne))

/-- Greater concordance gives a smaller extremal coefficient. -/
theorem LowerOrthantLE.extremalCoefficient_antitone {C D : Copula 2}
    (h : C.LowerOrthantLE D) (hC : C.IsExtremeValue) (hD : D.IsExtremeValue) :
    D.extremalCoefficient ≤ C.extremalCoefficient := by
  have ht := h.upperTailDependence_le hC.hasUpperTailDependence hD.hasUpperTailDependence
  linarith

theorem IsExtremeValue.hasUpperTailDependence_one_iff {C : Copula 2} (hC : C.IsExtremeValue) :
    C.HasUpperTailDependence 1 ↔ C = comonotonic 2 := by
  constructor
  · intro ht
    apply hC.extremalCoefficient_eq_one_iff.1
    have he := hC.hasUpperTailDependence.unique ht
    linarith
  · intro he
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      ((hasPowerDiagonal_one_iff C).2 he).hasUpperTailDependence

end ProbabilityTheory.Copula
