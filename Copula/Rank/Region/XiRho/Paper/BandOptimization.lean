import Copula.Rank.Region.XiRho.Support.DiagonalBand
import Copula.Rank.Region.XiRho.Paper.DiagonalBandUnit

/-! # Global optimization for the normalization-defined diagonal-band family

The explicit piecewise intercept and coefficient formulas for general slopes
are separate obligations. This file constructs all slopes and proves their
optimality using the marginal normalization directly.
-/

open MeasureTheory ProbabilityTheory Set ProbabilityTheory.Copula.RankRegion.XiRho.Support
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiRho

/-- The normalized clamped-affine family, for the entire nonnegative slope range. -/
noncomputable abbrev normalizedBand (b : ℝ) (hb : 0 ≤ b) : Copula 2 := diagonalBand b hb

theorem normalizedBand_conditionalCDF (b : ℝ) (hb : 0 ≤ b) (v : I) :
    (fun u => (normalizedBand b hb).conditionalCDF u v) =ᵐ[volume]
      fun u => unitClamp (bandIntercept b hb v - b * (u : ℝ)) :=
  diagonalBand_conditionalCDF b hb v

theorem normalizedBand_isSI (b : ℝ) (hb : 0 ≤ b) : (normalizedBand b hb).IsSI :=
  diagonalBand_isSI b hb

theorem normalizedBand_support (C : Copula 2) (b : ℝ) (hb : 0 ≤ b) :
    b * C.spearmanRho - C.chatterjeeXi ≤
      b * (normalizedBand b hb).spearmanRho - (normalizedBand b hb).chatterjeeXi :=
  diagonalBand_support C b hb

theorem normalizedBand_support_eq_iff (C : Copula 2) (b : ℝ) (hb : 0 ≤ b) :
    b * C.spearmanRho - C.chatterjeeXi =
      b * (normalizedBand b hb).spearmanRho - (normalizedBand b hb).chatterjeeXi ↔
      C = normalizedBand b hb := diagonalBand_support_eq_iff C b hb

theorem normalizedBand_maximal_rho (C : Copula 2) (b : ℝ) (hb : 0 < b)
    (hx : C.chatterjeeXi ≤ (normalizedBand b hb.le).chatterjeeXi) :
    C.spearmanRho ≤ (normalizedBand b hb.le).spearmanRho :=
  diagonalBand_maximal_rho C b hb hx

theorem normalizedBand_maximal_rho_eq_iff (C : Copula 2) (b : ℝ) (hb : 0 < b)
    (hx : C.chatterjeeXi = (normalizedBand b hb.le).chatterjeeXi) :
    C.spearmanRho = (normalizedBand b hb.le).spearmanRho ↔ C = normalizedBand b hb.le :=
  diagonalBand_maximal_rho_eq_iff C b hb hx

/-- The implicitly normalized slope-one copula is exactly the explicit source copula. -/
theorem normalizedBand_one : normalizedBand 1 (by norm_num) = unitDiagonalBand := by
  apply (unitDiagonalBand_support_eq_iff _).mp
  apply le_antisymm (unitDiagonalBand_support _)
  simpa using normalizedBand_support unitDiagonalBand 1 (by norm_num)

/-- The zero-slope endpoint is independence, without taking an assumed limit. -/
theorem normalizedBand_zero : normalizedBand 0 (by norm_num) = Copula.independence 2 := by
  apply ((normalizedBand 0 (by norm_num)).chatterjeeXi_eq_zero_iff).mp
  have h := normalizedBand_support (Copula.independence 2) 0 (by norm_num)
  have hn := (normalizedBand 0 (by norm_num)).chatterjeeXi_nonneg
  simp only [zero_mul, zero_sub, Copula.chatterjeeXi_independence] at h
  linarith

end ProbabilityTheory.Copula.RankRegion.XiRho
