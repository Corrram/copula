import Copula.Rank.Region.XiBlest.Paper.PolynomialCoefficients
import Copula.Rank.Region.XiBlest.Support.HyperbolicCoefficients

/-! # Exact coefficient formulas for slopes greater than one -/

open MeasureTheory ProbabilityTheory Set ProbabilityTheory.Copula.RankRegion.XiBlest.Support
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest

noncomputable def xiFormula (b : ℝ) : ℝ :=
  if b ≤ 1 then 8*b^2*(7-3*b)/105 else
    let g := Real.sqrt ((b-1)/b)
    (183*g-38*b*g-88*b^2*g+112*b^2+48*b^3*g-48*b^3-105*Real.arcosh (Real.sqrt b)/b)/210

noncomputable def nuFormula (b : ℝ) : ℝ :=
  if b ≤ 1 then 4*b*(28-9*b)/105 else
    let g := Real.sqrt ((b-1)/b)
    (87*g/b+250*g-376*b*g+448*b+144*b^2*g-144*b^2-105*Real.arcosh (Real.sqrt b)/b^2)/420

theorem extremal_coefficients_hyperbolic (b : ℝ) (hb : 1 < b) :
    (extremalCopula b (by linarith)).chatterjeeXi =
      (183*Real.sqrt ((b-1)/b)-38*b*Real.sqrt ((b-1)/b)-88*b^2*Real.sqrt ((b-1)/b)+112*b^2+
        48*b^3*Real.sqrt ((b-1)/b)-48*b^3-105*Real.arcosh (Real.sqrt b)/b)/210 ∧
    blestNu (extremalCopula b (by linarith)) =
      (87*Real.sqrt ((b-1)/b)/b+250*Real.sqrt ((b-1)/b)-376*b*Real.sqrt ((b-1)/b)+448*b+
        144*b^2*Real.sqrt ((b-1)/b)-144*b^2-105*Real.arcosh (Real.sqrt b)/b^2)/420 := by
  have hb0 : 0 < b := by linarith
  have hs : 1 < Real.sqrt b := by nlinarith [Real.sq_sqrt hb0.le,Real.sqrt_nonneg b]
  have hsn : Real.sqrt b ≠ 0 := by linarith
  let r : ℝ := 1/Real.sqrt b
  have hr : r ∈ Ioo (0 : ℝ) 1 := ⟨by dsimp [r]; positivity,(div_lt_one (by linarith)).mpr hs⟩
  have hbr : b*r^2=1 := by
    dsimp [r]
    rw [div_pow,one_pow,Real.sq_sqrt hb0.le]
    field_simp
  have hr2 : r^2=1/b := (eq_div_iff hb0.ne').mpr (by nlinarith)
  have hg : 1-r^2=(b-1)/b := by rw [hr2]; field_simp
  have ha : 1/r=Real.sqrt b := by dsimp [r]; field_simp
  constructor
  · change (quadraticBand b _).chatterjeeXi=_
    rw [quadraticBand_xi_tail,xi_hyperbolic_integral b r hb0 hr hbr,hg,ha]
  · rw [extremal_blest_noise,integral_noise_weighted_tail b hb0.le]
    have he : 12*(1/6+4*b/45-b^2/35+(∫ p : I × I,nuTail b |squareDelta p|)/12)-2 =
        4*b*(28-9*b)/105+∫ p : I × I,nuTail b |squareDelta p| := by ring
    rw [he,nu_hyperbolic_integral b r hb0 hr hbr,hg,ha]

/-- Equations (4) and (5), including the b=0 endpoint extension. -/
theorem extremal_coefficients (b : ℝ) (hb : 0 ≤ b) :
    (extremalCopula b hb).chatterjeeXi=xiFormula b ∧ blestNu (extremalCopula b hb)=nuFormula b := by
  by_cases h : b ≤ 1
  · simpa only [xiFormula,nuFormula,ite_eq_left h] using extremal_coefficients_polynomial b ⟨hb,h⟩
  · simpa only [xiFormula,nuFormula,ite_eq_right h] using extremal_coefficients_hyperbolic b (lt_of_not_ge h)

end ProbabilityTheory.Copula.RankRegion.XiBlest
