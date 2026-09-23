import Copula.Rank.Region.XiBlest.Support.HyperbolicTailIntegrals

/-! # Closed hyperbolic expressions for both extremal coefficient integrals -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

private theorem radicalMoment_succ (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    radicalMoment r (n+1)=(Real.sqrt (1-r^2)^3+(2*(n : ℝ)+1)*r^2*radicalMoment r n)/(2*(n : ℝ)+4) := by
  have h := radicalMoment_recurrence r hr n
  apply (eq_div_iff (by positivity : 2*(n : ℝ)+4 ≠ 0)).mpr
  linarith

theorem xi_hyperbolic_integral (b r : ℝ) (hb : 0 < b) (hr : r ∈ Ioo (0 : ℝ) 1) (hbr : b*r^2=1) :
    8*b^2*(7-3*b)/105+(∫ p : I × I,xiTail b |squareDelta p|) =
      (183*Real.sqrt (1-r^2)-38*b*Real.sqrt (1-r^2)-88*b^2*Real.sqrt (1-r^2)+112*b^2+
        48*b^3*Real.sqrt (1-r^2)-48*b^3-105*Real.arcosh (1/r)/b)/210 := by
  rw [integral_xiTail_radical b r hb hr hbr,radicalMoment_succ r hr 2,radicalMoment_succ r hr 1,
    radicalMoment_succ r hr 0,radicalMoment_zero r hr]
  have hs : Real.sqrt (1-r^2)^3=(1-r^2)*Real.sqrt (1-r^2) := by
    rw [show Real.sqrt (1-r^2)^3=Real.sqrt (1-r^2)^2*Real.sqrt (1-r^2) by ring,
      Real.sq_sqrt (by nlinarith [hr.1,hr.2])]
  rw [hs]
  have hr2 : r^2=1/b := (eq_div_iff hb.ne').mpr (by nlinarith)
  rw [show r^4=(r^2)^2 by ring,show r^6=(r^2)^3 by ring,hr2]
  norm_num only [Nat.cast_ofNat,Nat.cast_zero]
  field_simp
  ring

theorem nu_hyperbolic_integral (b r : ℝ) (hb : 0 < b) (hr : r ∈ Ioo (0 : ℝ) 1) (hbr : b*r^2=1) :
    4*b*(28-9*b)/105+(∫ p : I × I,nuTail b |squareDelta p|) =
      (87*Real.sqrt (1-r^2)/b+250*Real.sqrt (1-r^2)-376*b*Real.sqrt (1-r^2)+448*b+
        144*b^2*Real.sqrt (1-r^2)-144*b^2-105*Real.arcosh (1/r)/b^2)/420 := by
  rw [integral_nuTail_radical b r hb hr hbr,radicalMoment_succ r hr 2,radicalMoment_succ r hr 1,
    radicalMoment_succ r hr 0,radicalMoment_zero r hr]
  have hs : Real.sqrt (1-r^2)^3=(1-r^2)*Real.sqrt (1-r^2) := by
    rw [show Real.sqrt (1-r^2)^3=Real.sqrt (1-r^2)^2*Real.sqrt (1-r^2) by ring,
      Real.sq_sqrt (by nlinarith [hr.1,hr.2])]
  rw [hs]
  have hr2 : r^2=1/b := (eq_div_iff hb.ne').mpr (by nlinarith)
  rw [show r^4=(r^2)^2 by ring,show r^6=(r^2)^3 by ring,hr2]
  norm_num only [Nat.cast_ofNat,Nat.cast_zero]
  field_simp
  ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
