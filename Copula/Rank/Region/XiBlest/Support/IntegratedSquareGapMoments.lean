import Copula.Rank.Region.XiBlest.Support.SquareGapInnerMoments

/-! # Integrating the four square-gap moments -/

open MeasureTheory ProbabilityTheory Set

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

theorem integral_radical_polynomial (r a b c d : ℝ) :
    (∫ x in r..1,(a+b*x^2+c*x^4+d*x^6)*Real.sqrt (x^2-r^2)) =
      a*radicalMoment r 0+b*radicalMoment r 1+c*radicalMoment r 2+d*radicalMoment r 3 := by
  have he (x : ℝ) : (a+b*x^2+c*x^4+d*x^6)*Real.sqrt (x^2-r^2) =
      a*Real.sqrt (x^2-r^2)+b*(x^2*Real.sqrt (x^2-r^2))+
      c*(x^4*Real.sqrt (x^2-r^2))+d*(x^6*Real.sqrt (x^2-r^2)) := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_add,intervalIntegral.integral_add,intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  · simp [radicalMoment]
  all_goals exact (by fun_prop : Continuous _).intervalIntegrable r 1

theorem integrated_innerSquareMoment (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
    (∫ x in r..1,innerSquareMoment x (Real.sqrt (x^2-r^2)) 0)=radicalMoment r 0 ∧
    (∫ x in r..1,innerSquareMoment x (Real.sqrt (x^2-r^2)) 1)=
      (2*radicalMoment r 1+r^2*radicalMoment r 0)/3 ∧
    (∫ x in r..1,innerSquareMoment x (Real.sqrt (x^2-r^2)) 2)=
      (8*radicalMoment r 2+4*r^2*radicalMoment r 1+3*r^4*radicalMoment r 0)/15 ∧
    (∫ x in r..1,innerSquareMoment x (Real.sqrt (x^2-r^2)) 3)=
      (16*radicalMoment r 3+8*r^2*radicalMoment r 2+6*r^4*radicalMoment r 1+5*r^6*radicalMoment r 0)/35 := by
  have hp (x : ℝ) (hx : x ∈ uIcc r 1) := innerSquareMoment_radical r x
    (by rw [uIcc_of_le hr.2.le] at hx; nlinarith [hx.1,hr.1])
  refine ⟨?_,?_,?_,?_⟩
  · simp_rw [innerSquareMoment_zero]
    simp [radicalMoment]
  · have he : (∫ x in r..1,innerSquareMoment x (Real.sqrt (x^2-r^2)) 1)=
        ∫ x in r..1,(r^2+2*x^2+0*x^4+0*x^6)*Real.sqrt (x^2-r^2)/3 := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [(hp x hx).2.1]
      ring
    rw [he,intervalIntegral.integral_div,integral_radical_polynomial]
    ring
  · have he : (∫ x in r..1,innerSquareMoment x (Real.sqrt (x^2-r^2)) 2)=
        ∫ x in r..1,(3*r^4+(4*r^2)*x^2+8*x^4+0*x^6)*Real.sqrt (x^2-r^2)/15 := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [(hp x hx).2.2.1]
      ring
    rw [he,intervalIntegral.integral_div,integral_radical_polynomial]
    ring
  · have he : (∫ x in r..1,innerSquareMoment x (Real.sqrt (x^2-r^2)) 3)=
        ∫ x in r..1,(5*r^6+(6*r^4)*x^2+(8*r^2)*x^4+16*x^6)*Real.sqrt (x^2-r^2)/35 := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [(hp x hx).2.2.2]
      ring
    rw [he,intervalIntegral.integral_div,integral_radical_polynomial]
    ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
