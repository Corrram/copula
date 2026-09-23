import Copula.Rank.Region.XiBlest.Support.HyperbolicTailReduction
import Copula.Rank.Region.XiBlest.Support.IntegratedSquareGapMoments
import Copula.Rank.Region.XiBlest.Support.QuadraticBandTailCoefficients

/-! # Exact tail integrals in terms of four radical moments -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

private theorem integral_gap_polynomial (x s a b c d : ℝ) :
    (∫ y in (0 : ℝ)..s,a+b*(x^2-y^2)+c*(x^2-y^2)^2+d*(x^2-y^2)^3)=
      a*innerSquareMoment x s 0+b*innerSquareMoment x s 1+c*innerSquareMoment x s 2+d*innerSquareMoment x s 3 := by
  unfold innerSquareMoment
  simp only [pow_zero,pow_one]
  rw [intervalIntegral.integral_add,intervalIntegral.integral_add,intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  · simp; ring
  all_goals exact (by fun_prop : Continuous _).intervalIntegrable 0 s

private theorem integral_inner_polynomial (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) (a b c d : ℝ) :
    (∫ x in r..1,a*innerSquareMoment x (Real.sqrt (x^2-r^2)) 0+
      b*innerSquareMoment x (Real.sqrt (x^2-r^2)) 1+
      c*innerSquareMoment x (Real.sqrt (x^2-r^2)) 2+
      d*innerSquareMoment x (Real.sqrt (x^2-r^2)) 3)=
      a*radicalMoment r 0+b*(2*radicalMoment r 1+r^2*radicalMoment r 0)/3+
      c*(8*radicalMoment r 2+4*r^2*radicalMoment r 1+3*r^4*radicalMoment r 0)/15+
      d*(16*radicalMoment r 3+8*r^2*radicalMoment r 2+6*r^4*radicalMoment r 1+5*r^6*radicalMoment r 0)/35 := by
  have hm := integrated_innerSquareMoment r hr
  rw [intervalIntegral.integral_add,intervalIntegral.integral_add,intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,hm.1,hm.2.1,hm.2.2.1,hm.2.2.2]
  · ring
  all_goals
    apply Continuous.intervalIntegrable
    simp only [innerSquareMoment_zero,innerSquareMoment_one,innerSquareMoment_two,innerSquareMoment_three]
    fun_prop

private theorem potential_tail_reflection (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ p : I × I,f |squareDelta p|) = ∫ p : I × I,f (|(p.1 : ℝ)^2-(p.2 : ℝ)^2|) := by
  have h1 : Integrable (fun p : I × I => f |squareDelta p|) :=
    (by fun_prop : Continuous (fun p : I × I => f |squareDelta p|)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable (fun p : I × I => f (|(p.1 : ℝ)^2-(p.2 : ℝ)^2|)) :=
    (by fun_prop : Continuous (fun p : I × I => f (|(p.1 : ℝ)^2-(p.2 : ℝ)^2|))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ p : I × I,f |squareDelta p| ∂(volume : Measure I).prod volume)=
    ∫ p : I × I,f (|(p.1 : ℝ)^2-(p.2 : ℝ)^2|) ∂(volume : Measure I).prod volume
  rw [integral_prod _ h1,integral_prod _ h2]
  have he (u v : I) : f |squareDelta (u,v)|=f (|(unitInterval.symm u : ℝ)^2-(unitInterval.symm v : ℝ)^2|) := by
    simp only [squareDelta,squarePotential,unitInterval.coe_symm_eq]
    rw [abs_sub_comm]
  simp_rw [he]
  have hin (u : I) := integral_unit_reflection (fun v : I => f (|(unitInterval.symm u : ℝ)^2-(v : ℝ)^2|))
  simp_rw [hin]
  exact integral_unit_reflection (fun u : I => ∫ v : I,f (|(u : ℝ)^2-(v : ℝ)^2|))

private theorem gap_ge_cutoff (r x y : ℝ) (hr : 0 < r) (hx : r ≤ x)
    (hy : y ∈ uIcc (0 : ℝ) (Real.sqrt (x^2-r^2))) : r^2 ≤ x^2-y^2 := by
  rw [uIcc_of_le (Real.sqrt_nonneg _)] at hy
  have hs := Real.sq_sqrt (show 0 ≤ x^2-r^2 by nlinarith)
  nlinarith [hy.1,hy.2,Real.sqrt_nonneg (x^2-r^2)]

theorem integral_xiTail_radical (b r : ℝ) (hb : 0 < b) (hr : r ∈ Ioo (0 : ℝ) 1) (hbr : b*r^2=1) :
    (∫ p : I × I,xiTail b |squareDelta p|) =
      2*(radicalMoment r 0+(-3*b^2)*(8*radicalMoment r 2+4*r^2*radicalMoment r 1+3*r^4*radicalMoment r 0)/15+
        (2*b^3)*(16*radicalMoment r 3+8*r^2*radicalMoment r 2+6*r^4*radicalMoment r 1+5*r^6*radicalMoment r 0)/35) := by
  have hz (t : ℝ) (ht : t ≤ r^2) : xiTail b t=0 := by
    unfold xiTail
    rw [max_eq_left (by nlinarith [mul_le_mul_of_nonneg_left ht hb.le])]
    norm_num
  rw [potential_tail_reflection _ (continuous_xiTail b),square_gap_tail_reduction r hr _ (continuous_xiTail b) hz]
  have he : (∫ x in r..1,∫ y in (0 : ℝ)..Real.sqrt (x^2-r^2),xiTail b (x^2-y^2)) =
      ∫ x in r..1,1*innerSquareMoment x (Real.sqrt (x^2-r^2)) 0+
        0*innerSquareMoment x (Real.sqrt (x^2-r^2)) 1+
        (-3*b^2)*innerSquareMoment x (Real.sqrt (x^2-r^2)) 2+
        (2*b^3)*innerSquareMoment x (Real.sqrt (x^2-r^2)) 3 := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [← integral_gap_polynomial]
    apply intervalIntegral.integral_congr
    intro y hy
    dsimp only
    rw [uIcc_of_le hr.2.le] at hx
    have hg := gap_ge_cutoff r x y hr.1 hx.1 hy
    unfold xiTail
    rw [max_eq_right (by nlinarith [mul_le_mul_of_nonneg_left hg hb.le])]
    ring
  rw [he,integral_inner_polynomial r hr]
  ring

theorem integral_nuTail_radical (b r : ℝ) (hb : 0 < b) (hr : r ∈ Ioo (0 : ℝ) 1) (hbr : b*r^2=1) :
    (∫ p : I × I,nuTail b |squareDelta p|) =
      2*(3*(2*radicalMoment r 1+r^2*radicalMoment r 0)/3+
        (-6*b)*(8*radicalMoment r 2+4*r^2*radicalMoment r 1+3*r^4*radicalMoment r 0)/15+
        (3*b^2)*(16*radicalMoment r 3+8*r^2*radicalMoment r 2+6*r^4*radicalMoment r 1+5*r^6*radicalMoment r 0)/35) := by
  have hz (t : ℝ) (ht : t ≤ r^2) : nuTail b t=0 := by
    unfold nuTail
    rw [max_eq_left (by nlinarith [mul_le_mul_of_nonneg_left ht hb.le])]
    norm_num
  rw [potential_tail_reflection _ (continuous_nuTail b),square_gap_tail_reduction r hr _ (continuous_nuTail b) hz]
  have he : (∫ x in r..1,∫ y in (0 : ℝ)..Real.sqrt (x^2-r^2),nuTail b (x^2-y^2)) =
      ∫ x in r..1,0*innerSquareMoment x (Real.sqrt (x^2-r^2)) 0+
        3*innerSquareMoment x (Real.sqrt (x^2-r^2)) 1+
        (-6*b)*innerSquareMoment x (Real.sqrt (x^2-r^2)) 2+
        (3*b^2)*innerSquareMoment x (Real.sqrt (x^2-r^2)) 3 := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [← integral_gap_polynomial]
    apply intervalIntegral.integral_congr
    intro y hy
    dsimp only
    rw [uIcc_of_le hr.2.le] at hx
    have hg := gap_ge_cutoff r x y hr.1 hx.1 hy
    unfold nuTail
    rw [max_eq_right (by nlinarith [mul_le_mul_of_nonneg_left hg hb.le])]
    ring
  rw [he,integral_inner_polynomial r hr]
  ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
