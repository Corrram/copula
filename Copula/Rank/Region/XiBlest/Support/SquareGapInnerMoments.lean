import Copula.Rank.Region.XiBlest.Support.HyperbolicMoments

/-! # Polynomial inner integrals on a square-gap tail -/

open MeasureTheory ProbabilityTheory Set

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

noncomputable def innerSquareMoment (x s : ℝ) (k : ℕ) : ℝ := ∫ y in (0 : ℝ)..s,(x^2-y^2)^k

theorem innerSquareMoment_zero (x s : ℝ) : innerSquareMoment x s 0=s := by
  simp [innerSquareMoment]

theorem innerSquareMoment_one (x s : ℝ) : innerSquareMoment x s 1=x^2*s-s^3/3 := by
  have hd (y : ℝ) : HasDerivAt (fun y : ℝ => x^2*y-y^3/3) (x^2-y^2) y := by
    convert! ((hasDerivAt_id y).const_mul (x^2)).sub (((hasDerivAt_id y).pow 3).div_const 3) using 1
    simp only [id_eq,Nat.cast_ofNat]; ring
  unfold innerSquareMoment
  simp only [pow_one]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
    ((by fun_prop : Continuous (fun y : ℝ => x^2-y^2)).intervalIntegrable 0 s)]
  ring

theorem innerSquareMoment_two (x s : ℝ) : innerSquareMoment x s 2=x^4*s-(2/3)*x^2*s^3+s^5/5 := by
  have hd (y : ℝ) : HasDerivAt (fun y : ℝ => x^4*y-(2/3)*x^2*y^3+y^5/5) ((x^2-y^2)^2) y := by
    convert! (((hasDerivAt_id y).const_mul (x^4)).sub
      (((hasDerivAt_id y).pow 3).const_mul ((2/3)*x^2))).add (((hasDerivAt_id y).pow 5).div_const 5) using 1
    simp only [id_eq,Nat.cast_ofNat]; ring
  unfold innerSquareMoment
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
    ((by fun_prop : Continuous (fun y : ℝ => (x^2-y^2)^2)).intervalIntegrable 0 s)]
  ring

theorem innerSquareMoment_three (x s : ℝ) :
    innerSquareMoment x s 3=x^6*s-x^4*s^3+(3/5)*x^2*s^5-s^7/7 := by
  have hd (y : ℝ) : HasDerivAt (fun y : ℝ => x^6*y-x^4*y^3+(3/5)*x^2*y^5-y^7/7) ((x^2-y^2)^3) y := by
    convert! ((((hasDerivAt_id y).const_mul (x^6)).sub
      (((hasDerivAt_id y).pow 3).const_mul (x^4))).add
      (((hasDerivAt_id y).pow 5).const_mul ((3/5)*x^2))).sub (((hasDerivAt_id y).pow 7).div_const 7) using 1
    simp only [id_eq,Nat.cast_ofNat]; ring
  unfold innerSquareMoment
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
    ((by fun_prop : Continuous (fun y : ℝ => (x^2-y^2)^3)).intervalIntegrable 0 s)]
  ring

theorem innerSquareMoment_radical (r x : ℝ) (h : 0 ≤ x^2-r^2) :
    innerSquareMoment x (Real.sqrt (x^2-r^2)) 0=Real.sqrt (x^2-r^2) ∧
    innerSquareMoment x (Real.sqrt (x^2-r^2)) 1=(2*x^2+r^2)*Real.sqrt (x^2-r^2)/3 ∧
    innerSquareMoment x (Real.sqrt (x^2-r^2)) 2=(8*x^4+4*r^2*x^2+3*r^4)*Real.sqrt (x^2-r^2)/15 ∧
    innerSquareMoment x (Real.sqrt (x^2-r^2)) 3=(16*x^6+8*r^2*x^4+6*r^4*x^2+5*r^6)*Real.sqrt (x^2-r^2)/35 := by
  let s := Real.sqrt (x^2-r^2)
  have hs : s^2=x^2-r^2 := Real.sq_sqrt h
  have h3 : s^3=(x^2-r^2)*s := by rw [show s^3=s^2*s by ring,hs]
  have h5 : s^5=(x^2-r^2)^2*s := by rw [show s^5=(s^2)^2*s by ring,hs]
  have h7 : s^7=(x^2-r^2)^3*s := by rw [show s^7=(s^2)^3*s by ring,hs]
  refine ⟨innerSquareMoment_zero _ _,?_,?_,?_⟩
  · rw [innerSquareMoment_one]
    change x^2*s-s^3/3=_
    rw [h3]
    ring
  · rw [innerSquareMoment_two]
    change x^4*s-(2/3)*x^2*s^3+s^5/5=_
    rw [h3,h5]
    ring
  · rw [innerSquareMoment_three]
    change x^6*s-x^4*s^3+(3/5)*x^2*s^5-s^7/7=_
    rw [h3,h5,h7]
    ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
