import Copula.Rank.Region.XiBlest.Support.RampIntegrals
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-! # Radical moments underlying the hyperbolic coefficient branch -/

open MeasureTheory ProbabilityTheory Set

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

private theorem sqrt_scaled {r x : ℝ} (hr : 0 < r) (hx : r < x) :
    Real.sqrt ((x/r)^2-1)=Real.sqrt (x^2-r^2)/r := by
  have he : (x/r)^2-1=(x^2-r^2)/r^2 := by field_simp
  rw [he,Real.sqrt_div (by nlinarith : 0 ≤ x^2-r^2),Real.sqrt_sq hr.le]

theorem hasDerivAt_arcosh_scaled {r x : ℝ} (hr : 0 < r) (hx : r < x) :
    HasDerivAt (fun t : ℝ => Real.arcosh (t/r)) (1/Real.sqrt (x^2-r^2)) x := by
  have hp : 0 < x^2-r^2 := by nlinarith
  have hs : Real.sqrt (x^2-r^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have h := (Real.hasDerivAt_arcosh (show x/r ∈ Ioi 1 from (one_lt_div hr).mpr hx)).comp x
    ((hasDerivAt_id x).div_const r)
  convert! h using 1
  rw [sqrt_scaled hr hx]
  field_simp

theorem hasDerivAt_sqrt_square_sub {r x : ℝ} (hr : 0 < r) (hx : r < x) :
    HasDerivAt (fun t : ℝ => Real.sqrt (t^2-r^2)) (x/Real.sqrt (x^2-r^2)) x := by
  have hp : 0 < x^2-r^2 := by nlinarith
  have h := (((hasDerivAt_id x).pow 2).sub_const (r^2)).sqrt hp.ne'
  convert! h using 1
  simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.add_one_sub_one,pow_one]
  ring

theorem hasDerivAt_hyperbolic_primitive {r x : ℝ} (hr : 0 < r) (hx : r < x) :
    HasDerivAt (fun t : ℝ => (t*Real.sqrt (t^2-r^2)-r^2*Real.arcosh (t/r))/2)
      (Real.sqrt (x^2-r^2)) x := by
  have hp : 0 < x^2-r^2 := by nlinarith
  have hs := Real.sq_sqrt hp.le
  have hn : Real.sqrt (x^2-r^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have h := (((hasDerivAt_id x).mul (hasDerivAt_sqrt_square_sub hr hx)).sub
    ((hasDerivAt_arcosh_scaled hr hx).const_mul (r^2))).div_const 2
  convert! h using 1
  simp only [id_eq]
  field_simp
  nlinarith

noncomputable def radicalMoment (r : ℝ) (k : ℕ) : ℝ :=
  ∫ x in r..1, x^(2*k)*Real.sqrt (x^2-r^2)

theorem radicalMoment_zero (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
    radicalMoment r 0=(Real.sqrt (1-r^2)-r^2*Real.arcosh (1/r))/2 := by
  have hc : ContinuousOn (fun t : ℝ => (t*Real.sqrt (t^2-r^2)-r^2*Real.arcosh (t/r))/2) (Icc r 1) := by
    apply ContinuousOn.div_const
    apply ContinuousOn.sub (by fun_prop)
    apply ContinuousOn.const_mul
    apply Real.continuousOn_arcosh.comp (by fun_prop)
    intro x hx
    exact (one_le_div hr.1).mpr hx.1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.2.le hc
    (fun x hx => hasDerivAt_hyperbolic_primitive hr.1 hx.1)
    ((show Continuous (fun x : ℝ => Real.sqrt (x^2-r^2)) by fun_prop).intervalIntegrable r 1)
  unfold radicalMoment
  simp only [Nat.mul_zero,pow_zero,one_mul]
  rw [he]
  simp [hr.1.ne']

theorem hasDerivAt_radical_recurrence {r x : ℝ} (hr : 0 < r) (hx : r < x) (n : ℕ) :
    HasDerivAt (fun t : ℝ => t^(2*n+1)*Real.sqrt (t^2-r^2)^3)
      ((2*(n : ℝ)+4)*x^(2*(n+1))*Real.sqrt (x^2-r^2)-
        (2*(n : ℝ)+1)*r^2*x^(2*n)*Real.sqrt (x^2-r^2)) x := by
  have hp : 0 < x^2-r^2 := by nlinarith
  have hs := Real.sq_sqrt hp.le
  have hn : Real.sqrt (x^2-r^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have h := ((hasDerivAt_id x).pow (2*n+1)).mul ((hasDerivAt_sqrt_square_sub hr hx).pow 3)
  convert! h using 1
  simp only [Pi.pow_apply,id_eq,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,
    show 2*n+1-1=2*n by omega,show 3-1=2 by omega]
  field_simp
  rw [show 2*(n+1)=2*n+2 by omega,pow_add,pow_add]
  simp only [pow_one]
  rw [hs]
  ring

theorem radicalMoment_recurrence (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    (2*(n : ℝ)+4)*radicalMoment r (n+1)-(2*(n : ℝ)+1)*r^2*radicalMoment r n =
      Real.sqrt (1-r^2)^3 := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.2.le
    (show ContinuousOn (fun t : ℝ => t^(2*n+1)*Real.sqrt (t^2-r^2)^3) (Icc r 1) by fun_prop)
    (fun x hx => hasDerivAt_radical_recurrence hr.1 hx.1 n)
    ((show Continuous (fun x : ℝ => (2*(n : ℝ)+4)*x^(2*(n+1))*Real.sqrt (x^2-r^2)-
      (2*(n : ℝ)+1)*r^2*x^(2*n)*Real.sqrt (x^2-r^2)) by fun_prop).intervalIntegrable r 1)
  have hi (k : ℕ) : IntervalIntegrable (fun x : ℝ => x^(2*k)*Real.sqrt (x^2-r^2)) volume r 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x^(2*k)*Real.sqrt (x^2-r^2))).intervalIntegrable r 1
  have hid (x : ℝ) : (2*(n : ℝ)+4)*x^(2*(n+1))*Real.sqrt (x^2-r^2)-
      (2*(n : ℝ)+1)*r^2*x^(2*n)*Real.sqrt (x^2-r^2) =
      (2*(n : ℝ)+4)*(x^(2*(n+1))*Real.sqrt (x^2-r^2))-
      ((2*(n : ℝ)+1)*r^2)*(x^(2*n)*Real.sqrt (x^2-r^2)) := by ring
  simp_rw [hid] at he
  rw [intervalIntegral.integral_sub ((hi (n+1)).const_mul _) ((hi n).const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at he
  unfold radicalMoment
  simpa only [one_pow,one_mul,sub_self,Real.sqrt_zero,zero_pow (by decide : 3 ≠ 0),mul_zero,sub_zero] using he

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
