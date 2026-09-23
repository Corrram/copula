import Copula.Rank.Region.XiBlest.Support.SquaredUniformMoments
import Copula.Rank.Region.XiBlest.Support.HyperbolicMoments

/-! # Reducing symmetric square-gap tails to a single radical integral -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

/-- A continuous function vanishing below r² has only the two symmetric triangular tails. -/
theorem square_gap_tail_reduction (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1)
    (f : ℝ → ℝ) (hf : Continuous f) (hz : ∀ t : ℝ, t ≤ r^2 → f t=0) :
    (∫ p : I × I, f (|(p.1 : ℝ)^2-(p.2 : ℝ)^2|)) =
      2*(∫ x in r..1, ∫ y in (0 : ℝ)..Real.sqrt (x^2-r^2), f (x^2-y^2)) := by
  let g : I × I → ℝ := fun p => f ((p.1 : ℝ)^2-(p.2 : ℝ)^2)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hi := hg.integrable_of_hasCompactSupport (μ := (volume : Measure (I × I)))
    (HasCompactSupport.of_compactSpace _)
  have his : Integrable (fun p : I × I => g p.swap) :=
    (hg.comp continuous_swap).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (p : I × I) : f (|(p.1 : ℝ)^2-(p.2 : ℝ)^2|)=g p+g p.swap := by
    dsimp [g]
    rcases le_total ((p.1 : ℝ)^2) ((p.2 : ℝ)^2) with h | h
    · rw [abs_of_nonpos (by linarith),hz ((p.1 : ℝ)^2-(p.2 : ℝ)^2) (by nlinarith [sq_nonneg r])]
      simp only [zero_add]
      congr 1; ring
    · rw [abs_of_nonneg (by linarith),hz ((p.2 : ℝ)^2-(p.1 : ℝ)^2) (by nlinarith [sq_nonneg r])]
      simp
  simp_rw [he]
  rw [integral_add hi his]
  have hswap : (∫ p : I × I, g p.swap) = ∫ p : I × I, g p := integral_prod_swap g
  rw [hswap,← two_mul]
  congr 1
  let F : ℝ → ℝ := fun x => ∫ y : I, f (x^2-(y : ℝ)^2)
  have hF : Continuous F := by
    have h := continuous_parametric_integral_of_continuous (μ := (volume : Measure I))
      (f := fun x : ℝ => fun y : I => f (x^2-(y : ℝ)^2)) (by fun_prop) isCompact_univ
    change Continuous (fun x : ℝ => ∫ y : I, f (x^2-(y : ℝ)^2))
    simpa only [Measure.restrict_univ] using h
  have hzero : (∫ x in (0 : ℝ)..r, F x)=0 := by
    calc
      _ = ∫ _x in (0 : ℝ)..r, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hr.1.le] at hx
        apply integral_eq_zero_of_ae
        filter_upwards [] with y
        exact hz _ (by nlinarith [hx.1,hx.2,sq_nonneg (y : ℝ)])
      _ = 0 := by simp
  have hinner (x : ℝ) (hx : x ∈ Icc r 1) : F x=
      ∫ y in (0 : ℝ)..Real.sqrt (x^2-r^2),f (x^2-y^2) := by
    have hx0 : 0 ≤ x := hr.1.le.trans hx.1
    have hrad : 0 ≤ x^2-r^2 := by nlinarith [hx.1,hr.1]
    have hs := Real.sq_sqrt hrad
    have hs0 := Real.sqrt_nonneg (x^2-r^2)
    have hs1 : Real.sqrt (x^2-r^2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [hx.2,sq_nonneg r])
    have hcf : Continuous (fun y : ℝ => f (x^2-y^2)) := by fun_prop
    have hright : (∫ y in Real.sqrt (x^2-r^2)..1,f (x^2-y^2))=0 := by
      calc
        _ = ∫ _y in Real.sqrt (x^2-r^2)..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro y hy
          rw [uIcc_of_le hs1] at hy
          exact hz _ (by nlinarith [hy.1])
        _ = 0 := by simp
    dsimp only [F]
    rw [Copula.integral_unitInterval (fun y => f (x^2-y^2)),
      ← intervalIntegral.integral_add_adjacent_intervals (hcf.intervalIntegrable 0 (Real.sqrt (x^2-r^2)))
        (hcf.intervalIntegrable (Real.sqrt (x^2-r^2)) 1),hright,add_zero]
  change (∫ p : I × I, g p ∂(volume : Measure I).prod volume)=_
  rw [integral_prod _ hi]
  change (∫ x : I, F x)=_
  rw [Copula.integral_unitInterval F,← intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable 0 r) (hF.intervalIntegrable r 1),hzero,zero_add]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hr.2.le] at hx
  exact hinner x hx

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
