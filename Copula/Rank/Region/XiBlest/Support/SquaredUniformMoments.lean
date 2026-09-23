import Copula.Rank.Region.XiBlest.Support.RampIntegrals

/-! # Difference moments of two squared uniform variables -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

private theorem integral_abs_square_diff_cube (x : I) :
    (∫ y : I, |(x : ℝ)^2-(y : ℝ)^2|^3) =
      1/7-(3/5)*(x : ℝ)^2+(x : ℝ)^4-(x : ℝ)^6+(32/35)*(x : ℝ)^7 := by
  rw [Copula.integral_unitInterval (fun y => |(x : ℝ)^2-y^2|^3)]
  have hc : Continuous (fun y : ℝ => |(x : ℝ)^2-y^2|^3) := by fun_prop
  have hl : (∫ y in (0 : ℝ)..(x : ℝ), |(x : ℝ)^2-y^2|^3) = (16/35)*(x : ℝ)^7 := by
    have he : (∫ y in (0 : ℝ)..(x : ℝ), |(x : ℝ)^2-y^2|^3) =
        ∫ y in (0 : ℝ)..(x : ℝ), (x : ℝ)^6-3*(x : ℝ)^4*y^2+3*(x : ℝ)^2*y^4-y^6 := by
      apply intervalIntegral.integral_congr
      intro y hy
      dsimp only
      rw [uIcc_of_le x.property.1] at hy
      rw [abs_of_nonneg (by nlinarith [hy.1,hy.2,x.property.1])]
      ring
    rw [he]
    have hd (y : ℝ) : HasDerivAt (fun y : ℝ => (x : ℝ)^6*y-(x : ℝ)^4*y^3+
        (3/5)*(x : ℝ)^2*y^5-y^7/7)
        ((x : ℝ)^6-3*(x : ℝ)^4*y^2+3*(x : ℝ)^2*y^4-y^6) y := by
      convert! ((((hasDerivAt_id y).const_mul ((x : ℝ)^6)).sub
        (((hasDerivAt_id y).pow 3).const_mul ((x : ℝ)^4))).add
        (((hasDerivAt_id y).pow 5).const_mul ((3/5)*(x : ℝ)^2))).sub
        (((hasDerivAt_id y).pow 7).div_const 7) using 1
      simp only [id_eq,Nat.cast_ofNat]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
      ((show Continuous (fun y : ℝ => (x : ℝ)^6-3*(x : ℝ)^4*y^2+3*(x : ℝ)^2*y^4-y^6) by fun_prop).intervalIntegrable _ _)]
    ring
  have hr : (∫ y in (x : ℝ)..1, |(x : ℝ)^2-y^2|^3) =
      1/7-(3/5)*(x : ℝ)^2+(x : ℝ)^4-(x : ℝ)^6+(16/35)*(x : ℝ)^7 := by
    have he : (∫ y in (x : ℝ)..1, |(x : ℝ)^2-y^2|^3) =
        ∫ y in (x : ℝ)..1, y^6-3*(x : ℝ)^2*y^4+3*(x : ℝ)^4*y^2-(x : ℝ)^6 := by
      apply intervalIntegral.integral_congr
      intro y hy
      dsimp only
      rw [uIcc_of_le x.property.2] at hy
      rw [abs_of_nonpos (by nlinarith [hy.1,x.property.1])]
      ring
    rw [he]
    have hd (y : ℝ) : HasDerivAt (fun y : ℝ => y^7/7-(3/5)*(x : ℝ)^2*y^5+
        (x : ℝ)^4*y^3-(x : ℝ)^6*y)
        (y^6-3*(x : ℝ)^2*y^4+3*(x : ℝ)^4*y^2-(x : ℝ)^6) y := by
      convert! (((((hasDerivAt_id y).pow 7).div_const 7).sub
        (((hasDerivAt_id y).pow 5).const_mul ((3/5)*(x : ℝ)^2))).add
        (((hasDerivAt_id y).pow 3).const_mul ((x : ℝ)^4))).sub
        ((hasDerivAt_id y).const_mul ((x : ℝ)^6)) using 1
      simp only [id_eq,Nat.cast_ofNat]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
      ((show Continuous (fun y : ℝ => y^6-3*(x : ℝ)^2*y^4+3*(x : ℝ)^4*y^2-(x : ℝ)^6) by fun_prop).intervalIntegrable _ _)]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 x)
    (hc.intervalIntegrable x 1),hl,hr]
  ring

theorem integral_square_diff_cube :
    (∫ x : I, ∫ y : I, |(x : ℝ)^2-(y : ℝ)^2|^3) = 4/35 := by
  simp_rw [integral_abs_square_diff_cube]
  rw [integral_add,integral_sub,integral_add,integral_sub,integral_const_mul,integral_const_mul,
    Copula.integral_unit_pow,Copula.integral_unit_pow,Copula.integral_unit_pow,Copula.integral_unit_pow]
  · norm_num
  all_goals exact Copula.integrable_continuous_unit volume (by fun_prop)

theorem integral_square_diff_sq :
    (∫ x : I, ∫ y : I, ((x : ℝ)^2-(y : ℝ)^2)^2) = 8/45 := by
  have he (x : I) : (∫ y : I, ((x : ℝ)^2-(y : ℝ)^2)^2) = (x : ℝ)^4-(2/3)*(x : ℝ)^2+1/5 := by
    have hp : (fun y : I => ((x : ℝ)^2-(y : ℝ)^2)^2) =
        fun y : I => (x : ℝ)^4-(2*(x : ℝ)^2)*(y : ℝ)^2+(y : ℝ)^4 := by funext y; ring
    rw [hp,integral_add,integral_sub,integral_const_mul,Copula.integral_unit_pow,Copula.integral_unit_pow]
    · simp; ring
    all_goals exact Copula.integrable_continuous_unit volume (by fun_prop)
  simp_rw [he]
  rw [integral_add,integral_sub,integral_const_mul,Copula.integral_unit_pow,Copula.integral_unit_pow]
  · norm_num
  all_goals exact Copula.integrable_continuous_unit volume (by fun_prop)

noncomputable def squarePotential (u : I) : ℝ := (1-(u : ℝ))^2

noncomputable def squareDelta (p : I × I) : ℝ := squarePotential p.2-squarePotential p.1

@[fun_prop] theorem continuous_squarePotential : Continuous squarePotential := by
  unfold squarePotential; fun_prop

@[fun_prop] theorem continuous_squareDelta : Continuous squareDelta := by
  unfold squareDelta; fun_prop

theorem squarePotential_mem (u : I) : squarePotential u ∈ Icc (0 : ℝ) 1 :=
  ⟨sq_nonneg _,by unfold squarePotential; nlinarith [u.property.1,u.property.2]⟩

theorem squareDelta_abs_le (p : I × I) : |squareDelta p| ≤ 1 := by
  unfold squareDelta
  exact abs_le.mpr ⟨by linarith [(squarePotential_mem p.1).2,(squarePotential_mem p.2).1],
    by linarith [(squarePotential_mem p.1).1,(squarePotential_mem p.2).2]⟩

private theorem pair_reflection (f : I → I → ℝ) :
    (∫ u : I, ∫ v : I, f (unitInterval.symm u) (unitInterval.symm v)) = ∫ u : I, ∫ v : I, f u v := by
  have he (u : I) := integral_unit_reflection (f (unitInterval.symm u))
  simp_rw [he]
  exact integral_unit_reflection (fun u => ∫ v : I, f u v)

theorem integral_squareDelta_cube : (∫ p : I × I, |squareDelta p|^3) = 4/35 := by
  have hi : Integrable (fun p : I × I => |squareDelta p|^3) :=
    (by fun_prop : Continuous (fun p : I × I => |squareDelta p|^3)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ p : I × I, |squareDelta p|^3 ∂(volume : Measure I).prod volume)=_
  rw [integral_prod _ hi]
  have he (u v : I) : |squareDelta (u,v)|^3 = |(unitInterval.symm u : ℝ)^2-(unitInterval.symm v : ℝ)^2|^3 := by
    simp only [squareDelta,squarePotential,unitInterval.coe_symm_eq]
    rw [abs_sub_comm]
  simp_rw [he]
  rw [pair_reflection (fun u v : I => |(u : ℝ)^2-(v : ℝ)^2|^3),integral_square_diff_cube]

theorem integral_squareDelta_sq : (∫ p : I × I, squareDelta p ^ 2) = 8/45 := by
  have hi : Integrable (fun p : I × I => squareDelta p ^ 2) :=
    (by fun_prop : Continuous (fun p : I × I => squareDelta p ^ 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ p : I × I, squareDelta p^2 ∂(volume : Measure I).prod volume)=_
  rw [integral_prod _ hi]
  have he (u v : I) : squareDelta (u,v)^2 = ((unitInterval.symm u : ℝ)^2-(unitInterval.symm v : ℝ)^2)^2 := by
    simp only [squareDelta,squarePotential,unitInterval.coe_symm_eq]
    ring
  simp_rw [he]
  rw [pair_reflection (fun u v : I => ((u : ℝ)^2-(v : ℝ)^2)^2),integral_square_diff_sq]

theorem integral_squarePotential : (∫ u : I, squarePotential u) = 1/3 := by
  have he (u : I) : squarePotential u=(unitInterval.symm u : ℝ)^2 := rfl
  simp_rw [he]
  rw [integral_unit_reflection (fun u : I => (u : ℝ)^2),Copula.integral_unit_pow]
  norm_num

theorem integral_pair_symmetrize (f : I × I → ℝ) (hf : Continuous f) :
    (∫ p : I × I, f p) = ∫ p : I × I, (f p+f p.swap)/2 := by
  have hi := hf.integrable_of_hasCompactSupport (μ := (volume : Measure (I × I)))
    (HasCompactSupport.of_compactSpace _)
  have hs : Integrable (fun p : I × I => f p.swap) := (hf.comp continuous_swap).integrable_of_hasCompactSupport (μ := (volume : Measure (I × I)))
    (HasCompactSupport.of_compactSpace _)
  rw [integral_div,integral_add hi hs]
  have he : (∫ p : I × I, f p.swap) = ∫ p : I × I, f p := integral_prod_swap f
  rw [he]
  ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
