import Copula.Rank.Region.XiBlest.Paper.Normalization
import Copula.Rank.Region.XiBlest.Support.DeterministicRho
import Copula.Rank.Symmetry

/-! # The entire vertical boundary in Theorem 1.1

On radially symmetric copulas Blest's nu equals Spearman's rho. The centered
deterministic witnesses therefore cover nu in [-1,1] while keeping xi=1.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest

theorem blest_eq_rho_of_radiallySymmetric (C : Copula 2) (hC : C.IsRadiallySymmetric) :
    blestNu C = C.spearmanRho := by
  have hp : (Copula.independence 2).reflect Finset.univ = Copula.independence 2 :=
    Copula.isRadiallySymmetric_independence
  have hs := Copula.integral_reflect (Copula.independence 2) Finset.univ
    (fun x => (1 - (x 0 : ℝ)) * C.cdf x) (by fun_prop)
  rw [hp] at hs
  have he : (fun x : Fin 2 → I => (1 - (Copula.reflectPoint Finset.univ x 0 : ℝ)) *
      C.cdf (Copula.reflectPoint Finset.univ x)) =
      fun x => (x 0 : ℝ) * C.cdf x + (x 0 : ℝ) - (x 0 : ℝ) ^ 2 - (x 0 : ℝ) * x 1 := by
    funext x
    have hx : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
    have hr : Copula.reflectPoint Finset.univ x = ![unitInterval.symm (x 0), unitInterval.symm (x 1)] := by
      ext i; fin_cases i <;> simp [Copula.reflectPoint]
    have hc := (Copula.isRadiallySymmetric_iff C).mp hC (x 0) (x 1)
    rw [hx] at hc
    have hc' : C.cdf ![unitInterval.symm (x 0), unitInterval.symm (x 1)] =
        C.cdf x - (x 0 : ℝ) - x 1 + 1 := by linarith
    rw [hr, hc']
    simp only [Matrix.cons_val_zero, unitInterval.coe_symm_eq]
    ring
  rw [he, integral_sub, integral_sub, integral_add,
    Copula.integral_coe_eval, Copula.integral_sq_eval,
    Copula.integral_independence_mul (fun u : I => (u : ℝ)) (fun v : I => (v : ℝ)),
    Copula.integral_unit_id] at hs
  · have hw : (∫ x, (1 - (x 0 : ℝ)) * C.cdf x ∂(Copula.independence 2).toMeasure) =
        (∫ x, C.cdf x ∂(Copula.independence 2).toMeasure) -
          (∫ x, (x 0 : ℝ) * C.cdf x ∂(Copula.independence 2).toMeasure) := by
      have hf : (fun x : Fin 2 → I => (1 - (x 0 : ℝ)) * C.cdf x) =
          fun x => C.cdf x - (x 0 : ℝ) * C.cdf x := by funext x; ring
      rw [hf, integral_sub]
      all_goals exact Copula.integrable_continuous_cube _ (by fun_prop)
    rw [blestNu, C.spearmanRho_eq_integral_cdf]
    linarith
  all_goals exact Copula.integrable_continuous_cube _ (by fun_prop)

theorem xi_one_slice (v : ℝ) :
    (∃ C : Copula 2, C.chatterjeeXi = 1 ∧ blestNu C = v) ↔ v ∈ Icc (-1) 1 := by
  constructor
  · rintro ⟨C, _, rfl⟩
    exact blest_mem_Icc C
  · intro hv
    obtain ⟨C, hs, hxi, hrho⟩ := ProbabilityTheory.Copula.RankRegion.XiBlest.Support.deterministic_rho_attained v hv
    exact ⟨C, hxi, (blest_eq_rho_of_radiallySymmetric C hs).trans hrho⟩

end ProbabilityTheory.Copula.RankRegion.XiBlest
