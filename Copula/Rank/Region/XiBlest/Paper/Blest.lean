import Copula.Rank.Region.XiBlest.Paper.Definitions
import Copula.Rank.FGM
import Copula.Rank.Mixture
import Copula.Rank.ConditionalDistance
import Copula.Rank.ConditionalDerivative

/-! # Blest's weighted CDF functional

Equation (3) weights the first coordinate by 1-u. Its integral exists for
every copula, including singular ones. We check monotonicity, affine
mixtures, the independence normalization, and the xi=0 endpoint.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest

/-- Equation (3), with the first coordinate carrying Blest's weight. -/
noncomputable def blestNu (C : Copula 2) : ℝ :=
  24 * (∫ x, (1 - (x 0 : ℝ)) * C.cdf x ∂(Copula.independence 2).toMeasure) - 2

theorem blest_integrable (C : Copula 2) :
    Integrable (fun x => (1 - (x 0 : ℝ)) * C.cdf x)
      (Copula.independence 2).toMeasure :=
  Copula.integrable_continuous_cube _ ((continuous_const.sub (by fun_prop)).mul C.continuous_cdf)

/-- The product-measure definition agrees with the source's iterated integral. -/
theorem blest_integral_formula (C : Copula 2) :
    blestNu C = 24 * (∫ v : I, ∫ u : I, (1 - (u : ℝ)) * C.cdf ![u, v]) - 2 := by
  have hi : Integrable (fun p : I × I => (1 - (p.1 : ℝ)) * C.cdf ![p.1, p.2])
      ((volume : Measure I).prod volume) :=
    (show Continuous (fun p : I × I => (1 - (p.1 : ℝ)) * C.cdf ![p.1, p.2]) by
      fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hprod := (measurePreserving_finTwoArrow (volume : Measure I)).integral_comp
    MeasurableEquiv.finTwoArrow.measurableEmbedding
    (fun p : I × I => (1 - (p.1 : ℝ)) * C.cdf ![p.1, p.2])
  have hx (x : Fin 2 → I) : ![x 0, x 1] = x := by
    ext i
    fin_cases i <;> rfl
  simp only [MeasurableEquiv.finTwoArrow_apply, hx] at hprod
  rw [blestNu, Copula.toMeasure_independence, hprod, integral_prod (f := fun p : I × I => (1 - (p.1 : ℝ)) * C.cdf ![p.1, p.2]) hi,
    integral_integral_swap hi]

theorem xi_derivative_formula (C : Copula 2) :
    C.chatterjeeXi = 6 * (∫ v : I, ∫ u : I, deriv (C.cdfSection v) (u : ℝ) ^ 2) - 2 :=
  C.chatterjeeXi_eq_integral_deriv

theorem blest_mono (C D : Copula 2) (h : ∀ x, C.cdf x ≤ D.cdf x) :
    blestNu C ≤ blestNu D := by
  have hi := integral_mono (blest_integrable C) (blest_integrable D)
    (fun x => mul_le_mul_of_nonneg_left (h x) (sub_nonneg.mpr (x 0).property.2))
  unfold blestNu
  linarith

theorem blest_mix (C D : Copula 2) (a : I) :
    blestNu (C.mix D a) = (a : ℝ) * blestNu C + (1 - (a : ℝ)) * blestNu D := by
  have he : (fun x => (1 - (x 0 : ℝ)) * (C.mix D a).cdf x) =
      fun x => (a : ℝ) * ((1 - (x 0 : ℝ)) * C.cdf x) +
        (1 - (a : ℝ)) * ((1 - (x 0 : ℝ)) * D.cdf x) := by
    funext x
    rw [Copula.cdf_mix]
    ring
  unfold blestNu
  rw [he, integral_add ((blest_integrable C).const_mul _) ((blest_integrable D).const_mul _),
    integral_const_mul, integral_const_mul]
  ring

theorem blest_independence : blestNu (Copula.independence 2) = 0 := by
  have he : (fun x => (1 - (x 0 : ℝ)) * (Copula.independence 2).cdf x) =
      fun x : Fin 2 → I => ((x 0 : ℝ) * (1 - (x 0 : ℝ))) * (x 1 : ℝ) := by
    funext x
    simp only [Copula.cdf_independence, Fin.prod_univ_two]
    ring
  rw [blestNu, he, Copula.integral_independence_mul
    (fun u : I => (u : ℝ) * (1 - (u : ℝ))) (fun v : I => (v : ℝ)),
    Copula.integral_unit_mul_one_sub, Copula.integral_unit_id]
  norm_num

/-- The xi=0 endpoint of the region in Theorem 1.1. -/
theorem xi_zero_slice (C : Copula 2) :
    C.chatterjeeXi = 0 ↔ C = Copula.independence 2 ∧ blestNu C = 0 := by
  constructor
  · intro h
    have he := C.chatterjeeXi_eq_zero_iff.mp h
    exact ⟨he, he ▸ blest_independence⟩
  · rintro ⟨rfl, _⟩
    simp

end ProbabilityTheory.Copula.RankRegion.XiBlest
