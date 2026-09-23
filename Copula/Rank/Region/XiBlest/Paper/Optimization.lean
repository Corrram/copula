import Copula.Rank.Region.XiBlest.Paper.ConditionalFormula

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
open ProbabilityTheory.Copula.RankRegion.XiBlest.Support

namespace ProbabilityTheory.Copula.RankRegion.XiBlest

theorem blest_quadratic_certificate (a b t x : ℝ) (hx : x ∈ Icc 0 1) :
    (x - unitClamp (a + b*(1-t)^2))^2 ≤
      (x^2 - 2*b*(1-t)^2*x) -
      (unitClamp (a+b*(1-t)^2)^2 - 2*b*(1-t)^2*unitClamp (a+b*(1-t)^2)) +
      (-2*a)*(x-unitClamp (a+b*(1-t)^2)) := by
  nlinarith [unitClamp_projection (a+b*(1-t)^2) x hx]

private theorem section_certificate (C D : Copula 2) (a b : ℝ) (v : I)
    (hD : (fun u => D.conditionalCDF u v) =ᵐ[volume]
      fun u => unitClamp (a + b * (1 - (u : ℝ)) ^ 2)) :
    (∫ u : I, (C.conditionalCDF u v - D.conditionalCDF u v) ^ 2) ≤
      ((∫ u : I, C.conditionalCDF u v ^ 2) -
        2 * b * (∫ u : I, (1 - (u : ℝ)) ^ 2 * C.conditionalCDF u v)) -
      ((∫ u : I, D.conditionalCDF u v ^ 2) -
        2 * b * (∫ u : I, (1 - (u : ℝ)) ^ 2 * D.conditionalCDF u v)) := by
  have hi (E : Copula 2) : Integrable (fun u : I => E.conditionalCDF u v ^ 2 -
      (2 * b) * ((1 - (u : ℝ)) ^ 2 * E.conditionalCDF u v)) :=
    (E.integrable_conditionalCDF_sq v).sub ((integrable_blest_section E v).const_mul _)
  have hd : Integrable (fun u => C.conditionalCDF u v - D.conditionalCDF u v) :=
    (C.integrable_conditionalCDF v).sub (D.integrable_conditionalCDF v)
  have hsub : Integrable (fun u : I =>
      (C.conditionalCDF u v ^ 2 - 2 * b * ((1 - (u : ℝ)) ^ 2 * C.conditionalCDF u v)) -
      (D.conditionalCDF u v ^ 2 - 2 * b * ((1 - (u : ℝ)) ^ 2 * D.conditionalCDF u v))) :=
    (hi C).sub (hi D)
  have hh := integral_mono_ae (C.integrable_conditionalCDF_sub_sq D v)
    (((hi C).sub (hi D)).add (hd.const_mul ((-2 * a)))) (by
      filter_upwards [hD] with u hu
      simpa only [Pi.add_apply, Pi.sub_apply, hu, mul_assoc] using blest_quadratic_certificate a b (u : ℝ)
        (C.conditionalCDF u v) ⟨C.conditionalCDF_nonneg u v, C.conditionalCDF_le_one u v⟩)
  simp only [Pi.add_apply, Pi.sub_apply] at hh
  rw [integral_add hsub (hd.const_mul _), integral_sub (hi C) (hi D),
    integral_const_mul, integral_sub (C.integrable_conditionalCDF v)
      (D.integrable_conditionalCDF v), C.integral_conditionalCDF, D.integral_conditionalCDF] at hh
  simp only [sub_self, mul_zero, add_zero] at hh
  simpa only [integral_sub (C.integrable_conditionalCDF_sq v)
    ((integrable_blest_section C v).const_mul _),
    integral_sub (D.integrable_conditionalCDF_sq v)
      ((integrable_blest_section D v).const_mul _), integral_const_mul] using hh

/-- Quantitative sharp support inequality, without a density restriction. -/
theorem clamped_blest_distance_bound (C D : Copula 2) (b : ℝ)
    (hD : ∀ᵐ v : I, ∃ a : ℝ, (fun u => D.conditionalCDF u v) =ᵐ[volume]
      fun u => unitClamp (a + b * (1 - (u : ℝ)) ^ 2)) :
    6 * C.conditionalCDFDistanceSq D ≤
      C.chatterjeeXi - D.chatterjeeXi - b * (blestNu C - blestNu D) := by
  have hi (E : Copula 2) : Integrable (fun v : I =>
      (∫ u : I, E.conditionalCDF u v ^ 2) -
      (2 * b) * (∫ u : I, (1 - (u : ℝ)) ^ 2 * E.conditionalCDF u v)) :=
    E.integrable_integral_conditionalCDF_sq.sub ((integrable_blest_profile E).const_mul _)
  have hh := integral_mono_ae (C.integrable_integral_conditionalCDF_sub_sq D)
    ((hi C).sub (hi D)) (by
      filter_upwards [hD] with v hv
      obtain ⟨a, ha⟩ := hv
      exact section_certificate C D a b v ha)
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (hi C) (hi D),
    integral_sub C.integrable_integral_conditionalCDF_sq
      ((integrable_blest_profile C).const_mul _),
    integral_sub D.integrable_integral_conditionalCDF_sq
      ((integrable_blest_profile D).const_mul _), integral_const_mul, integral_const_mul] at hh
  rw [blest_conditional_formula C, blest_conditional_formula D]
  unfold Copula.chatterjeeXi Copula.conditionalCDFDistanceSq
  linarith

theorem clamped_blest_support (C D : Copula 2) (b : ℝ)
    (hD : ∀ᵐ v : I, ∃ a : ℝ, (fun u => D.conditionalCDF u v) =ᵐ[volume]
      fun u => unitClamp (a + b * (1 - (u : ℝ)) ^ 2)) :
    b * blestNu C - C.chatterjeeXi ≤ b * blestNu D - D.chatterjeeXi := by
  have h := clamped_blest_distance_bound C D b hD
  have hn := C.conditionalCDFDistanceSq_nonneg D
  linarith

theorem clamped_blest_support_eq_iff (C D : Copula 2) (b : ℝ)
    (hD : ∀ᵐ v : I, ∃ a : ℝ, (fun u => D.conditionalCDF u v) =ᵐ[volume]
      fun u => unitClamp (a + b * (1 - (u : ℝ)) ^ 2)) :
    b * blestNu C - C.chatterjeeXi = b * blestNu D - D.chatterjeeXi ↔ C = D := by
  refine ⟨fun he => ?_, fun he => he ▸ rfl⟩
  apply (C.conditionalCDFDistanceSq_eq_zero_iff D).mp
  have h := clamped_blest_distance_bound C D b hD
  have hn := C.conditionalCDFDistanceSq_nonneg D
  linarith

end ProbabilityTheory.Copula.RankRegion.XiBlest
