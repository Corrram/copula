import Copula.Rank.Region.XiRho.Support.StochasticRho
import Copula.Rank.ConditionalDistance

/-! # A sharp quadratic certificate for clamped conditional distributions

A clamped affine conditional CDF with slope `-b` uniquely maximizes
`b * rho - xi`. The quantitative remainder controls the squared conditional
CDF distance, and applies to every competing copula, including singular laws.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

/-- Projection to the closed unit interval. -/
noncomputable def unitClamp (x : ℝ) : ℝ := min 1 (max 0 x)

theorem unitClamp_mem (x : ℝ) : unitClamp x ∈ Icc 0 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem unitClamp_projection (z x : ℝ) (hx : x ∈ Icc 0 1) :
    0 ≤ (x - unitClamp z) * (unitClamp z - z) := by
  unfold unitClamp
  rcases le_total z 0 with hz | hz
  · rw [max_eq_left hz, min_eq_right zero_le_one]
    exact mul_nonneg (by linarith [hx.1]) (by linarith)
  · rw [max_eq_right hz]
    rcases le_total z 1 with hz1 | hz1
    · rw [min_eq_right hz1]
      simp
    · rw [min_eq_left hz1]
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hx.2]) (by linarith)

theorem clamped_quadratic_certificate (a b t x : ℝ) (hx : x ∈ Icc 0 1) :
    (x - unitClamp (a - b * t)) ^ 2 ≤
      (x ^ 2 - 2 * b * (1 - t) * x) -
      (unitClamp (a - b * t) ^ 2 - 2 * b * (1 - t) * unitClamp (a - b * t)) +
      2 * (b - a) * (x - unitClamp (a - b * t)) := by
  nlinarith [unitClamp_projection (a - b * t) x hx]

theorem integrable_rho_section (C : Copula 2) (v : I) :
    Integrable (fun u : I => (1 - (u : ℝ)) * C.conditionalCDF u v) :=
  integrable_unit_bounded ((measurable_const.sub measurable_subtype_coe).mul (C.measurable_conditionalCDF_left v)) (fun u => ⟨
    mul_nonneg (by linarith [u.property.2]) (C.conditionalCDF_nonneg u v),
    (mul_le_mul_of_nonneg_left (C.conditionalCDF_le_one u v)
      (by linarith [u.property.2])).trans (by simp; linarith [u.property.1])⟩)

theorem integrable_rho_profile (C : Copula 2) :
    Integrable (fun v : I => ∫ u : I, (1 - (u : ℝ)) * C.conditionalCDF u v) := by
  have he (v : I) : (∫ u : I, (1 - (u : ℝ)) * C.conditionalCDF u v) =
      ∫ u : I, C.cdf ![u, v] := by
    simp_rw [C.cdf_eq_integral_conditionalCDF]
    exact (integral_lower_integral (C.measurable_conditionalCDF_left v)
      (fun u => ⟨C.conditionalCDF_nonneg u v, C.conditionalCDF_le_one u v⟩)).symm
  simp_rw [he]
  have hi : Integrable (fun p : I × I => C.cdf ![p.1, p.2])
      ((volume : Measure I).prod volume) :=
    (C.continuous_cdf.comp (by fun_prop)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact hi.integral_prod_right

theorem rho_conditional_formula (C : Copula 2) :
    C.spearmanRho = 12 * (∫ v : I, ∫ u : I,
      (1 - (u : ℝ)) * C.conditionalCDF u v) - 3 := by
  rw [spearmanRho_eq_iterated_cdf]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with v
  simp_rw [C.cdf_eq_integral_conditionalCDF]
  exact integral_lower_integral (C.measurable_conditionalCDF_left v)
    (fun u => ⟨C.conditionalCDF_nonneg u v, C.conditionalCDF_le_one u v⟩)

private theorem section_certificate (C D : Copula 2) (a b : ℝ) (v : I)
    (hD : (fun u => D.conditionalCDF u v) =ᵐ[volume]
      fun u => unitClamp (a - b * (u : ℝ))) :
    (∫ u : I, (C.conditionalCDF u v - D.conditionalCDF u v) ^ 2) ≤
      ((∫ u : I, C.conditionalCDF u v ^ 2) -
        2 * b * (∫ u : I, (1 - (u : ℝ)) * C.conditionalCDF u v)) -
      ((∫ u : I, D.conditionalCDF u v ^ 2) -
        2 * b * (∫ u : I, (1 - (u : ℝ)) * D.conditionalCDF u v)) := by
  have hi (E : Copula 2) : Integrable (fun u : I => E.conditionalCDF u v ^ 2 -
      (2 * b) * ((1 - (u : ℝ)) * E.conditionalCDF u v)) :=
    (E.integrable_conditionalCDF_sq v).sub ((integrable_rho_section E v).const_mul _)
  have hd : Integrable (fun u => C.conditionalCDF u v - D.conditionalCDF u v) :=
    (C.integrable_conditionalCDF v).sub (D.integrable_conditionalCDF v)
  have hsub : Integrable (fun u : I =>
      (C.conditionalCDF u v ^ 2 - 2 * b * ((1 - (u : ℝ)) * C.conditionalCDF u v)) -
      (D.conditionalCDF u v ^ 2 - 2 * b * ((1 - (u : ℝ)) * D.conditionalCDF u v))) :=
    (hi C).sub (hi D)
  have hh := integral_mono_ae (C.integrable_conditionalCDF_sub_sq D v)
    (((hi C).sub (hi D)).add (hd.const_mul (2 * (b - a)))) (by
      filter_upwards [hD] with u hu
      simpa only [Pi.add_apply, Pi.sub_apply, hu, mul_assoc] using clamped_quadratic_certificate a b (u : ℝ)
        (C.conditionalCDF u v) ⟨C.conditionalCDF_nonneg u v, C.conditionalCDF_le_one u v⟩)
  simp only [Pi.add_apply, Pi.sub_apply] at hh
  rw [integral_add hsub (hd.const_mul _), integral_sub (hi C) (hi D),
    integral_const_mul, integral_sub (C.integrable_conditionalCDF v)
      (D.integrable_conditionalCDF v), C.integral_conditionalCDF, D.integral_conditionalCDF] at hh
  simp only [sub_self, mul_zero, add_zero] at hh
  simpa only [integral_sub (C.integrable_conditionalCDF_sq v)
    ((integrable_rho_section C v).const_mul _),
    integral_sub (D.integrable_conditionalCDF_sq v)
      ((integrable_rho_section D v).const_mul _), integral_const_mul] using hh

/-- Quantitative sharp support inequality, without a density restriction. -/
theorem clamped_rho_distance_bound (C D : Copula 2) (b : ℝ)
    (hD : ∀ᵐ v : I, ∃ a : ℝ, (fun u => D.conditionalCDF u v) =ᵐ[volume]
      fun u => unitClamp (a - b * (u : ℝ))) :
    6 * C.conditionalCDFDistanceSq D ≤
      C.chatterjeeXi - D.chatterjeeXi - b * (C.spearmanRho - D.spearmanRho) := by
  have hi (E : Copula 2) : Integrable (fun v : I =>
      (∫ u : I, E.conditionalCDF u v ^ 2) -
      (2 * b) * (∫ u : I, (1 - (u : ℝ)) * E.conditionalCDF u v)) :=
    E.integrable_integral_conditionalCDF_sq.sub ((integrable_rho_profile E).const_mul _)
  have hh := integral_mono_ae (C.integrable_integral_conditionalCDF_sub_sq D)
    ((hi C).sub (hi D)) (by
      filter_upwards [hD] with v hv
      obtain ⟨a, ha⟩ := hv
      exact section_certificate C D a b v ha)
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (hi C) (hi D),
    integral_sub C.integrable_integral_conditionalCDF_sq
      ((integrable_rho_profile C).const_mul _),
    integral_sub D.integrable_integral_conditionalCDF_sq
      ((integrable_rho_profile D).const_mul _), integral_const_mul, integral_const_mul] at hh
  rw [rho_conditional_formula C, rho_conditional_formula D]
  unfold Copula.chatterjeeXi Copula.conditionalCDFDistanceSq
  linarith

theorem clamped_rho_support (C D : Copula 2) (b : ℝ)
    (hD : ∀ᵐ v : I, ∃ a : ℝ, (fun u => D.conditionalCDF u v) =ᵐ[volume]
      fun u => unitClamp (a - b * (u : ℝ))) :
    b * C.spearmanRho - C.chatterjeeXi ≤ b * D.spearmanRho - D.chatterjeeXi := by
  have h := clamped_rho_distance_bound C D b hD
  have hn := C.conditionalCDFDistanceSq_nonneg D
  linarith

theorem clamped_rho_support_eq_iff (C D : Copula 2) (b : ℝ)
    (hD : ∀ᵐ v : I, ∃ a : ℝ, (fun u => D.conditionalCDF u v) =ᵐ[volume]
      fun u => unitClamp (a - b * (u : ℝ))) :
    b * C.spearmanRho - C.chatterjeeXi = b * D.spearmanRho - D.chatterjeeXi ↔ C = D := by
  refine ⟨fun he => ?_, fun he => he ▸ rfl⟩
  apply (C.conditionalCDFDistanceSq_eq_zero_iff D).mp
  have h := clamped_rho_distance_bound C D b hD
  have hn := C.conditionalCDFDistanceSq_nonneg D
  linarith

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
