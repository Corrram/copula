/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Raftery
import Copula.Rank.Region.Common.StochasticRho
import Copula.Rank.Integration
import Copula.Dependence.Density

/-! # Spearman's rho of the Raftery family

For the Raftery copula `C_θ` (`0 ≤ θ < 1`, exponent `p = 1/(1-θ)`) Spearman's rho is

`ρ(C_θ) = θ(4 - 3θ)/(2 - θ)²`  (`spearmanRho_raftery`; Nelsen 2006, exercises of Ch. 5).

The double integral `∫∫ C_θ` splits along the diagonal. Below the diagonal (`u ≤ v`) the inner
integral in `u` is elementary; above it, the integrand `v + v^p (u^p - u^{1-p})/(2p-1)` is
integrated in `v` after exchanging the order of integration (Fubini), so that no integral of
`u^{1-p}` (logarithmic at `p = 2`) is needed. Both triangles contribute
`∫₀¹ (x²/2 + (x^{2p+1} - x²)/((2p-1)(p+1))) dx`, which gives `ρ = 1 - 4/(p+1)²`.
-/

open MeasureTheory Set Function
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace RafterySpearman

variable {p : ℝ}

theorem integral_branch (hp : 1 ≤ p) (c x : ℝ) :
    (∫ t in (0 : ℝ)..x, (t + c * t ^ p)) = x ^ 2 / 2 + c * x ^ (p + 1) / (p + 1) := by
  have h1 : IntervalIntegrable (fun t : ℝ => t) volume 0 x := continuous_id.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t : ℝ => c * t ^ p) volume 0 x :=
    (continuous_const.mul (Real.continuous_rpow_const (by linarith))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 h2,
    integral_id, intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
    Real.zero_rpow (by linarith)]
  ring

/-- The common value of the two triangle integrals, in closed form. -/
noncomputable def G (p x : ℝ) : ℝ :=
  x ^ 2 / 2 + (x ^ (2 * p + 1) - x ^ 2) / ((2 * p - 1) * (p + 1))

theorem branch_value (hp : 1 ≤ p) {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 / 2 + (x ^ p - x ^ (1 - p)) / (2 * p - 1) * x ^ (p + 1) / (p + 1) = G p x := by
  unfold G
  rcases eq_or_lt_of_le hx with h | h
  · subst h
    simp [Real.zero_rpow (show p ≠ 0 by linarith), Real.zero_rpow (show p + 1 ≠ 0 by linarith),
      Real.zero_rpow (show 2 * p + 1 ≠ 0 by linarith)]
  · have h1 : x ^ p * x ^ (p + 1) = x ^ (2 * p + 1) := by rw [← Real.rpow_add h]; ring_nf
    have h2 : x ^ (1 - p) * x ^ (p + 1) = x ^ 2 := by
      rw [← Real.rpow_add h, show 1 - p + (p + 1) = ((2 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    have hq : (2 * p - 1) ≠ 0 := by linarith
    have hr : (p + 1) ≠ 0 := by linarith
    rw [← h1, ← h2]
    field_simp

/-- The part of the Raftery CDF below the diagonal, as a function of `(v, u)`. -/
noncomputable def lower (p : ℝ) (v u : I) : ℝ :=
  if (u : ℝ) ≤ v then u + (u : ℝ) ^ p * ((v : ℝ) ^ p - (v : ℝ) ^ (1 - p)) / (2 * p - 1) else 0

/-- The part of the Raftery CDF above the diagonal, as a function of `(v, u)`. -/
noncomputable def upper (p : ℝ) (v u : I) : ℝ :=
  if (u : ℝ) ≤ v then 0 else v + (v : ℝ) ^ p * ((u : ℝ) ^ p - (u : ℝ) ^ (1 - p)) / (2 * p - 1)

theorem core_eq (v u : I) : Raftery.core p u v = lower p v u + upper p v u := by
  unfold Raftery.core lower upper
  split_ifs <;> ring

theorem measurable_lower (p : ℝ) : Measurable (uncurry (lower p)) := by
  unfold uncurry lower
  refine Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) ?_ measurable_const
  fun_prop

theorem measurable_upper (p : ℝ) : Measurable (uncurry (upper p)) := by
  unfold uncurry upper
  refine Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) measurable_const ?_
  fun_prop

theorem abs_core_le (hp : 1 ≤ p) (u v : I) : |Raftery.core p u v| ≤ 1 := by
  have h1 := Raftery.mul_le_core hp u.2.1 u.2.2 v.2.1 v.2.2
  have h2 := (Raftery.min_sub_core_le hp u.2.1 u.2.2 v.2.1 v.2.2).1
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg u.2.1 v.2.1]
  · linarith [min_le_left (u : ℝ) v, u.2.2]

theorem abs_lower_le (hp : 1 ≤ p) (v u : I) : |lower p v u| ≤ 1 := by
  have h := abs_core_le hp u v
  unfold Raftery.core at h
  unfold lower
  split_ifs with huv
  · rwa [ite_eq_left huv] at h
  · simp

theorem abs_upper_le (hp : 1 ≤ p) (v u : I) : |upper p v u| ≤ 1 := by
  have h := abs_core_le hp u v
  unfold Raftery.core at h
  unfold upper
  split_ifs with huv
  · simp
  · rwa [ite_eq_right huv] at h

theorem integrable_upper (hp : 1 ≤ p) :
    Integrable (uncurry (upper p)) ((volume : Measure I).prod volume) :=
  (integrable_const (1 : ℝ)).mono' (measurable_upper p).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs]; exact abs_upper_le hp q.1 q.2)

theorem integrable_lower_section (hp : 1 ≤ p) (v : I) : Integrable (fun u => lower p v u) :=
  (integrable_const (1 : ℝ)).mono' ((measurable_lower p).comp measurable_prodMk_left).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]; exact abs_lower_le hp v u)

theorem integrable_upper_section (hp : 1 ≤ p) (v : I) : Integrable (fun u => upper p v u) :=
  (integrable_const (1 : ℝ)).mono' ((measurable_upper p).comp measurable_prodMk_left).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]; exact abs_upper_le hp v u)

/-- The inner integral below the diagonal. -/
theorem integral_lower (hp : 1 ≤ p) (v : I) : (∫ u : I, lower p v u) = G p v := by
  set c := ((v : ℝ) ^ p - (v : ℝ) ^ (1 - p)) / (2 * p - 1)
  have he : (fun u : I => lower p v u) =
      (Iic v).indicator (fun u : I => (u : ℝ) + c * (u : ℝ) ^ p) := by
    funext u
    unfold lower
    by_cases h : u ≤ v
    · rw [indicator_of_mem (show u ∈ Iic v from h), ite_eq_left (show (u : ℝ) ≤ v from h)]
      simp only [c]; ring
    · rw [indicator_of_notMem (show u ∉ Iic v from h), ite_eq_right (show ¬ (u : ℝ) ≤ v from h)]
  rw [he, integral_indicator measurableSet_Iic, integral_unit_Iic (fun t => t + c * t ^ p),
    integral_branch hp, ← branch_value hp v.2.1]

/-- The inner integral above the diagonal, after exchanging the order of integration. -/
theorem integral_upper (hp : 1 ≤ p) (u : I) : (∫ v : I, upper p v u) = G p u := by
  set c := ((u : ℝ) ^ p - (u : ℝ) ^ (1 - p)) / (2 * p - 1)
  have he : (fun v : I => upper p v u) =
      (Iio u).indicator (fun v : I => (v : ℝ) + c * (v : ℝ) ^ p) := by
    funext v
    unfold upper
    by_cases h : v < u
    · rw [indicator_of_mem (show v ∈ Iio u from h),
        ite_eq_right (show ¬ (u : ℝ) ≤ v from not_le.mpr h)]
      simp only [c]; ring
    · rw [indicator_of_notMem (show v ∉ Iio u from h),
        ite_eq_left (show (u : ℝ) ≤ v from not_lt.mp h)]
  rw [he, integral_indicator measurableSet_Iio, setIntegral_congr_set Iio_ae_eq_Iic,
    integral_unit_Iic (fun t => t + c * t ^ p), integral_branch hp, ← branch_value hp u.2.1]

theorem integral_G (hp : 1 ≤ p) :
    (∫ x : I, G p x) = 1 / 6 + (1 / (2 * p + 2) - 1 / 3) / ((2 * p - 1) * (p + 1)) := by
  rw [integral_unitInterval (G p)]
  have hq : (2 * p - 1) * (p + 1) ≠ 0 := by apply mul_ne_zero <;> linarith
  have h2 : (2 * p + 2) ≠ 0 := by linarith
  have hd : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun x : ℝ => x ^ 3 / 6 + (x ^ (2 * p + 2) / (2 * p + 2) - x ^ 3 / 3) /
        ((2 * p - 1) * (p + 1))) (G p x) x := by
    intro x _
    have hr := Real.hasDerivAt_rpow_const (x := x) (p := 2 * p + 2) (Or.inr (by linarith))
    have h := (((hasDerivAt_pow 3 x).div_const 6).add
      (((hr.div_const (2 * p + 2)).sub ((hasDerivAt_pow 3 x).div_const 3)).div_const
        ((2 * p - 1) * (p + 1))))
    convert h using 1
    unfold G
    rw [show 2 * p + 2 - 1 = 2 * p + 1 by ring]
    field_simp
    ring
  have hGc : Continuous (G p) := by
    unfold G
    exact ((continuous_pow 2).div_const _).add
      (((Real.continuous_rpow_const (by linarith)).sub (continuous_pow 2)).div_const _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hGc.intervalIntegrable _ _),
    Real.one_rpow, Real.zero_rpow (by linarith)]
  field_simp
  ring

end RafterySpearman

/-- Spearman's rho of the Raftery copula: `ρ(C_θ) = θ(4 - 3θ)/(2 - θ)²`. -/
theorem spearmanRho_raftery {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    (raftery θ h0 h1).spearmanRho = θ * (4 - 3 * θ) / (2 - θ) ^ 2 := by
  have hp := one_le_raftery_exponent h0 h1
  set p := 1 / (1 - θ) with hpdef
  rw [RankRegion.Common.spearmanRho_eq_iterated_cdf]
  have hinner : ∀ v : I, (∫ u : I, (raftery θ h0 h1).cdf ![u, v]) =
      RafterySpearman.G p v + ∫ u : I, RafterySpearman.upper p v u := by
    intro v
    simp_rw [cdf_raftery_two, rafteryCDF, RafterySpearman.core_eq]
    rw [integral_add (RafterySpearman.integrable_lower_section hp v)
      (RafterySpearman.integrable_upper_section hp v), RafterySpearman.integral_lower hp]
  simp_rw [hinner]
  have hGi : Integrable (fun v : I => RafterySpearman.G p v) := by
    have hc : Continuous (RafterySpearman.G p) := by
      unfold RafterySpearman.G
      exact ((continuous_pow 2).div_const _).add
        (((Real.continuous_rpow_const (by linarith)).sub (continuous_pow 2)).div_const _)
    exact (integrable_const (1 : ℝ)).mono' (hc.measurable.comp measurable_subtype_coe).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => by
        rw [← RafterySpearman.integral_lower hp v]
        refine (norm_integral_le_of_norm_le_const (C := 1)
          (Filter.Eventually.of_forall fun u => ?_)).trans ?_
        · rw [Real.norm_eq_abs]; exact RafterySpearman.abs_lower_le hp v u
        · simp)
  have hUi : Integrable (fun v : I => ∫ u : I, RafterySpearman.upper p v u) :=
    (RafterySpearman.integrable_upper hp).integral_prod_left
  rw [integral_add hGi hUi, integral_integral_swap (RafterySpearman.integrable_upper hp)]
  simp_rw [RafterySpearman.integral_upper hp]
  rw [RafterySpearman.integral_G hp]
  have h1' : (1 - θ) ≠ 0 := by linarith
  have h2' : (2 - θ) ≠ 0 := by linarith
  have h3 : 1 + (1 - θ) ≠ 0 := by linarith
  have h4 : 2 - (1 - θ) ≠ 0 := by linarith
  rw [hpdef]
  field_simp
  ring

end ProbabilityTheory.Copula
