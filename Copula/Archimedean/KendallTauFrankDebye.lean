/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.KendallTauFrank
import Copula.Families.FrankNegative
import Copula.Rank.Symmetry

/-! # Kendall's tau of the Frank family in Debye form

Nelsen, *An Introduction to Copulas*, second edition, Example 5.4 / Table 4.1 (family 4.2.5):
for Frank's family with parameter `θ > 0`,
`τ_θ = 1 − (4/θ) (1 − D₁(θ))`, where `D₁(θ) = (1/θ) ∫₀^θ t / (e^t − 1) dt` is the Debye function of
order one (`debyeOne`).

`kendallTau_frank` (Corollary 5.1.4) gives
`τ = 1 + (4/θ) ∫₀¹ (e^{θt} − 1) log((1 − e^{−θt}) / (1 − e^{−θ})) dt`. After the substitution
`x = θ t`, an integration by parts against `F(x) = e^x − 1 − x` (with the boundary term at `0`
vanishing because `F(x) ≤ x (e^x − 1)` and `|w log w| ≤ 1`) turns this into
`∫₀^θ (e^x − 1) log(...) dx = −θ + ∫₀^θ x / (e^x − 1) dx` (`frank_integral_eq_debye`), which is
the Debye form (`kendallTau_frank_debye`).

For `θ < 0` (`frankNegative θ`, the reflection of Frank's copula with parameter `−θ`), the same
formula holds (`kendallTau_frankNegative_debye`), by `τ(C^{σ₂}) = −τ(C)` and the reflection
identity `D₁(−x) = D₁(x) + x/2` (`debyeOne_neg`).
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The Debye function of order one, `D₁(θ) = (1/θ) ∫₀^θ t / (e^t − 1) dt`. -/
noncomputable def debyeOne (θ : ℝ) : ℝ := θ⁻¹ * ∫ t in (0 : ℝ)..θ, t / (Real.exp t - 1)

namespace FrankDebye

private theorem expm1_pos {x : ℝ} (hx : 0 < x) : 0 < Real.exp x - 1 := by
  have := Real.add_one_lt_exp hx.ne'
  linarith

private theorem w_pos {x : ℝ} (hx : 0 < x) : 0 < 1 - Real.exp (-x) := by
  have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
  linarith

private theorem w_le_one (x : ℝ) : 1 - Real.exp (-x) ≤ 1 := by
  have := Real.exp_pos (-x)
  linarith

/-- `e^x − 1 = e^x (1 − e^{−x})`. -/
private theorem expm1_eq (x : ℝ) : Real.exp x - 1 = Real.exp x * (1 - Real.exp (-x)) := by
  rw [mul_sub, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- `0 ≤ e^x − 1 − x ≤ x (e^x − 1)`. -/
private theorem F_bounds (x : ℝ) :
    0 ≤ Real.exp x - 1 - x ∧ Real.exp x - 1 - x ≤ x * (Real.exp x - 1) := by
  refine ⟨by linarith [Real.add_one_le_exp x], ?_⟩
  have h := Real.add_one_le_exp (-x)
  have he := expm1_eq x
  have hpos := Real.exp_pos x
  nlinarith

/-- The integrand after substitution. -/
private noncomputable def h (θ x : ℝ) : ℝ :=
  (Real.exp x - 1) * Real.log ((1 - Real.exp (-x)) / (1 - Real.exp (-θ)))

/-- The antiderivative used for the integration by parts. -/
private noncomputable def f (θ x : ℝ) : ℝ :=
  (Real.exp x - 1 - x) * Real.log ((1 - Real.exp (-x)) / (1 - Real.exp (-θ)))

private noncomputable def k (x : ℝ) : ℝ := (Real.exp x - 1 - x) / (Real.exp x - 1)

private theorem log_split {θ x : ℝ} (hθ : 0 < θ) (hx : 0 < x) :
    Real.log ((1 - Real.exp (-x)) / (1 - Real.exp (-θ))) =
      Real.log (1 - Real.exp (-x)) - Real.log (1 - Real.exp (-θ)) :=
  Real.log_div (w_pos hx).ne' (w_pos hθ).ne'

private theorem w_abs_log_le {x : ℝ} (hx : 0 < x) :
    (1 - Real.exp (-x)) * |Real.log (1 - Real.exp (-x))| ≤ 1 := by
  have h := Real.abs_log_mul_self_lt _ (w_pos hx) (w_le_one x)
  rw [abs_mul, abs_of_pos (w_pos hx)] at h
  linarith

private theorem hasDerivAt_f {θ x : ℝ} (hθ : 0 < θ) (hx : 0 < x) :
    HasDerivAt (f θ) (h θ x + k x) x := by
  have hw := w_pos hx
  have hwθ := w_pos hθ
  have hq : (1 - Real.exp (-x)) / (1 - Real.exp (-θ)) ≠ 0 := (div_pos hw hwθ).ne'
  have hF : HasDerivAt (fun y => Real.exp y - 1 - y) (Real.exp x - 1) x := by
    exact ((Real.hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id' x)
  have hW : HasDerivAt (fun y => (1 - Real.exp (-y)) / (1 - Real.exp (-θ)))
      (Real.exp (-x) / (1 - Real.exp (-θ))) x := by
    have := (((hasDerivAt_id x).neg.exp).const_sub 1).div_const (1 - Real.exp (-θ))
    simpa using this
  have hG := hW.log hq
  have := hF.mul hG
  refine this.congr_deriv ?_
  have he := expm1_pos hx
  have hE : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  simp only [h, k]
  field_simp
  rw [expm1_eq x]
  field_simp
  ring_nf
  nlinarith [hE]

private theorem abs_h_le {θ x : ℝ} (hθ : 0 < θ) (hx : 0 < x) (hxθ : x ≤ θ) :
    |h θ x| ≤ Real.exp θ * (1 + |Real.log (1 - Real.exp (-θ))|) := by
  have hw := w_pos hx
  have hex := Real.exp_pos x
  have hexθ : Real.exp x ≤ Real.exp θ := Real.exp_le_exp.mpr hxθ
  rw [h, log_split hθ hx, expm1_eq x, abs_mul, abs_mul, abs_of_pos hex, abs_of_pos hw]
  have h1 := w_abs_log_le hx
  have h2 : |Real.log (1 - Real.exp (-x)) - Real.log (1 - Real.exp (-θ))| ≤
      |Real.log (1 - Real.exp (-x))| + |Real.log (1 - Real.exp (-θ))| := abs_sub _ _
  have h3 := w_le_one x
  have hA := abs_nonneg (Real.log (1 - Real.exp (-θ)))
  have hB := abs_nonneg (Real.log (1 - Real.exp (-x)))
  calc Real.exp x * (1 - Real.exp (-x)) *
        |Real.log (1 - Real.exp (-x)) - Real.log (1 - Real.exp (-θ))|
      ≤ Real.exp x * (1 - Real.exp (-x)) *
        (|Real.log (1 - Real.exp (-x))| + |Real.log (1 - Real.exp (-θ))|) := by gcongr
    _ = Real.exp x * ((1 - Real.exp (-x)) * |Real.log (1 - Real.exp (-x))|) +
        Real.exp x * (1 - Real.exp (-x)) * |Real.log (1 - Real.exp (-θ))| := by ring
    _ ≤ Real.exp θ * 1 + Real.exp θ * 1 * |Real.log (1 - Real.exp (-θ))| := by
        gcongr
    _ = _ := by ring

private theorem abs_k_le {x : ℝ} (hx : 0 < x) : |k x| ≤ x := by
  have he := expm1_pos hx
  obtain ⟨h0, h1⟩ := F_bounds x
  rw [k, abs_of_nonneg (div_nonneg h0 he.le), div_le_iff₀ he]
  exact h1

private theorem abs_ratio_le {x : ℝ} (hx : 0 < x) : |x / (Real.exp x - 1)| ≤ 1 := by
  have he := expm1_pos hx
  rw [abs_of_nonneg (div_nonneg hx.le he.le), div_le_iff₀ he, one_mul]
  linarith [Real.add_one_le_exp x]

private theorem abs_f_le {θ x : ℝ} (hθ : 0 < θ) (hx : 0 < x) :
    |f θ x| ≤ x * Real.exp x * (1 + |Real.log (1 - Real.exp (-θ))|) := by
  have hw := w_pos hx
  have hex := Real.exp_pos x
  obtain ⟨h0, h1⟩ := F_bounds x
  rw [f, log_split hθ hx, abs_mul, abs_of_nonneg h0]
  have hF : Real.exp x - 1 - x ≤ x * Real.exp x * (1 - Real.exp (-x)) := by
    rw [mul_assoc, ← expm1_eq x]; exact h1
  have h2 : |Real.log (1 - Real.exp (-x)) - Real.log (1 - Real.exp (-θ))| ≤
      |Real.log (1 - Real.exp (-x))| + |Real.log (1 - Real.exp (-θ))| := abs_sub _ _
  have h3 := w_abs_log_le hx
  have h4 := w_le_one x
  have hA := abs_nonneg (Real.log (1 - Real.exp (-θ)))
  have hB := abs_nonneg (Real.log (1 - Real.exp (-x)))
  have hxe : 0 ≤ x * Real.exp x := by positivity
  calc (Real.exp x - 1 - x) * |Real.log (1 - Real.exp (-x)) - Real.log (1 - Real.exp (-θ))|
      ≤ (x * Real.exp x * (1 - Real.exp (-x))) *
        (|Real.log (1 - Real.exp (-x))| + |Real.log (1 - Real.exp (-θ))|) := by
        gcongr
    _ = x * Real.exp x * ((1 - Real.exp (-x)) * |Real.log (1 - Real.exp (-x))|) +
        x * Real.exp x * (1 - Real.exp (-x)) * |Real.log (1 - Real.exp (-θ))| := by ring
    _ ≤ x * Real.exp x * 1 + x * Real.exp x * 1 * |Real.log (1 - Real.exp (-θ))| := by
        gcongr
    _ = _ := by ring

private theorem intervalIntegrable_of_bound {g : ℝ → ℝ} {θ : ℝ} (hθ : 0 < θ) (hg : Measurable g)
    (M : ℝ) (hM : ∀ x, 0 < x → x ≤ θ → |g x| ≤ M) : IntervalIntegrable g volume 0 θ := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => M) intervalIntegrable_const
    hg.aestronglyMeasurable ?_
  rw [uIoc_of_le hθ.le]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simpa [Real.norm_eq_abs] using hM x hx.1 hx.2

private theorem measurable_h (θ : ℝ) : Measurable (h θ) := by
  unfold h; fun_prop

private theorem measurable_k : Measurable k := by
  unfold k; fun_prop

/-- The key identity:
`∫₀^θ (e^x − 1) log((1 − e^{−x}) / (1 − e^{−θ})) dx = −θ + ∫₀^θ x/(e^x − 1) dx`. -/
theorem frank_integral_eq_debye {θ : ℝ} (hθ : 0 < θ) :
    (∫ x in (0 : ℝ)..θ, (Real.exp x - 1) * Real.log ((1 - Real.exp (-x)) / (1 - Real.exp (-θ)))) =
      -θ + ∫ x in (0 : ℝ)..θ, x / (Real.exp x - 1) := by
  set c := 1 + |Real.log (1 - Real.exp (-θ))| with hc
  have hhi : IntervalIntegrable (h θ) volume 0 θ :=
    intervalIntegrable_of_bound hθ (measurable_h θ) _ fun x hx hxθ => abs_h_le hθ hx hxθ
  have hki : IntervalIntegrable k volume 0 θ :=
    intervalIntegrable_of_bound hθ measurable_k θ fun x hx hxθ => (abs_k_le hx).trans hxθ
  have hri : IntervalIntegrable (fun x => x / (Real.exp x - 1)) volume 0 θ :=
    intervalIntegrable_of_bound hθ (by fun_prop) 1 fun x hx _ => abs_ratio_le hx
  -- FTC for `f`
  have hFTC : ∫ x in (0 : ℝ)..θ, (h θ x + k x) = 0 - 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hθ
      (fun x hx => hasDerivAt_f hθ hx.1) (hhi.add hki)
    · -- limit at `0⁺`
      have hlim : Tendsto (fun x : ℝ => x * Real.exp x * c) (𝓝[>] 0) (𝓝 0) := by
        have hcont : Continuous (fun x : ℝ => x * Real.exp x * c) := by fun_prop
        have := hcont.tendsto 0
        simp only [zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [Real.norm_eq_abs]
      exact abs_f_le hθ hx
    · -- limit at `θ⁻`
      have hcont : ContinuousAt (f θ) θ := by
        unfold f
        apply ContinuousAt.mul (by fun_prop)
        apply ContinuousAt.log (by fun_prop)
        exact (div_pos (w_pos hθ) (w_pos hθ)).ne'
      have hval : f θ θ = 0 := by
        simp [f, div_self (w_pos hθ).ne']
      rw [← hval]
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  rw [intervalIntegral.integral_add hhi hki, sub_zero] at hFTC
  have hk : ∫ x in (0 : ℝ)..θ, k x = θ - ∫ x in (0 : ℝ)..θ, x / (Real.exp x - 1) := by
    have hcongr : ∫ x in (0 : ℝ)..θ, k x = ∫ x in (0 : ℝ)..θ, (1 - x / (Real.exp x - 1)) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => ?_)
      rw [uIoc_of_le hθ.le] at hx
      have he := (expm1_pos hx.1).ne'
      simp only [k]
      field_simp
    rw [hcongr, intervalIntegral.integral_sub intervalIntegrable_const hri]
    simp
  change ∫ x in (0 : ℝ)..θ, h θ x = _
  linarith

end FrankDebye

/-- Nelsen, Example 5.4 / Table 4.1 (family 4.2.5): Kendall's tau of Frank's copula in Debye form,
`τ_θ = 1 − (4/θ) (1 − D₁(θ))` for `θ > 0`. -/
theorem kendallTau_frank_debye (θ : ℝ) (hθ : 0 < θ) :
    (frank θ hθ).kendallTau = 1 - 4 / θ * (1 - debyeOne θ) := by
  rw [kendallTau_frank θ hθ]
  have hsub : (∫ t in (0 : ℝ)..1,
      (Real.exp (θ * t) - 1) * Real.log ((1 - Real.exp (-(θ * t))) / (1 - Real.exp (-θ)))) =
      θ⁻¹ * ∫ x in (0 : ℝ)..θ,
        (Real.exp x - 1) * Real.log ((1 - Real.exp (-x)) / (1 - Real.exp (-θ))) := by
    have := intervalIntegral.integral_comp_mul_left
      (fun x => (Real.exp x - 1) * Real.log ((1 - Real.exp (-x)) / (1 - Real.exp (-θ))))
      (a := 0) (b := 1) hθ.ne'
    simpa only [mul_zero, mul_one, smul_eq_mul] using this
  rw [hsub, FrankDebye.frank_integral_eq_debye hθ, debyeOne]
  field_simp
  ring

/-- The integrand `t/(e^t − 1)` of the Debye function is interval integrable on `[0, x]`. -/
theorem intervalIntegrable_debye_integrand {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun t => t / (Real.exp t - 1)) volume 0 x :=
  FrankDebye.intervalIntegrable_of_bound hx (by fun_prop) 1 fun _ ht _ => FrankDebye.abs_ratio_le ht

/-- Reflection identity of the Debye function: `D₁(−x) = D₁(x) + x/2` for `x > 0`. -/
theorem debyeOne_neg {x : ℝ} (hx : 0 < x) : debyeOne (-x) = debyeOne x + x / 2 := by
  have hflip : (∫ t in (0 : ℝ)..-x, t / (Real.exp t - 1)) =
      -∫ s in (0 : ℝ)..x, (-s) / (Real.exp (-s) - 1) := by
    rw [intervalIntegral.integral_comp_neg (fun t => t / (Real.exp t - 1)), neg_zero,
      intervalIntegral.integral_symm]
  have hid : ∀ s ∈ uIoc (0 : ℝ) x, (-s) / (Real.exp (-s) - 1) = s + s / (Real.exp s - 1) := by
    intro s hs
    rw [uIoc_of_le hx.le] at hs
    have he := (FrankDebye.expm1_pos hs.1).ne'
    have hE : Real.exp s * Real.exp (-s) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hn : Real.exp (-s) - 1 ≠ 0 := by
      have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hs.1)
      linarith
    rw [div_eq_iff hn]
    field_simp
    linear_combination (-s) * hE
  rw [debyeOne, debyeOne, hflip,
    intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => hid s hs),
    intervalIntegral.integral_add intervalIntegral.intervalIntegrable_id
      (intervalIntegrable_debye_integrand hx), integral_id]
  field_simp
  ring

/-- Nelsen, Example 5.4 / Table 4.1 (family 4.2.5) for negative parameters: Kendall's tau of
Frank's copula `frankNegative θ` (`θ < 0`) is `1 − (4/θ) (1 − D₁(θ))`. -/
theorem kendallTau_frankNegative_debye (θ : ℝ) (hθ : θ < 0) :
    (frankNegative θ hθ).kendallTau = 1 - 4 / θ * (1 - debyeOne θ) := by
  have hx : 0 < -θ := neg_pos.mpr hθ
  rw [frankNegative, kendallTau_reflect_second, kendallTau_frank_debye (-θ) hx]
  have hD := debyeOne_neg hx
  rw [neg_neg] at hD
  rw [hD]
  have hθ0 : θ ≠ 0 := hθ.ne
  field_simp
  ring

end ProbabilityTheory.Copula
