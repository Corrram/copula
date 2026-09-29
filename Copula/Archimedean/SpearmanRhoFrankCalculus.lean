/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.KendallTauFrankDebye

/-! # Elementary calculus for Spearman's rho of Frank's copula

Put `w x = 1 - e^{-x}` and, for `θ > 0` and `x, y ∈ (0, θ]`,
`L θ x y = -log (1 - w x * w y / w θ)`, so that `θ * C_θ(u, v) = L θ (θ u) (θ v)` for Frank's
copula. This file collects the one-variable computations behind
`Copula.Archimedean.SpearmanRhoFrankCore`:

* `hasDerivAt_L`: the derivative of `θ ↦ L θ x y` is `f x y θ = e^{-θ} (1/w θ - 1/(w θ - w x w y))`;
* `L_eq_min_add_integral`: `L θ x y = min x y + ∫_{max x y}^θ f x y s ds`;
* `K_eq`: `∫₀^s ∫₀^s f x y s dy dx = s²/(e^s - 1) - ∫₀^s t/(e^t - 1) dt`.
-/

open MeasureTheory Set Filter Topology

namespace ProbabilityTheory.Copula

namespace FrankRho

/-- `w x = 1 - e^{-x}`. -/
noncomputable def w (x : ℝ) : ℝ := 1 - Real.exp (-x)

/-- `L θ x y = -log (1 - w x * w y / w θ)`, i.e. `θ` times Frank's cdf at `(x/θ, y/θ)`. -/
noncomputable def L (θ x y : ℝ) : ℝ := -Real.log (1 - w x * w y / w θ)

/-- The `θ`-derivative of `L θ x y`. -/
noncomputable def f (x y s : ℝ) : ℝ := Real.exp (-s) * (1 / w s - 1 / (w s - w x * w y))

theorem w_pos {x : ℝ} (hx : 0 < x) : 0 < w x := by
  have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
  unfold w; linarith

theorem w_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ w x := by
  have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  unfold w; linarith

theorem w_lt_one (x : ℝ) : w x < 1 := by
  have := Real.exp_pos (-x)
  unfold w; linarith

theorem w_mono {x y : ℝ} (h : x ≤ y) : w x ≤ w y := by
  have := Real.exp_le_exp.mpr (neg_le_neg h)
  unfold w; linarith

theorem sub_pos' {θ x y : ℝ} (hθ : 0 < θ) (hxθ : x ≤ θ) (hy : 0 ≤ y) :
    0 < w θ - w x * w y := by
  have h1 := w_pos hθ
  have h2 := w_mono hxθ
  have h3 := w_nonneg hy
  have h4 := w_lt_one y
  nlinarith [mul_nonneg (sub_nonneg.mpr h2) h3, mul_pos h1 (sub_pos.mpr h4)]

theorem hasDerivAt_w (s : ℝ) : HasDerivAt w (Real.exp (-s)) s := by
  have h := ((hasDerivAt_id s).neg.exp).const_sub 1
  refine h.congr_deriv ?_
  simp

theorem hasDerivAt_L {x y s : ℝ} (hs : 0 < s) (hxs : x ≤ s) (hy : 0 ≤ y) :
    HasDerivAt (fun t => L t x y) (f x y s) s := by
  have hws := w_pos hs
  have hpos := sub_pos' hs hxs hy
  have hne : w s - w x * w y ≠ 0 := hpos.ne'
  have hq : HasDerivAt (fun t => 1 - w x * w y / w t)
      (-((0 * w s - w x * w y * Real.exp (-s)) / w s ^ 2)) s :=
    ((hasDerivAt_const s (w x * w y)).div (hasDerivAt_w s) hws.ne').const_sub 1
  have hq0 : 1 - w x * w y / w s ≠ 0 := by
    have : 1 - w x * w y / w s = (w s - w x * w y) / w s := by field_simp
    rw [this]; exact div_ne_zero hne hws.ne'
  have hl := (hq.log hq0).neg
  refine hl.congr_deriv ?_
  unfold f
  field_simp
  ring

theorem L_left {x y : ℝ} (hx : 0 < x) : L x x y = y := by
  unfold L
  rw [mul_div_cancel_left₀ _ (w_pos hx).ne']
  unfold w
  rw [sub_sub_cancel, Real.log_exp, neg_neg]

theorem L_right {x y : ℝ} (hy : 0 < y) : L y x y = x := by
  unfold L
  rw [mul_div_cancel_right₀ _ (w_pos hy).ne']
  unfold w
  rw [sub_sub_cancel, Real.log_exp, neg_neg]

theorem L_max {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : L (max x y) x y = min x y := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, min_eq_left h]; exact L_right hy
  · rw [max_eq_left h, min_eq_right h]; exact L_left hx

theorem continuousOn_f {x y a b : ℝ} (ha : 0 < a) (hxa : x ≤ a) (hy : 0 ≤ y) :
    ContinuousOn (f x y) (Icc a b) := by
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
  have h1 := (w_pos hs0).ne'
  have h2 := (sub_pos' hs0 (hxa.trans hs.1) hy).ne'
  refine ContinuousAt.continuousWithinAt ?_
  unfold f w at *
  refine ContinuousAt.mul (by fun_prop) (ContinuousAt.sub ?_ ?_)
  · exact continuousAt_const.div (by fun_prop) h1
  · exact continuousAt_const.div (by fun_prop) h2

theorem L_eq_min_add_integral {θ x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxθ : x ≤ θ)
    (hyθ : y ≤ θ) :
    L θ x y = min x y + ∫ s in (max x y)..θ, f x y s := by
  have hm : max x y ≤ θ := max_le hxθ hyθ
  have hm0 : 0 < max x y := lt_max_of_lt_left hx
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => L t x y)
    (f' := f x y) (a := max x y) (b := θ)
    (fun s hs => by
      rw [uIcc_of_le hm] at hs
      exact hasDerivAt_L (hm0.trans_le hs.1) ((le_max_left x y).trans hs.1) hy.le)
    (by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hm]
      exact continuousOn_f hm0 (le_max_left x y) hy.le)
  rw [h, L_max hx hy]
  ring

theorem f_bounds {x y s : ℝ} (hs : 0 < s) (hx0 : 0 ≤ x) (hxs : x ≤ s) (hy0 : 0 ≤ y)
    (hys : y ≤ s) : -1 ≤ f x y s ∧ f x y s ≤ 0 := by
  have hg := w_pos hs
  have hpos := sub_pos' hs hxs hy0
  have hwx0 := w_nonneg hx0
  have hwy0 := w_nonneg hy0
  have hwx := w_mono hxs
  have hwy := w_mono hys
  have hc0 : 0 ≤ w x * w y := mul_nonneg hwx0 hwy0
  have hc1 : w x * w y ≤ w s * w s := mul_le_mul hwx hwy hwy0 hg.le
  have he : Real.exp (-s) + w s = 1 := by unfold w; ring
  have he0 := Real.exp_pos (-s)
  have key : f x y s = -(Real.exp (-s) * (w x * w y)) / (w s * (w s - w x * w y)) := by
    unfold f
    field_simp
    ring
  rw [key]
  have hden : 0 < w s * (w s - w x * w y) := mul_pos hg hpos
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith [mul_nonneg he0.le hc0]
  · exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [mul_nonneg he0.le hc0]) hden.le

/-- The inner integral: `∫₀^s dy / (w s - w x w y) = (s - x)/(e^{-x} - e^{-s})` for `0 ≤ x < s`. -/
theorem inner_integral {x s : ℝ} (hx : 0 ≤ x) (hxs : x < s) :
    ∫ y in (0 : ℝ)..s, 1 / (w s - w x * w y) = (s - x) / (Real.exp (-x) - Real.exp (-s)) := by
  have hs : 0 < s := hx.trans_lt hxs
  set c := Real.exp (-x) - Real.exp (-s) with hc
  have hcpos : 0 < c := by
    have := Real.exp_lt_exp.mpr (neg_lt_neg hxs)
    linarith
  set α := w x with hα
  have hα0 : 0 ≤ α := w_nonneg hx
  have hden : ∀ y : ℝ, w s - α * w y = c + α * Real.exp (-y) := by
    intro y
    simp only [hc, hα, w]; ring
  have hpos : ∀ y : ℝ, 0 < c + α * Real.exp (-y) := fun y => by
    have := Real.exp_pos (-y)
    positivity
  have hderiv : ∀ y ∈ uIcc (0 : ℝ) s,
      HasDerivAt (fun y => (y + Real.log (c + α * Real.exp (-y))) / c)
        (1 / (w s - α * w y)) y := by
    intro y _
    have h1 : HasDerivAt (fun y : ℝ => c + α * Real.exp (-y))
        (α * (Real.exp (-y) * -1)) y := by
      have := (((hasDerivAt_id y).neg.exp).const_mul α).const_add c
      simpa using this
    have h2 := ((hasDerivAt_id y).add (h1.log (hpos y).ne')).div_const c
    refine h2.congr_deriv ?_
    rw [hden y]
    have := (hpos y).ne'
    field_simp
    ring
  have hint : IntervalIntegrable (fun y : ℝ => 1 / (w s - α * w y)) volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    intro y _
    refine ContinuousAt.continuousWithinAt ?_
    have : (fun y : ℝ => 1 / (w s - α * w y)) = fun y => 1 / (c + α * Real.exp (-y)) := by
      funext y; rw [hden y]
    rw [this]
    exact continuousAt_const.div (by fun_prop) (hpos y).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [neg_zero, Real.exp_zero, mul_one, zero_add]
  have h1 : c + α * Real.exp (-s) = Real.exp (-x) * w s := by
    simp only [hc, hα, w]; ring
  have h2 : c + α = w s := by simp only [hc, hα, w]; ring
  rw [h1, h2, Real.log_mul (Real.exp_pos _).ne' (w_pos hs).ne', Real.log_exp]
  field_simp
  ring

theorem F_eq (s : ℝ) : (fun z : ℝ => z / (Real.exp (-(s - z)) - Real.exp (-s))) =
    fun z => Real.exp s * (z / (Real.exp z - 1)) := by
  funext z
  by_cases hz : z = 0
  · simp [hz]
  have hE : Real.exp s * Real.exp (-s) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hE2 : Real.exp (-(s - z)) = Real.exp (-s) * Real.exp z := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hE2]
  by_cases hz1 : Real.exp z - 1 = 0
  · have : Real.exp (-s) * Real.exp z - Real.exp (-s) = 0 := by
      have : Real.exp (-s) * Real.exp z - Real.exp (-s) = Real.exp (-s) * (Real.exp z - 1) := by
        ring
      rw [this, hz1, mul_zero]
    rw [this, hz1]; simp
  · have hpos := Real.exp_pos s
    have hpos' := Real.exp_pos (-s)
    have : Real.exp (-s) * Real.exp z - Real.exp (-s) ≠ 0 := by
      have : Real.exp (-s) * Real.exp z - Real.exp (-s) = Real.exp (-s) * (Real.exp z - 1) := by
        ring
      rw [this]; exact mul_ne_zero hpos'.ne' hz1
    field_simp
    linear_combination (-1) * hE

/-- Substitution `z = s - x` in the outer integral. -/
theorem J_integral {s : ℝ} :
    ∫ x in (0 : ℝ)..s, (s - x) / (Real.exp (-x) - Real.exp (-s)) =
      Real.exp s * ∫ z in (0 : ℝ)..s, z / (Real.exp z - 1) := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun z : ℝ => z / (Real.exp (-(s - z)) - Real.exp (-s))) (a := 0) (b := s) s
  simp only [sub_sub_cancel, sub_self, sub_zero] at h
  rw [h, F_eq s, intervalIntegral.integral_const_mul]

theorem intervalIntegrable_G {s : ℝ} (hs : 0 < s) :
    IntervalIntegrable (fun x : ℝ => (s - x) / (Real.exp (-x) - Real.exp (-s))) volume 0 s := by
  have h1 : IntervalIntegrable (fun z : ℝ => z / (Real.exp (-(s - z)) - Real.exp (-s)))
      volume 0 s := by
    rw [F_eq s]
    exact (intervalIntegrable_debye_integrand hs).const_mul _
  have h2 := h1.comp_sub_left s
  simp only [sub_sub_cancel, sub_self, sub_zero] at h2
  exact h2.symm

theorem intervalIntegrable_inv {x s : ℝ} (hs : 0 < s) (hxs : x ≤ s) :
    IntervalIntegrable (fun y : ℝ => 1 / (w s - w x * w y)) volume 0 s := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  rw [uIcc_of_le hs.le] at hy
  have h2 := (sub_pos' hs hxs hy.1).ne'
  refine ContinuousAt.continuousWithinAt ?_
  unfold w at *
  exact continuousAt_const.div (by fun_prop) h2

/-- The key computation: `∫₀^s ∫₀^s f x y s dy dx = s²/(e^s - 1) - ∫₀^s t/(e^t - 1) dt`. -/
theorem K_eq {s : ℝ} (hs : 0 < s) :
    ∫ x in (0 : ℝ)..s, ∫ y in (0 : ℝ)..s, f x y s =
      s ^ 2 / (Real.exp s - 1) - ∫ t in (0 : ℝ)..s, t / (Real.exp t - 1) := by
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({s} : Set ℝ) :=
    (Set.countable_singleton s).ae_notMem _
  have hstep : ∀ x ∈ Ioo (0 : ℝ) s, ∫ y in (0 : ℝ)..s, f x y s =
      s * (Real.exp (-s) / w s) - Real.exp (-s) * ((s - x) / (Real.exp (-x) - Real.exp (-s))) := by
    intro x hx
    have hfeq : ∀ y : ℝ, f x y s = Real.exp (-s) / w s - Real.exp (-s) * (1 / (w s - w x * w y)) := by
      intro y; unfold f; ring
    simp_rw [hfeq]
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((intervalIntegrable_inv hs hx.2.le).const_mul _), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, inner_integral hx.1.le hx.2]
    simp
  rw [intervalIntegral.integral_congr_ae (g := fun x => s * (Real.exp (-s) / w s) -
      Real.exp (-s) * ((s - x) / (Real.exp (-x) - Real.exp (-s))))]
  · rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((intervalIntegrable_G hs).const_mul _), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, J_integral]
    have hs1 : Real.exp s - 1 ≠ 0 := by
      have := Real.add_one_lt_exp hs.ne'
      linarith
    have hE0 := (Real.exp_pos s).ne'
    have hw : 1 - (Real.exp s)⁻¹ ≠ 0 := by
      have : 1 - (Real.exp s)⁻¹ = (Real.exp s - 1) / Real.exp s := by field_simp
      rw [this]; exact div_ne_zero hs1 hE0
    simp only [smul_eq_mul, sub_zero, w, Real.exp_neg]
    field_simp
  · filter_upwards [hae] with x hx hxI
    rw [uIoc_of_le hs.le] at hxI
    exact hstep x ⟨hxI.1, lt_of_le_of_ne hxI.2 hx⟩

end FrankRho

end ProbabilityTheory.Copula
