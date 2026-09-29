/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.SpearmanRhoFrankCalculus
import Copula.Archimedean.DebyeTwo

/-! # The double integral behind Spearman's rho of Frank's copula

With `L θ x y = -log (1 - w x w y / w θ)` (see `Copula.Archimedean.SpearmanRhoFrankCalculus`)
we prove
`∫₀^θ ∫₀^θ L θ x y dy dx = θ³/3 - θ ∫₀^θ t/(e^t-1) dt + 2 ∫₀^θ t²/(e^t-1) dt`
(`FrankRho.H_eq`). The proof writes `L θ x y = min x y + ∫_{max x y}^θ f x y s ds`
(`L_eq_min_add_integral`), exchanges the order of integration (Fubini over the cube
`(0, θ]³`) and evaluates the resulting inner double integrals with `K_eq`.
-/

open MeasureTheory Set Filter Topology

namespace ProbabilityTheory.Copula

namespace FrankRho

/-- The kernel `f x y s` restricted to `max x y ≤ s`. -/
noncomputable def G (x y s : ℝ) : ℝ := if max x y ≤ s then f x y s else 0

theorem measurable_G : Measurable (fun p : ℝ × ℝ × ℝ => G p.1 p.2.1 p.2.2) := by
  unfold G f w
  exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop)
    measurable_const

theorem abs_G_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (s : ℝ) : |G x y s| ≤ 1 := by
  unfold G
  split_ifs with h
  · have hxs := (le_max_left x y).trans h
    have hys := (le_max_right x y).trans h
    have := f_bounds (hx.trans_le hxs) hx.le hxs hy.le hys
    rw [abs_le]
    exact ⟨this.1, by linarith [this.2]⟩
  · simp

theorem G_nested (x y s : ℝ) :
    G x y s = if x ≤ s then (if y ≤ s then f x y s else 0) else 0 := by
  unfold G
  by_cases hx : x ≤ s <;> by_cases hy : y ≤ s <;> simp [hx, hy]

/-- Integral of a truncated function over `(0, θ]`, upper truncation. -/
theorem integral_ite_le {θ s : ℝ} (hs : s ≤ θ) (Q : ℝ → ℝ) :
    ∫ x in Ioc 0 θ, (if x ≤ s then Q x else 0) = ∫ x in Ioc 0 s, Q x := by
  have h : (fun x => if x ≤ s then Q x else 0) = (Iic s).indicator Q := by
    funext x; simp [indicator_apply]
  rw [h, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  congr 2
  ext x
  simp only [mem_inter_iff, mem_Iic, mem_Ioc]
  constructor
  · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hs⟩

/-- Integral of a truncated function over `(0, θ]`, lower truncation. -/
theorem integral_ite_ge {θ m : ℝ} (hm : 0 < m) (g : ℝ → ℝ) :
    ∫ s in Ioc 0 θ, (if m ≤ s then g s else 0) = ∫ s in Ioc m θ, g s := by
  have h : (fun s => if m ≤ s then g s else 0) = (Ici m).indicator g := by
    funext x; simp [indicator_apply]
  rw [h, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  rw [← integral_Icc_eq_integral_Ioc]
  congr 2
  ext x
  simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
  constructor
  · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, hm.trans_le h1, h2⟩

theorem integral_G_s {θ x y : ℝ} (hx : 0 < x) (hxθ : x ≤ θ) (hyθ : y ≤ θ) :
    ∫ s in Ioc 0 θ, G x y s = ∫ s in (max x y)..θ, f x y s := by
  unfold G
  rw [integral_ite_ge (lt_max_of_lt_left hx), intervalIntegral.integral_of_le (max_le hxθ hyθ)]

theorem L_eq_min_add_G {θ x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxθ : x ≤ θ) (hyθ : y ≤ θ) :
    L θ x y = min x y + ∫ s in Ioc 0 θ, G x y s := by
  rw [integral_G_s hx hxθ hyθ, L_eq_min_add_integral hx hy hxθ hyθ]

/-- Bounded measurable functions are integrable for the product of restricted Lebesgue measures. -/
theorem integrable_prod_of_bdd {θ : ℝ} {g : ℝ × ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hb : ∀ p ∈ Ioc 0 θ ×ˢ Ioc 0 θ, |g p| ≤ M) :
    Integrable g ((volume.restrict (Ioc 0 θ)).prod (volume.restrict (Ioc 0 θ))) := by
  rw [Measure.prod_restrict]
  refine Measure.integrableOn_of_bounded (M := M) ?_ hg.aestronglyMeasurable ?_
  · rw [show (volume : Measure ℝ).prod volume = volume from rfl, Measure.volume_eq_prod,
      Measure.prod_prod]
    simp [Real.volume_Ioc, ENNReal.mul_eq_top]
  · rw [ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)]
    exact Eventually.of_forall fun p hp => by simpa [Real.norm_eq_abs] using hb p hp

/-- The mean of `min x y` over `y ∈ (0, θ]`. -/
theorem integral_min {θ x : ℝ} (hx : 0 ≤ x) (hxθ : x ≤ θ) :
    ∫ y in Ioc 0 θ, min x y = x * θ - x ^ 2 / 2 := by
  have hc : Continuous fun y : ℝ => min x y := continuous_const.min continuous_id
  rw [← intervalIntegral.integral_of_le (hx.trans hxθ),
    ← intervalIntegral.integral_add_adjacent_intervals (b := x)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ y in (0 : ℝ)..x, min x y = ∫ y in (0 : ℝ)..x, y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hx] at hy
    exact min_eq_right hy.2
  have h2 : ∫ y in x..θ, min x y = ∫ y in x..θ, x := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hxθ] at hy
    exact min_eq_left hy.1
  rw [h1, h2]
  simp
  ring

theorem integral_min_min {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫ x in Ioc 0 θ, (x * θ - x ^ 2 / 2) = θ ^ 3 / 3 := by
  rw [← intervalIntegral.integral_of_le hθ,
    intervalIntegral.integral_sub ((by fun_prop : Continuous fun x : ℝ => x * θ).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x : ℝ => x ^ 2 / 2).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_mul_const, integral_id, intervalIntegral.integral_div,
    integral_pow]
  ring

/-- The `y`-integral of the truncated kernel. -/
noncomputable def h (θ x s : ℝ) : ℝ := ∫ y in Ioc 0 θ, G x y s

theorem integrable_G_ys {θ x : ℝ} (hx : 0 < x) :
    Integrable (fun p : ℝ × ℝ => G x p.1 p.2)
      ((volume.restrict (Ioc 0 θ)).prod (volume.restrict (Ioc 0 θ))) :=
  integrable_prod_of_bdd (M := 1)
    (measurable_G.comp (by fun_prop : Measurable fun p : ℝ × ℝ => (x, p.1, p.2)))
    (fun p hp => abs_G_le hx hp.1.1 p.2)

theorem integrable_h {θ : ℝ} :
    Integrable (fun p : ℝ × ℝ => h θ p.1 p.2)
      ((volume.restrict (Ioc 0 θ)).prod (volume.restrict (Ioc 0 θ))) := by
  have hm : StronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => G q.1.1 q.2 q.1.2) :=
    (measurable_G.comp
      (by fun_prop : Measurable fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2, q.1.2))).stronglyMeasurable
  have hm2 := hm.integral_prod_right' (ν := volume.restrict (Ioc 0 θ))
  refine integrable_prod_of_bdd (M := volume.real (Ioc 0 θ)) hm2.measurable ?_
  intro p hp
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc 0 θ)
    (f := fun y => G p.1 y p.2) (C := 1) (by simp [Real.volume_Ioc])
    (fun y hy => by simpa [Real.norm_eq_abs] using abs_G_le hp.1.1 hy.1 p.2)
  simpa [h, Real.norm_eq_abs] using this

theorem inner_swap {θ x : ℝ} (hx : 0 < x) :
    ∫ y in Ioc 0 θ, ∫ s in Ioc 0 θ, G x y s = ∫ s in Ioc 0 θ, h θ x s :=
  integral_integral_swap (f := fun y s => G x y s) (integrable_G_ys hx)

theorem H_triple {θ : ℝ} (hθ : 0 < θ) :
    ∫ x in Ioc 0 θ, ∫ y in Ioc 0 θ, L θ x y =
      θ ^ 3 / 3 + ∫ s in Ioc 0 θ, ∫ x in Ioc 0 θ, h θ x s := by
  have step1 : ∀ x ∈ Ioc 0 θ, ∫ y in Ioc 0 θ, L θ x y =
      (x * θ - x ^ 2 / 2) + ∫ s in Ioc 0 θ, h θ x s := by
    intro x hx
    have e1 : ∫ y in Ioc 0 θ, L θ x y =
        ∫ y in Ioc 0 θ, (min x y + ∫ s in Ioc 0 θ, G x y s) :=
      setIntegral_congr_fun measurableSet_Ioc fun y hy =>
        L_eq_min_add_G hx.1 hy.1 hx.2 hy.2
    have hmin : Integrable (fun y => min x y) (volume.restrict (Ioc 0 θ)) :=
      (continuous_const.min continuous_id).integrableOn_Ioc
    have hI3 := (integrable_G_ys (θ := θ) hx.1).integral_prod_left
    rw [e1, integral_add hmin hI3, integral_min hx.1.le hx.2, inner_swap hx.1]
  rw [setIntegral_congr_fun measurableSet_Ioc step1]
  have ha : Integrable (fun x : ℝ => x * θ - x ^ 2 / 2) (volume.restrict (Ioc 0 θ)) :=
    (by fun_prop : Continuous fun x : ℝ => x * θ - x ^ 2 / 2).integrableOn_Ioc
  rw [integral_add ha (integrable_h (θ := θ)).integral_prod_left, integral_min_min hθ.le]
  congr 1
  exact integral_integral_swap (f := fun x s => h θ x s) (integrable_h (θ := θ))

theorem integral_h {θ s : ℝ} (hsθ : s ≤ θ) :
    ∫ x in Ioc 0 θ, h θ x s = ∫ x in Ioc 0 s, ∫ y in Ioc 0 s, f x y s := by
  have hx : ∀ x : ℝ, h θ x s = if x ≤ s then ∫ y in Ioc 0 s, f x y s else 0 := by
    intro x
    unfold h
    by_cases hxs : x ≤ s
    · simp only [hxs, ↓reduceIte]
      have : ∀ y : ℝ, G x y s = if y ≤ s then f x y s else 0 := fun y => by
        simp [G_nested, hxs]
      simp_rw [this]
      exact integral_ite_le hsθ (fun y => f x y s)
    · simp only [hxs, ↓reduceIte]
      have : ∀ y : ℝ, G x y s = 0 := fun y => by simp [G_nested, hxs]
      simp [this]
  simp_rw [hx]
  exact integral_ite_le hsθ (fun x => ∫ y in Ioc 0 s, f x y s)

/-- `S θ = ∫₀^θ t/(e^t - 1) dt = θ D₁(θ)`. -/
noncomputable def S (θ : ℝ) : ℝ := ∫ t in (0 : ℝ)..θ, t / (Real.exp t - 1)

/-- `T θ = ∫₀^θ t²/(e^t - 1) dt = (θ²/2) D₂(θ)`. -/
noncomputable def T (θ : ℝ) : ℝ := ∫ t in (0 : ℝ)..θ, t ^ 2 / (Real.exp t - 1)

theorem expm1_ne {s : ℝ} (hs : 0 < s) : Real.exp s - 1 ≠ 0 := by
  have := Real.add_one_lt_exp hs.ne'
  intro h; linarith

theorem hasDerivAt_S {s : ℝ} (hs : 0 < s) : HasDerivAt S (s / (Real.exp s - 1)) s := by
  have hm : Measurable fun t : ℝ => t / (Real.exp t - 1) := by fun_prop
  have hc : ContinuousAt (fun t : ℝ => t / (Real.exp t - 1)) s :=
    continuousAt_id.div (by fun_prop) (expm1_ne hs)
  have hi := intervalIntegrable_debye_integrand hs
  have hf : StronglyMeasurableAtFilter (fun t : ℝ => t / (Real.exp t - 1)) (𝓝 s) volume :=
    hm.stronglyMeasurable.stronglyMeasurableAtFilter
  exact intervalIntegral.integral_hasDerivAt_right hi hf hc

theorem hasDerivAt_T {s : ℝ} (hs : 0 < s) : HasDerivAt T (s ^ 2 / (Real.exp s - 1)) s := by
  have hm : Measurable fun t : ℝ => t ^ 2 / (Real.exp t - 1) := by fun_prop
  have hc : ContinuousAt (fun t : ℝ => t ^ 2 / (Real.exp t - 1)) s :=
    (continuousAt_id.pow 2).div (by fun_prop) (expm1_ne hs)
  have hi := intervalIntegrable_debyeTwo_integrand hs
  have hf : StronglyMeasurableAtFilter (fun t : ℝ => t ^ 2 / (Real.exp t - 1)) (𝓝 s) volume :=
    hm.stronglyMeasurable.stronglyMeasurableAtFilter
  exact intervalIntegral.integral_hasDerivAt_right hi hf hc

theorem continuousOn_S {θ : ℝ} (hθ : 0 < θ) : ContinuousOn S (Icc 0 θ) := by
  have h := intervalIntegral.continuousOn_primitive_interval' (intervalIntegrable_debye_integrand hθ)
    (left_mem_uIcc (a := (0 : ℝ)) (b := θ))
  rwa [uIcc_of_le hθ.le] at h

theorem continuousOn_T {θ : ℝ} (hθ : 0 < θ) : ContinuousOn T (Icc 0 θ) := by
  have h := intervalIntegral.continuousOn_primitive_interval' (intervalIntegrable_debyeTwo_integrand hθ)
    (left_mem_uIcc (a := (0 : ℝ)) (b := θ))
  rwa [uIcc_of_le hθ.le] at h

theorem integral_S {θ : ℝ} (hθ : 0 < θ) : ∫ s in (0 : ℝ)..θ, S s = θ * S θ - T θ := by
  have hcont : ContinuousOn (fun s => s * S s - T s) (Icc 0 θ) :=
    (continuousOn_id.mul (continuousOn_S hθ)).sub (continuousOn_T hθ)
  have hSint : IntervalIntegrable S volume 0 θ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hθ.le]; exact continuousOn_S hθ
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hθ.le hcont
    (f' := S) (fun x hx => by
      have := (((hasDerivAt_id x).mul (hasDerivAt_S hx.1)).sub (hasDerivAt_T hx.1))
      refine (this.congr_deriv ?_).hasDerivWithinAt
      simp only [id]
      ring) hSint
  rw [h]
  simp [S, T]

theorem H_eq {θ : ℝ} (hθ : 0 < θ) :
    ∫ x in (0 : ℝ)..θ, ∫ y in (0 : ℝ)..θ, L θ x y = θ ^ 3 / 3 - θ * S θ + 2 * T θ := by
  simp_rw [intervalIntegral.integral_of_le hθ.le]
  rw [H_triple hθ]
  have hK : ∀ s ∈ Ioc 0 θ, ∫ x in Ioc 0 θ, h θ x s =
      s ^ 2 / (Real.exp s - 1) - S s := by
    intro s hs
    rw [integral_h hs.2, ← intervalIntegral.integral_of_le hs.1.le]
    simp_rw [← intervalIntegral.integral_of_le hs.1.le]
    exact K_eq hs.1
  rw [setIntegral_congr_fun measurableSet_Ioc hK, ← intervalIntegral.integral_of_le hθ.le,
    intervalIntegral.integral_sub (intervalIntegrable_debyeTwo_integrand hθ)
      (by apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le hθ.le]; exact continuousOn_S hθ),
    integral_S hθ]
  change θ ^ 3 / 3 + (T θ - (θ * S θ - T θ)) = _
  ring

end FrankRho

end ProbabilityTheory.Copula
