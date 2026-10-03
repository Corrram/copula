/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Multivariate.SpearmanLowerBoundStrict

/-!
# A sharp lower bound for multivariate Spearman's rho: the dual certificate

For a `d`-copula `C` (law of `U = (U₁, …, U_d)`) we have `∫ C dΠ = E[∏ᵢ (1 - Uᵢ)]`
(`integral_cdf_independence_eq_prod`), and `Xᵢ = -log(1 - Uᵢ)` are standard exponential, so
minimizing `∫ C dΠ` (equivalently the multivariate Spearman's rho
`ρ_d(C) = (d+1)/(2^d - d - 1) · (2^d ∫ C dΠ - 1)`) is the problem of minimizing `E[exp(-∑ Xᵢ)]`
over all dependence structures of `d` exponential variables. Since the exponential distribution
has a decreasing density, the minimal sum in convex order is known (Wang–Wang 2011,
Bernard–Jiang–Wang 2014): one large and `d - 1` small values on a tail event of probability
`d c_d`, and a joint mix (constant sum) in the middle. This file proves the matching **lower
bound** by an explicit dual certificate; for `c = c_d` it equals that minimum (see below).

## The certificate

Put `vᵢ = 1 - Uᵢ ∈ (0, 1]`, `P = ∏ vᵢ`, and for `0 < x ≤ 1/(d(d-1))`

* `q(x) = x (1 - (d-1)x)^{d-1}` (`level`), with derivative `q'(x) ≥ 0` (`levelDeriv`);
* `κ_x(v) = max(x, min(v, 1 - (d-1)x))` (`clampLevel`).

**Pointwise inequality** (`prod_clampLevel_le`): `∏ᵢ κ_x(vᵢ) ≤ max(q(x), P)`: if some `vᵢ < x`
then that factor is `x` and the others are `≤ 1 - (d-1)x`; otherwise `κ_x(vᵢ) ≤ vᵢ`.
Taking logarithms and integrating against `q'(x) dx` over `(0, c]`, together with
`∫₀ᶜ q'(x) max(0, log P - log q(x)) dx ≤ P` (`integral_levelDeriv_posPart_le`), gives the
pointwise dual inequality `∑ᵢ ψ_c(vᵢ) - Q_c ≤ P` (`sum_dualFunction_sub_le_prod`) with
`ψ_c(v) = ∫₀ᶜ q'(x) log κ_x(v) dx` and `Q_c = ∫₀ᶜ q' log q = q(c) log q(c) - q(c)`. Integrating
against `C` and using uniform marginals and Fubini (`∫₀¹ log κ_x(v) dv = log(1-(d-1)x) + dx - 1`)
yields the main result:

* `dualBound_le_integral_cdf`: for `d ≥ 2`, `0 < c`, `c d (d-1) ≤ 1` and every `d`-copula,
  `∫ C dΠ ≥ L_d(c) := d ∫₀ᶜ q'(x) (log(1 - (d-1)x) + d x - 1) dx - q(c) log q(c) + q(c)`;
* `dualBound_le_multivariateSpearmanRho`: the corresponding bound for `ρ_d`.

## Sharpness (not formalized)

Maximizing over `c`, the optimum `c_d` solves `H(c) = D(c)` of Bernard–Jiang–Wang; for `d = 3`
this is `log((1 - 2c)/c) = 3 - 9c`, `c₃ ≈ 0.0945416`, and `L₃(c₃) = c₃ - 11c₃²/2 + 12c₃³ - 9c₃⁴
≈ 0.0548032` (`Copula.Multivariate.SpearmanInfimumThree`). Numerically `L_d(c_d)` coincides
with `E[exp(-T)]` for the convex-order minimal sum `T` of Bernard–Jiang–Wang (2014, Theorem 2.1),
which is attained by a copula whose middle part is a joint mix (Wang–Wang 2011, Theorem 2.4), so
the bound is the exact infimum: `inf ρ₃ ≈ -0.5615741`, `inf ρ₄ ≈ -0.3156518`,
`inf ρ₅ ≈ -0.1801073`. The attainment (existence of the joint mix) is not formalized here.

References: B. Wang and R. Wang, *The complete mixability and convex minimization problems with
monotone marginal densities*, J. Multivariate Anal. 102 (2011) 1344–1360; C. Bernard, X. Jiang
and R. Wang, *Risk aggregation with dependence uncertainty*, Insurance Math. Econom. 54 (2014)
93–108; E. Jakobsons, X. Han and R. Wang, *General convex order on risk aggregation*, Scand.
Actuar. J. 2016, 713–740.
-/

open MeasureTheory Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

namespace SpearmanInfimum

variable {d : ℕ}

/-- The tail level `q_d(x) = x (1 - (d-1) x)^{d-1}`. -/
noncomputable def level (d : ℕ) (x : ℝ) : ℝ := x * (1 - ((d : ℝ) - 1) * x) ^ (d - 1)

/-- The derivative of `level`: `(1 - (d-1)x)^{d-1} - (d-1)² x (1 - (d-1)x)^{d-2}`. -/
noncomputable def levelDeriv (d : ℕ) (x : ℝ) : ℝ :=
  (1 - ((d : ℝ) - 1) * x) ^ (d - 1) - ((d : ℝ) - 1) ^ 2 * x * (1 - ((d : ℝ) - 1) * x) ^ (d - 2)

/-- The clamp `κ_x(v) = max(x, min(v, 1 - (d-1)x))`. -/
noncomputable def clampLevel (d : ℕ) (x v : ℝ) : ℝ := max x (min v (1 - ((d : ℝ) - 1) * x))

theorem hasDerivAt_level (hd : 2 ≤ d) (x : ℝ) : HasDerivAt (level d) (levelDeriv d x) x := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  have h1 : (n + 2 - 1 : ℕ) = n + 1 := by omega
  have h2 : (n + 2 - 2 : ℕ) = n := by omega
  have hb : HasDerivAt (fun y : ℝ => 1 - (((n + 2 : ℕ) : ℝ) - 1) * y)
      (-(((n + 2 : ℕ) : ℝ) - 1)) x := by
    simpa using ((hasDerivAt_id x).const_mul (((n + 2 : ℕ) : ℝ) - 1)).const_sub 1
  have h := (hasDerivAt_id' x).mul (hb.pow (n + 1))
  unfold level levelDeriv
  rw [h1, h2]
  convert h using 1
  simp only [Pi.pow_apply, Nat.add_sub_cancel]
  push_cast
  ring

theorem continuous_level (d : ℕ) : Continuous (level d) := by
  unfold level
  fun_prop

/-- Positivity of the base `1 - (d-1)x` and `x ≤ 1 - (d-1)x` in the admissible range. -/
theorem le_base (hd : 2 ≤ d) {x : ℝ} (hx : 0 ≤ x) (hxd : x * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) :
    x ≤ 1 - ((d : ℝ) - 1) * x := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith [mul_nonneg hx (sub_nonneg.2 hd')]

theorem levelDeriv_nonneg (hd : 2 ≤ d) {x : ℝ} (hx : 0 ≤ x)
    (hxd : x * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) : 0 ≤ levelDeriv d x := by
  have hb := le_base hd hx hxd
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  have h1 : (n + 2 - 1 : ℕ) = n + 1 := by omega
  have h2 : (n + 2 - 2 : ℕ) = n := by omega
  unfold levelDeriv
  rw [h1, h2, pow_succ]
  push_cast at hxd hb ⊢
  have hb0 : 0 ≤ 1 - ((n : ℝ) + 2 - 1) * x := hx.trans hb
  have : 0 ≤ (1 - ((n : ℝ) + 2 - 1) * x) - ((n : ℝ) + 2 - 1) ^ 2 * x := by nlinarith
  have := mul_nonneg (pow_nonneg hb0 n) this
  linarith

theorem level_pos (hd : 2 ≤ d) {x : ℝ} (hx : 0 < x) (hxd : x * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) :
    0 < level d x :=
  mul_pos hx (pow_pos (hx.trans_le (le_base hd hx.le hxd)) _)

theorem level_zero : level d 0 = 0 := by simp [level]

/-- `level` is monotone on the admissible range `[0, c]`. -/
theorem monotoneOn_level (hd : 2 ≤ d) {c : ℝ} (hc : c * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) :
    MonotoneOn (level d) (Icc 0 c) := by
  have hdd : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) - 1) := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 c) (continuous_level d).continuousOn
  · exact fun x _ => (hasDerivAt_level hd x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_level hd x).deriv]
    exact levelDeriv_nonneg hd hx.1.le (by nlinarith [hx.2])

/-! ### The pointwise inequality -/

theorem clampLevel_nonneg {x v : ℝ} (hx : 0 ≤ x) : 0 ≤ clampLevel d x v :=
  hx.trans (le_max_left _ _)

theorem clampLevel_le_base {x v : ℝ} (hb : x ≤ 1 - ((d : ℝ) - 1) * x) :
    clampLevel d x v ≤ 1 - ((d : ℝ) - 1) * x :=
  max_le hb (min_le_right _ _)

/-- **The pointwise inequality**: `∏ᵢ κ_x(vᵢ) ≤ max(q(x), ∏ᵢ vᵢ)`. -/
theorem prod_clampLevel_le {x : ℝ} (hx : 0 ≤ x) (hb : x ≤ 1 - ((d : ℝ) - 1) * x)
    (v : Fin d → ℝ) :
    ∏ i, clampLevel d x (v i) ≤ max (level d x) (∏ i, v i) := by
  by_cases h : ∃ i, v i < x
  · obtain ⟨i, hi⟩ := h
    have hci : clampLevel d x (v i) = x := max_eq_left ((min_le_left _ _).trans hi.le)
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), hci]
    apply le_max_of_le_left
    unfold level
    apply mul_le_mul_of_nonneg_left _ hx
    calc ∏ j ∈ Finset.univ.erase i, clampLevel d x (v j)
        ≤ ∏ _j ∈ Finset.univ.erase i, (1 - ((d : ℝ) - 1) * x) :=
          Finset.prod_le_prod₀ (fun j _ => clampLevel_nonneg hx) (fun j _ => clampLevel_le_base hb)
      _ = (1 - ((d : ℝ) - 1) * x) ^ (d - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
            Fintype.card_fin]
  · push Not at h
    apply le_max_of_le_right
    exact Finset.prod_le_prod₀ (fun i _ => clampLevel_nonneg hx)
      (fun i _ => max_le (h i) (min_le_left _ _))

/-- Logarithmic form of the pointwise inequality. -/
theorem sum_log_clampLevel_sub_le (hd : 2 ≤ d) {x : ℝ} (hx : 0 < x)
    (hxd : x * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) {v : Fin d → ℝ} (hv : ∀ i, 0 < v i) :
    ∑ i, Real.log (clampLevel d x (v i)) - Real.log (level d x) ≤
      max 0 (Real.log (∏ i, v i) - Real.log (level d x)) := by
  have hb := le_base hd hx.le hxd
  have hq := level_pos hd hx hxd
  have hP : 0 < ∏ i, v i := Finset.prod_pos fun i _ => hv i
  have hcl : ∀ i, 0 < clampLevel d x (v i) := fun i => hx.trans_le (le_max_left _ _)
  rw [← Real.log_prod fun i _ => (hcl i).ne']
  have hle := prod_clampLevel_le (d := d) hx.le hb v
  have hpos : 0 < ∏ i, clampLevel d x (v i) := Finset.prod_pos fun i _ => hcl i
  rcases le_total (level d x) (∏ i, v i) with h | h
  · rw [max_eq_right h] at hle
    have := Real.log_le_log hpos hle
    exact le_max_of_le_right (by linarith)
  · rw [max_eq_left h] at hle
    have := Real.log_le_log hpos hle
    exact le_max_of_le_left (by linarith)

/-! ### The integral of the positive part -/

/-- The antiderivative `F(x) = q(x) (log P - log q(x) + 1)`. -/
private noncomputable def antider (d : ℕ) (P x : ℝ) : ℝ :=
  level d x * Real.log P - level d x * Real.log (level d x) + level d x

private theorem continuous_antider (d : ℕ) (P : ℝ) : Continuous (antider d P) := by
  unfold antider
  have := Real.continuous_mul_log.comp (continuous_level d)
  have hl := continuous_level d
  exact ((hl.mul continuous_const).sub this).add hl

private theorem hasDerivAt_antider (hd : 2 ≤ d) (P : ℝ) {x : ℝ} (hq : level d x ≠ 0) :
    HasDerivAt (antider d P) (levelDeriv d x * (Real.log P - Real.log (level d x))) x := by
  have h := hasDerivAt_level hd x
  have hlog := h.log hq
  have := ((h.mul_const (Real.log P)).sub (h.mul hlog)).add h
  convert this using 1
  · funext y
    simp only [antider, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  · field_simp
    ring

private theorem antider_le (P y : ℝ) (hP : 0 < P) (hy : 0 ≤ level d y) :
    antider d P y ≤ P := by
  unfold antider
  rcases hy.eq_or_lt with h | h
  · rw [← h]; simp [hP.le]
  · have := Real.log_le_sub_one_of_pos (div_pos hP h)
    rw [Real.log_div hP.ne' h.ne'] at this
    have h2 := mul_le_mul_of_nonneg_left this h.le
    have h3 : level d y * (P / level d y - 1) = P - level d y := by field_simp
    linarith

/-- The integral over `[0, y]` where `q ≤ P`. -/
private theorem integral_posPart_initial (hd : 2 ≤ d) {c y P : ℝ}
    (hc : c * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) (hy0 : 0 ≤ y) (hyc : y ≤ c) (hP : 0 < P)
    (hyP : level d y ≤ P) :
    ∫ x in (0 : ℝ)..y, levelDeriv d x * max 0 (Real.log P - Real.log (level d x)) ≤ P := by
  have hdd : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) - 1) := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hmono := monotoneOn_level hd hc
  have hadm : ∀ x ∈ Ioo (0 : ℝ) y, x * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1 := fun x hx =>
    le_trans (by nlinarith [hx.2]) hc
  have hqpos : ∀ x ∈ Ioo (0 : ℝ) y, 0 < level d x := fun x hx => level_pos hd hx.1 (hadm x hx)
  have hqle : ∀ x ∈ Ioc (0 : ℝ) y, level d x ≤ P := fun x hx =>
    (hmono ⟨hx.1.le, hx.2.trans hyc⟩ ⟨hy0, hyc⟩ hx.2).trans hyP
  have hcongr : ∫ x in (0 : ℝ)..y, levelDeriv d x * max 0 (Real.log P - Real.log (level d x)) =
      ∫ x in (0 : ℝ)..y, levelDeriv d x * (Real.log P - Real.log (level d x)) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [uIoc_of_le hy0] at hx
    have hq0 : 0 < level d x := level_pos hd hx.1 (le_trans (by nlinarith [hx.2]) hc)
    rw [max_eq_right (sub_nonneg.2 (Real.log_le_log hq0 (hqle x hx)))]
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) y,
      HasDerivAt (antider d P) (levelDeriv d x * (Real.log P - Real.log (level d x))) x :=
    fun x hx => hasDerivAt_antider hd P (hqpos x hx).ne'
  have hnn : ∀ x ∈ Ioo (0 : ℝ) y, 0 ≤ levelDeriv d x * (Real.log P - Real.log (level d x)) :=
    fun x hx => mul_nonneg (levelDeriv_nonneg hd hx.1.le (hadm x hx))
      (sub_nonneg.2 (Real.log_le_log (hqpos x hx) (hqle x ⟨hx.1, hx.2.le⟩)))
  have hint : IntervalIntegrable (fun x => levelDeriv d x * (Real.log P - Real.log (level d x)))
      volume 0 y := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
      (continuous_antider d P).continuousOn
    · simpa [min_eq_left hy0, max_eq_right hy0] using hderiv
    · simpa [min_eq_left hy0, max_eq_right hy0] using hnn
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hy0
    (continuous_antider d P).continuousOn hderiv hint]
  have h0 : antider d P 0 = 0 := by simp [antider, level_zero]
  rw [h0, sub_zero]
  have hyq : 0 ≤ level d y := mul_nonneg hy0 (pow_nonneg (hy0.trans (le_base hd hy0
    (le_trans (mul_le_mul_of_nonneg_right hyc hdd) hc))) _)
  exact antider_le P y hP hyq

theorem continuous_levelDeriv (d : ℕ) : Continuous (levelDeriv d) := by
  unfold levelDeriv
  fun_prop

theorem measurable_clampLevel (d : ℕ) : Measurable (fun p : ℝ × ℝ => clampLevel d p.1 p.2) := by
  unfold clampLevel
  fun_prop

/-! ### Integrability -/

/-- `log ∘ q` is interval integrable on `[0, c]`. -/
theorem intervalIntegrable_log_level (hd : 2 ≤ d) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) :
    IntervalIntegrable (fun x => Real.log (level d x)) volume 0 c := by
  have hdd : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) - 1) := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hadm : ∀ x ∈ uIcc (0 : ℝ) c, x * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1 := by
    intro x hx
    rw [uIcc_of_le hc0] at hx
    exact le_trans (mul_le_mul_of_nonneg_right hx.2 hdd) hc
  have hbpos : ∀ x ∈ uIcc (0 : ℝ) c, 0 < 1 - ((d : ℝ) - 1) * x := by
    intro x hx
    have h0 : 0 ≤ x := by rw [uIcc_of_le hc0] at hx; exact hx.1
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have := hadm x hx
    nlinarith
  have hcont : ContinuousOn (fun x => Real.log ((1 - ((d : ℝ) - 1) * x) ^ (d - 1))) (uIcc 0 c) :=
    ContinuousOn.log (by fun_prop) fun x hx => (pow_pos (hbpos x hx) _).ne'
  refine IntervalIntegrable.congr ?_
    ((intervalIntegral.intervalIntegrable_log' (a := 0) (b := c)).add hcont.intervalIntegrable)
  intro x hx
  rw [uIoc_of_le hc0] at hx
  have hb := hbpos x (by rw [uIcc_of_le hc0]; exact Ioc_subset_Icc_self hx)
  simp only [level]
  rw [Real.log_mul hx.1.ne' (pow_pos hb _).ne']

theorem intervalIntegrable_levelDeriv_mul_log_level (hd : 2 ≤ d) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) :
    IntervalIntegrable (fun x => levelDeriv d x * Real.log (level d x)) volume 0 c :=
  (intervalIntegrable_log_level hd hc0 hc).continuousOn_mul (continuous_levelDeriv d).continuousOn

/-- `x ↦ q'(x) log κ_x(v)` is interval integrable on `[0, c]`. -/
theorem intervalIntegrable_levelDeriv_mul_log_clamp (hd : 2 ≤ d) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) (v : ℝ) :
    IntervalIntegrable (fun x => levelDeriv d x * Real.log (clampLevel d x v)) volume 0 c := by
  have hdd : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) - 1) := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hlog : IntervalIntegrable (fun x => Real.log (clampLevel d x v)) volume 0 c := by
    refine (intervalIntegral.intervalIntegrable_log' (a := 0) (b := c)).norm.mono_fun' ?_ ?_
    · exact (Real.measurable_log.comp ((measurable_clampLevel d).comp
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable
    · rw [uIoc_of_le hc0]
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun x hx => ?_)
      have hx1 : x ≤ 1 := by
        have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
        nlinarith [mul_le_mul_of_nonneg_right hx.2 hdd, hx.1]
      have hcl : x ≤ clampLevel d x v := le_max_left _ _
      have hcl1 : clampLevel d x v ≤ 1 := by
        have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
        exact max_le hx1 ((min_le_right _ _).trans (by nlinarith [hx.1]))
      have h1 := Real.log_le_log hx.1 hcl
      have h2 := Real.log_nonpos (hx.1.le.trans hcl) hcl1
      have h3 := Real.log_nonpos hx.1.le hx1
      dsimp only
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos h2, abs_of_nonpos h3]
      linarith
  exact hlog.continuousOn_mul (continuous_levelDeriv d).continuousOn

/-! ### The integral of the positive part -/

/-- Interval integrability of `x ↦ q'(x) max(0, log P - log q(x))` on `[0, c]`. -/
theorem intervalIntegrable_posPart (hd : 2 ≤ d) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) (P : ℝ) :
    IntervalIntegrable (fun x => levelDeriv d x * max 0 (Real.log P - Real.log (level d x)))
      volume 0 c := by
  have hg : IntervalIntegrable (fun x => ‖levelDeriv d x‖ * (|Real.log P| +
      ‖Real.log (level d x)‖)) volume 0 c :=
    (intervalIntegrable_const.add (intervalIntegrable_log_level hd hc0 hc).norm).continuousOn_mul
      (continuous_levelDeriv d).norm.continuousOn
  refine hg.mono_fun' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((continuous_levelDeriv d).measurable.mul (measurable_const.max
      (measurable_const.sub (Real.measurable_log.comp
        (continuous_level d).measurable)))).aestronglyMeasurable
  · simp only [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _), Real.norm_eq_abs]
    have h1 := le_abs_self (Real.log P)
    have h2 := neg_abs_le (Real.log (level d x))
    exact max_le (by positivity) (by linarith)

/-- **`∫₀ᶜ q'(x) max(0, log P - log q(x)) dx ≤ P`** for `P > 0`. -/
theorem integral_levelDeriv_posPart_le (hd : 2 ≤ d) {c P : ℝ} (hc0 : 0 ≤ c)
    (hc : c * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) (hP : 0 < P) :
    ∫ x in (0 : ℝ)..c, levelDeriv d x * max 0 (Real.log P - Real.log (level d x)) ≤ P := by
  rcases le_or_gt (level d c) P with hcP | hcP
  · exact integral_posPart_initial hd hc hc0 le_rfl hP hcP
  obtain ⟨y, hy, hyP⟩ : ∃ y ∈ Icc 0 c, level d y = P := by
    have := intermediate_value_Icc hc0 (continuous_level d).continuousOn
    exact this ⟨by rw [level_zero]; exact hP.le, hcP.le⟩
  set f := fun x => levelDeriv d x * max 0 (Real.log P - Real.log (level d x)) with hf
  have hint : IntervalIntegrable f volume 0 c := intervalIntegrable_posPart hd hc0 hc P
  have hmono := monotoneOn_level hd hc
  have hzero : ∫ x in y..c, f x = 0 := by
    rw [← intervalIntegral.integral_zero (a := y) (b := c) (μ := volume)]
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [uIoc_of_le hy.2] at hx
    have hxy : P ≤ level d x := hyP ▸ hmono hy ⟨hy.1.trans hx.1.le, hx.2⟩ hx.1.le
    simp only [hf]
    rw [max_eq_left (sub_nonpos.2 (Real.log_le_log hP hxy)), mul_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint.mono_set (by
      rw [uIcc_of_le hy.1, uIcc_of_le hc0]; exact Icc_subset_Icc le_rfl hy.2))
    (hint.mono_set (by
      rw [uIcc_of_le hy.2, uIcc_of_le hc0]; exact Icc_subset_Icc hy.1 le_rfl)), hzero, add_zero]
  exact integral_posPart_initial hd hc hy.1 hy.2 hP hyP.le

/-! ### The dual function and the pointwise dual inequality -/

/-- The dual function `ψ_c(v) = ∫₀ᶜ q'(x) log κ_x(v) dx`. -/
noncomputable def dualFunction (d : ℕ) (c v : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..c, levelDeriv d x * Real.log (clampLevel d x v)

/-- The dual constant `Q_c = ∫₀ᶜ q'(x) log q(x) dx`. -/
noncomputable def dualConstant (d : ℕ) (c : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..c, levelDeriv d x * Real.log (level d x)

/-- `Q_c = q(c) log q(c) - q(c)`. -/
theorem dualConstant_eq (hd : 2 ≤ d) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) :
    dualConstant d c = level d c * Real.log (level d c) - level d c := by
  have hdd : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) - 1) := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hcont : Continuous (fun x => level d x * Real.log (level d x) - level d x) :=
    (Real.continuous_mul_log.comp (continuous_level d)).sub (continuous_level d)
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) c, HasDerivAt (fun x => level d x * Real.log (level d x) -
      level d x) (levelDeriv d x * Real.log (level d x)) x := by
    intro x hx
    have hq := level_pos hd hx.1 (le_trans (mul_le_mul_of_nonneg_right hx.2.le hdd) hc)
    have h := hasDerivAt_level hd x
    have := (h.mul (h.log hq.ne')).sub h
    convert this using 1
    field_simp
    ring
  unfold dualConstant
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hc0 hcont.continuousOn hderiv
    (intervalIntegrable_levelDeriv_mul_log_level hd hc0 hc)]
  simp [level_zero]

/-- **The pointwise dual inequality**: for `vᵢ > 0`, `∑ᵢ ψ_c(vᵢ) - Q_c ≤ ∏ᵢ vᵢ`. -/
theorem sum_dualFunction_sub_le_prod (hd : 2 ≤ d) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) {v : Fin d → ℝ} (hv0 : ∀ i, 0 < v i) :
    ∑ i, dualFunction d c (v i) - dualConstant d c ≤ ∏ i, v i := by
  have hdd : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) - 1) := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hi := fun i => intervalIntegrable_levelDeriv_mul_log_clamp hd hc0 hc (v i)
  have hq := intervalIntegrable_levelDeriv_mul_log_level hd hc0 hc
  have hP : 0 < ∏ i, v i := Finset.prod_pos fun i _ => hv0 i
  have hs : IntervalIntegrable (fun x => ∑ i, levelDeriv d x * Real.log (clampLevel d x (v i)))
      volume 0 c := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ => hi i) using 1
    ext x
    simp
  unfold dualFunction dualConstant
  rw [← intervalIntegral.integral_finsetSum fun i _ => hi i,
    ← intervalIntegral.integral_sub hs hq]
  refine le_trans ?_ (integral_levelDeriv_posPart_le hd hc0 hc hP)
  apply intervalIntegral.integral_mono_on_of_le_Ioo hc0 (hs.sub hq)
    (intervalIntegrable_posPart hd hc0 hc _)
  · intro x hx
    have hxd : x * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_right hx.2.le hdd) hc
    have h := sum_log_clampLevel_sub_le hd hx.1 hxd hv0
    have hk := levelDeriv_nonneg hd hx.1.le hxd
    have := mul_le_mul_of_nonneg_left h hk
    rw [← Finset.mul_sum, ← mul_sub]
    exact this

/-- `ψ_c` is monotone. -/
theorem monotone_dualFunction (hd : 2 ≤ d) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) : Monotone (dualFunction d c) := by
  have hdd : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) - 1) := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  intro v w hvw
  apply intervalIntegral.integral_mono_on_of_le_Ioo hc0
    (intervalIntegrable_levelDeriv_mul_log_clamp hd hc0 hc v)
    (intervalIntegrable_levelDeriv_mul_log_clamp hd hc0 hc w)
  intro x hx
  have hxd : x * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right hx.2.le hdd) hc
  apply mul_le_mul_of_nonneg_left _ (levelDeriv_nonneg hd hx.1.le hxd)
  exact Real.log_le_log (hx.1.trans_le (le_max_left _ _))
    (max_le_max le_rfl (min_le_min hvw le_rfl))

/-! ### Integrating the dual inequality against a copula -/

theorem measurable_dualFunction_symm (hd : 2 ≤ d) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) :
    Measurable (fun t : I => dualFunction d c (1 - (t : ℝ))) :=
  (monotone_dualFunction hd hc0 hc).measurable.comp (measurable_const.sub measurable_subtype_coe)

theorem integrable_dualFunction_symm (hd : 2 ≤ d) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) :
    Integrable (fun t : I => dualFunction d c (1 - (t : ℝ))) := by
  refine Integrable.of_bound (measurable_dualFunction_symm hd hc0 hc).aestronglyMeasurable
    (|dualFunction d c 0| + |dualFunction d c 1|) (Filter.Eventually.of_forall fun t => ?_)
  have hm := monotone_dualFunction hd hc0 hc
  have h0 : dualFunction d c 0 ≤ dualFunction d c (1 - (t : ℝ)) := hm (by linarith [t.2.2])
  have h1 : dualFunction d c (1 - (t : ℝ)) ≤ dualFunction d c 1 := hm (by linarith [t.2.1])
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [neg_abs_le (dualFunction d c 0), abs_nonneg (dualFunction d c 1)]
  · linarith [le_abs_self (dualFunction d c 1), abs_nonneg (dualFunction d c 0)]

/-- Integrating the pointwise dual inequality against a copula:
`d ∫₀¹ ψ_c(1 - t) dt - Q_c ≤ ∫ C dΠ`. -/
theorem integral_dualFunction_sub_le (hd : 2 ≤ d) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) (C : Copula d) :
    (d : ℝ) * (∫ t : I, dualFunction d c (1 - (t : ℝ))) - dualConstant d c ≤
      ∫ u, C.cdf u ∂(independence d).toMeasure := by
  rw [integral_cdf_independence_eq_prod]
  have hmeas := measurable_dualFunction_symm hd hc0 hc
  have hint := integrable_dualFunction_symm hd hc0 hc
  have hint_i : ∀ i, Integrable (fun y : Fin d → I => dualFunction d c (1 - (y i : ℝ)))
      C.toMeasure := fun i =>
    ((C.measurePreserving_eval i).integrable_comp hmeas.aestronglyMeasurable).2 hint
  have hsum : Integrable (fun y : Fin d → I => ∑ i, dualFunction d c (1 - (y i : ℝ)))
      C.toMeasure := integrable_finsetSum _ fun i _ => hint_i i
  have hlhs : (d : ℝ) * (∫ t : I, dualFunction d c (1 - (t : ℝ))) - dualConstant d c =
      ∫ y, (∑ i, dualFunction d c (1 - (y i : ℝ)) - dualConstant d c) ∂C.toMeasure := by
    rw [integral_sub hsum (integrable_const _), integral_finsetSum _ fun i _ => hint_i i]
    simp only [fun i => C.integral_eval i (fun t : I => dualFunction d c (1 - (t : ℝ))) hmeas,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, integral_const,
      probReal_univ, one_smul]
  rw [hlhs]
  apply integral_mono_ae (hsum.sub (integrable_const _))
    (integrable_continuous_cube _ (by fun_prop))
  have hne : ∀ᵐ y ∂C.toMeasure, ∀ i, y i ≠ 1 := ae_all_iff.2 fun i => C.ae_eval_ne i 1
  filter_upwards [hne] with y hy
  apply sum_dualFunction_sub_le_prod hd hc0 hc (v := fun i => 1 - (y i : ℝ))
  intro i
  have : (y i : ℝ) < 1 := lt_of_le_of_ne (y i).2.2 fun h => hy i (Subtype.ext h)
  linarith

/-! ### Fubini: the integral of the dual function -/

/-- `∫₀¹ log κ_x(v) dv = log(1 - (d-1)x) + d x - 1`. -/
theorem integral_log_clampLevel (hd : 2 ≤ d) {x : ℝ} (hx : 0 < x)
    (hxd : x * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) :
    ∫ v in (0 : ℝ)..1, Real.log (clampLevel d x v) =
      Real.log (1 - ((d : ℝ) - 1) * x) + d * x - 1 := by
  have hxb := le_base hd hx.le hxd
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set b := 1 - ((d : ℝ) - 1) * x with hbdef
  have hb1 : b ≤ 1 := by nlinarith
  have hcont : Continuous (fun v => Real.log (clampLevel d x v)) := by
    refine Continuous.log (by unfold clampLevel; fun_prop) fun v => ?_
    exact (hx.trans_le (le_max_left _ _)).ne'
  have hi := fun a e => hcont.intervalIntegrable (μ := volume) a e
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 x) (hi x 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hi x b) (hi b 1)]
  have e1 : ∫ v in (0 : ℝ)..x, Real.log (clampLevel d x v) = ∫ _v in (0 : ℝ)..x, Real.log x := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hx.le] at hv
    simp only [clampLevel]
    rw [max_eq_left ((min_le_left _ _).trans hv.2)]
  have e2 : ∫ v in x..b, Real.log (clampLevel d x v) = ∫ v in x..b, Real.log v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hxb] at hv
    simp only [clampLevel]
    rw [min_eq_left hv.2, max_eq_right hv.1]
  have e3 : ∫ v in b..1, Real.log (clampLevel d x v) = ∫ _v in b..1, Real.log b := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hb1] at hv
    simp only [clampLevel]
    rw [min_eq_right hv.1, max_eq_right hxb]
  rw [e1, e2, e3, intervalIntegral.integral_const, intervalIntegral.integral_const, integral_log,
    smul_eq_mul, smul_eq_mul]
  rw [hbdef]
  ring

/-- **Fubini**: `∫₀¹ ψ_c(1 - t) dt = ∫₀ᶜ q'(x) (log(1 - (d-1)x) + d x - 1) dx`. -/
theorem integral_dualFunction_symm (hd : 2 ≤ d) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) :
    ∫ t : I, dualFunction d c (1 - (t : ℝ)) =
      ∫ x in (0 : ℝ)..c, levelDeriv d x * (Real.log (1 - ((d : ℝ) - 1) * x) + d * x - 1) := by
  have hdd : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) - 1) := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  rw [integral_unitInterval (fun t => dualFunction d c (1 - t)),
    intervalIntegral.integral_comp_sub_left (fun v => dualFunction d c v) 1]
  simp only [sub_self, sub_zero]
  unfold dualFunction
  set F : ℝ → ℝ → ℝ := fun v x => levelDeriv d x * Real.log (clampLevel d x v) with hF
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le hc0]
  simp_rw [intervalIntegral.integral_of_le hc0]
  -- integrability on the product
  have hG : Integrable (fun x => ‖levelDeriv d x‖ * ‖Real.log x‖) (volume.restrict (Ioc 0 c)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hc0).1
      ((intervalIntegral.intervalIntegrable_log' (a := 0) (b := c)).norm.continuousOn_mul
        (continuous_levelDeriv d).norm.continuousOn))
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 c))) := by
    refine (hG.comp_snd _).mono' ?_ ?_
    · exact ((continuous_levelDeriv d).measurable.comp measurable_snd |>.mul
        (Real.measurable_log.comp ((measurable_clampLevel d).comp
          (measurable_snd.prodMk measurable_fst)))).aestronglyMeasurable
    · rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
      obtain ⟨-, hx⟩ := hp
      have hx1 : p.2 ≤ 1 := by
        have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
        nlinarith [mul_le_mul_of_nonneg_right hx.2 hdd, hx.1]
      have hcl : p.2 ≤ clampLevel d p.2 p.1 := le_max_left _ _
      have hcl1 : clampLevel d p.2 p.1 ≤ 1 := by
        have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
        exact max_le hx1 ((min_le_right _ _).trans (by nlinarith [hx.1]))
      have h1 := Real.log_le_log hx.1 hcl
      have h2 := Real.log_nonpos (hx.1.le.trans hcl) hcl1
      have h3 := Real.log_nonpos hx.1.le hx1
      simp only [Function.uncurry, hF, norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos h2, abs_of_nonpos h3]
      linarith
  rw [integral_integral_swap hprod]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have hxd : x * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right hx.2 hdd) hc
  simp only [hF]
  rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
    integral_log_clampLevel hd hx.1 hxd]

/-! ### The main result -/

/-- The dual lower bound
`L_d(c) = d ∫₀ᶜ q'(x) (log(1 - (d-1)x) + d x - 1) dx - q(c) log q(c) + q(c)`. -/
noncomputable def dualBound (d : ℕ) (c : ℝ) : ℝ :=
  d * (∫ x in (0 : ℝ)..c, levelDeriv d x * (Real.log (1 - ((d : ℝ) - 1) * x) + d * x - 1)) -
    (level d c * Real.log (level d c) - level d c)

/-- **The dual lower bound for `∫ C dΠ`**: for `d ≥ 2`, `0 ≤ c ≤ 1/(d(d-1))` and every
`d`-copula, `L_d(c) ≤ ∫ C dΠ`. For `c = c_d` (the Bernard–Jiang–Wang threshold) this is the exact
infimum. -/
theorem dualBound_le_integral_cdf (hd : 2 ≤ d) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) (C : Copula d) :
    dualBound d c ≤ ∫ u, C.cdf u ∂(independence d).toMeasure := by
  have h := integral_dualFunction_sub_le hd hc0 hc C
  rwa [integral_dualFunction_symm hd hc0 hc, dualConstant_eq hd hc0 hc] at h

end SpearmanInfimum

open SpearmanInfimum in
/-- **The dual lower bound for multivariate Spearman's rho**:
`ρ_d(C) ≥ (d+1)/(2^d - d - 1) · (2^d L_d(c) - 1)` for `d ≥ 2`, `0 ≤ c ≤ 1/(d(d-1))`. -/
theorem dualBound_le_multivariateSpearmanRho {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c * ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1) (C : Copula d) :
    ((d : ℝ) + 1) / ((2 : ℝ) ^ d - d - 1) * ((2 : ℝ) ^ d * dualBound d c - 1) ≤
      C.multivariateSpearmanRho := by
  have hD : 0 < (2 : ℝ) ^ d - d - 1 := by linarith [dim_add_one_lt_two_pow hd]
  rw [multivariateSpearmanRho]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) hD.le)
  have := dualBound_le_integral_cdf hd hc0 hc C
  have h2 : (0 : ℝ) ≤ 2 ^ d := by positivity
  nlinarith

end ProbabilityTheory.Copula
