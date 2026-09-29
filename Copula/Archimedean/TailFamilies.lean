/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.TailDependence
import Copula.Families.Frank
import Copula.Families.NelsenTable.N9
import Copula.Families.NelsenTable.N19
import Copula.Families.NelsenTable.N20

/-! # Tail coefficients of Archimedean families via their generators

Applications of Nelsen, *An Introduction to Copulas*, second edition, Corollary 5.4.3
(`Copula.Archimedean.TailDependence`) to families of Table 4.1 without previously recorded
tail coefficients (cf. Nelsen, Section 5.4):

| Family | `λ_L` | `λ_U` |
| --- | --- | --- |
| Frank (4.2.5), `θ > 0` | 0 | 0 |
| Gumbel–Barnett (4.2.9), `0 < θ ≤ 1` | 0 | 0 |
| 4.2.19, `θ > 0` | 1 | 0 |
| 4.2.20, `θ > 0` | 1 | 0 |

In each case `ψ` has a finite nonzero derivative at `0`, so `λ_U = 0`. For the lower tail the
limit `ψ(2x)/ψ(x)` as `x → ∞` is computed: it is `0` for Frank and Gumbel–Barnett (their
inverse generators decay exponentially) and `1` for families 19 and 20 (logarithmic decay).
-/

open Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

/-- `log (x + c) / log (2x + c) → 1` as `x → ∞`, for `c > 1`. -/
theorem tendsto_log_add_div_log_two_mul_add {c : ℝ} (hc : 1 < c) :
    Tendsto (fun x => Real.log (x + c) / Real.log (2 * x + c)) atTop (𝓝 1) := by
  have hc0 : 0 < c := by linarith
  have hlogc : 0 < Real.log c := Real.log_pos hc
  have hL : Tendsto (fun x => Real.log (x + c)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ c tendsto_id)
  have hlow : Tendsto (fun x => 1 - Real.log 2 / (Real.log (x + c) + Real.log 2)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := Real.log 2)).div_atTop
      (tendsto_atTop_add_const_right _ (Real.log 2) hL)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have h1 : 0 < Real.log (x + c) := Real.log_pos (by linarith)
    have h2 : Real.log (2 * x + c) ≤ Real.log (x + c) + Real.log 2 := by
      rw [← Real.log_mul (by linarith) (by norm_num)]
      exact Real.log_le_log (by linarith) (by nlinarith)
    have h3 : 0 < Real.log (2 * x + c) := Real.log_pos (by linarith)
    have hpos : 0 < Real.log (x + c) + Real.log 2 := by positivity
    rw [one_sub_div hpos.ne', add_sub_cancel_right, div_le_div_iff₀ hpos h3]
    nlinarith
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have h3 : 0 < Real.log (2 * x + c) := Real.log_pos (by linarith)
    rw [div_le_one h3]
    exact Real.log_le_log (by linarith) (by linarith)

/-! ### Frank -/

private theorem frankP (θ : ℝ) (hθ : 0 < θ) :
    0 < 1 - Real.exp (-θ) ∧ 1 - Real.exp (-θ) < 1 := by
  constructor
  · have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hθ); linarith
  · linarith [Real.exp_pos (-θ)]

section Frank

variable (θ : ℝ) (hθ : 0 < θ)

theorem frankGenerator_isStrict : (frankGenerator θ hθ).IsStrict := by
  intro s hs
  have hp := frankP θ hθ
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)
  have hep := Real.exp_pos (-s)
  have hb0 : 0 < 1 - (1 - Real.exp (-θ)) * Real.exp (-s) := by nlinarith
  have hb1 : 1 - (1 - Real.exp (-θ)) * Real.exp (-s) < 1 := by nlinarith
  change 0 < -Real.log (1 - (1 - Real.exp (-θ)) * Real.exp (-s)) / θ
  exact div_pos (neg_pos.mpr (Real.log_neg hb0 hb1)) hθ

/-- Frank copulas have no upper tail dependence. -/
theorem hasUpperTailDependence_frank : (frank θ hθ).HasUpperTailDependence 0 := by
  have hp := frankP θ hθ
  set p := 1 - Real.exp (-θ) with hpdef
  have hb : 1 - p * Real.exp (-0) ≠ 0 := by
    rw [neg_zero, Real.exp_zero, mul_one]; linarith
  have hd := (((((hasDerivAt_id' (0 : ℝ)).neg.exp).const_mul p).const_sub 1).log hb).neg.div_const θ
  refine (frankGenerator θ hθ).hasUpperTailDependence_zero_of_hasDerivWithinAt
    hd.hasDerivWithinAt ?_
  simp only [mul_one, mul_neg]
  have h1p : 1 - p ≠ 0 := by linarith
  exact div_ne_zero (neg_ne_zero.mpr (div_ne_zero (by simpa using hp.1.ne')
    (by simpa [neg_mul, sub_neg_eq_add] using h1p))) hθ.ne'

/-- Frank copulas with `θ > 0` have no lower tail dependence. -/
theorem hasLowerTailDependence_frank : (frank θ hθ).HasLowerTailDependence 0 := by
  have hp := frankP θ hθ
  set p := 1 - Real.exp (-θ) with hpdef
  apply BivariateGenerator.hasLowerTailDependence_of_tendsto (frankGenerator_isStrict θ hθ)
  have hup : Tendsto (fun x : ℝ => Real.exp (-x) / (1 - p)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.div_const (1 - p)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact div_nonneg ((frankGenerator θ hθ).nonneg _ (by linarith))
      ((frankGenerator θ hθ).nonneg _ hx)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    change (-Real.log (1 - p * Real.exp (-(2 * x))) / θ) /
      (-Real.log (1 - p * Real.exp (-x)) / θ) ≤ Real.exp (-x) / (1 - p)
    rw [div_div_div_cancel_right₀ hθ.ne']
    set y₁ := p * Real.exp (-x) with hy₁
    set y₂ := p * Real.exp (-(2 * x)) with hy₂
    have hex := Real.exp_pos (-x)
    have hex1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hy21 : y₂ = y₁ * Real.exp (-x) := by
      rw [hy₂, hy₁, mul_assoc, ← Real.exp_add]; ring_nf
    have hy1pos : 0 < y₁ := mul_pos hp.1 hex
    have hy1le : y₁ ≤ p := by rw [hy₁]; nlinarith
    have hy2pos : 0 < y₂ := by rw [hy21]; positivity
    have hy2le : y₂ ≤ p := by rw [hy21]; nlinarith
    have h1y1 : 0 < 1 - y₁ := by linarith
    have h1y2 : 0 < 1 - y₂ := by linarith
    -- `y ≤ -log (1 - y) ≤ y / (1 - y)`.
    have hB : y₁ ≤ -Real.log (1 - y₁) := by
      have := Real.log_le_sub_one_of_pos h1y1; linarith
    have hA : -Real.log (1 - y₂) ≤ y₂ / (1 - y₂) := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h1y2)
      rw [Real.log_inv] at h
      have he : (1 - y₂)⁻¹ - 1 = y₂ / (1 - y₂) := by field_simp; ring
      linarith
    have hA' : y₂ / (1 - y₂) ≤ y₂ / (1 - p) :=
      div_le_div_of_nonneg_left hy2pos.le (by linarith) (by linarith)
    have hBpos : 0 < -Real.log (1 - y₁) := hy1pos.trans_le hB
    rw [div_le_div_iff₀ hBpos (by linarith)]
    calc -Real.log (1 - y₂) * (1 - p) ≤ y₂ / (1 - p) * (1 - p) :=
          mul_le_mul_of_nonneg_right (hA.trans hA') (by linarith)
      _ = y₁ * Real.exp (-x) := by rw [div_mul_cancel₀ _ (by linarith), hy21]
      _ ≤ Real.exp (-x) * -Real.log (1 - y₁) := by nlinarith

end Frank

/-! ### Gumbel–Barnett (family 9) -/

section Nelsen9

variable (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1)

theorem nelsen9Generator_isStrict : (nelsen9Generator θ hθ h1).IsStrict :=
  fun _ _ => Real.exp_pos _

/-- Gumbel–Barnett copulas have no upper tail dependence. -/
theorem hasUpperTailDependence_nelsen9 : (nelsen9 θ hθ h1).HasUpperTailDependence 0 := by
  have hd := (((hasDerivAt_id' (0 : ℝ)).exp.const_sub 1).div_const θ).exp
  refine (nelsen9Generator θ hθ h1).hasUpperTailDependence_zero_of_hasDerivWithinAt
    hd.hasDerivWithinAt ?_
  simp only [Real.exp_zero, sub_self, zero_div, mul_one, one_mul]
  exact div_ne_zero (neg_ne_zero.mpr one_ne_zero) hθ.ne'

/-- Gumbel–Barnett copulas have no lower tail dependence. -/
theorem hasLowerTailDependence_nelsen9 : (nelsen9 θ hθ h1).HasLowerTailDependence 0 := by
  apply BivariateGenerator.hasLowerTailDependence_of_tendsto (nelsen9Generator_isStrict θ hθ h1)
  have hbot : Tendsto (fun x : ℝ => (1 - Real.exp x) / θ) atTop atBot :=
    (tendsto_atBot_add_const_left _ 1 (tendsto_neg_atTop_atBot.comp Real.tendsto_exp_atTop)).atBot_div_const hθ
  have hbot' : Tendsto (fun x : ℝ => (Real.exp x - Real.exp (2 * x)) / θ) atTop atBot := by
    refine tendsto_atBot_mono' _ ?_ hbot
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    apply div_le_div_of_nonneg_right _ hθ.le
    have he1 : 1 ≤ Real.exp x := Real.one_le_exp hx
    have h2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by rw [← Real.exp_add]; ring_nf
    rw [h2]
    nlinarith
  refine (Real.tendsto_exp_atBot.comp hbot').congr' ?_
  filter_upwards with x
  change Real.exp ((Real.exp x - Real.exp (2 * x)) / θ) =
    Real.exp ((1 - Real.exp (2 * x)) / θ) / Real.exp ((1 - Real.exp x) / θ)
  rw [← Real.exp_sub]
  congr 1
  ring

end Nelsen9

/-! ### Family 19 -/

section Nelsen19

variable (θ : ℝ) (hθ : 0 < θ)

theorem nelsen19Generator_isStrict : (nelsen19Generator θ hθ).IsStrict := by
  intro s hs
  have hc : 1 < Real.exp θ := (by have := Real.add_one_lt_exp hθ.ne'; linarith)
  exact div_pos hθ (Real.log_pos (by linarith))

/-- Nelsen's family 19 has lower tail dependence one. -/
theorem hasLowerTailDependence_nelsen19 : (nelsen19 θ hθ).HasLowerTailDependence 1 := by
  apply BivariateGenerator.hasLowerTailDependence_of_tendsto (nelsen19Generator_isStrict θ hθ)
  have hc : 1 < Real.exp θ := (by have := Real.add_one_lt_exp hθ.ne'; linarith)
  refine (tendsto_log_add_div_log_two_mul_add hc).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have h1 : 0 < Real.log (x + Real.exp θ) := Real.log_pos (by linarith)
  have h2 : 0 < Real.log (2 * x + Real.exp θ) := Real.log_pos (by linarith)
  change _ = (θ / Real.log (2 * x + Real.exp θ)) / (θ / Real.log (x + Real.exp θ))
  field_simp

/-- Nelsen's family 19 has no upper tail dependence. -/
theorem hasUpperTailDependence_nelsen19 : (nelsen19 θ hθ).HasUpperTailDependence 0 := by
  have hc : 0 < Real.exp θ := Real.exp_pos θ
  have hne : (0 : ℝ) + Real.exp θ ≠ 0 := by rw [zero_add]; exact hc.ne'
  have hl : Real.log (0 + Real.exp θ) ≠ 0 := by rw [zero_add, Real.log_exp]; exact hθ.ne'
  have hd := (hasDerivAt_const (0 : ℝ) θ).div (((hasDerivAt_id' (0 : ℝ)).add_const _).log hne) hl
  refine (nelsen19Generator θ hθ).hasUpperTailDependence_zero_of_hasDerivWithinAt
    hd.hasDerivWithinAt ?_
  simp only [zero_add, Real.log_exp, zero_mul, zero_sub, one_div]
  exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hθ.ne' (inv_ne_zero hc.ne')))
    (pow_ne_zero 2 hθ.ne')

end Nelsen19

/-! ### Family 20 -/

section Nelsen20

variable (θ : ℝ) (hθ : 0 < θ)

theorem nelsen20Generator_isStrict : (nelsen20Generator θ hθ).IsStrict := by
  intro s hs
  have hc : 1 < Real.exp 1 := (by have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith)
  exact Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _

/-- Nelsen's family 20 has lower tail dependence one. -/
theorem hasLowerTailDependence_nelsen20 : (nelsen20 θ hθ).HasLowerTailDependence 1 := by
  apply BivariateGenerator.hasLowerTailDependence_of_tendsto (nelsen20Generator_isStrict θ hθ)
  have hc : 1 < Real.exp 1 := (by have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith)
  have hr := ((tendsto_log_add_div_log_two_mul_add hc).inv₀ one_ne_zero).rpow_const
    (p := -θ⁻¹) (Or.inl (by norm_num))
  rw [inv_one, Real.one_rpow] at hr
  refine hr.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have h1 : 0 < Real.log (x + Real.exp 1) := Real.log_pos (by linarith)
  have h2 : 0 < Real.log (2 * x + Real.exp 1) := Real.log_pos (by linarith)
  change _ = Real.log (2 * x + Real.exp 1) ^ (-θ⁻¹) / Real.log (x + Real.exp 1) ^ (-θ⁻¹)
  rw [← Real.div_rpow h2.le h1.le, inv_div]

/-- Nelsen's family 20 has no upper tail dependence. -/
theorem hasUpperTailDependence_nelsen20 : (nelsen20 θ hθ).HasUpperTailDependence 0 := by
  have hc : 0 < Real.exp 1 := Real.exp_pos 1
  have hne : (0 : ℝ) + Real.exp 1 ≠ 0 := by rw [zero_add]; exact hc.ne'
  have hl : Real.log (0 + Real.exp 1) ≠ 0 := by rw [zero_add, Real.log_exp]; exact one_ne_zero
  have hd := (((hasDerivAt_id' (0 : ℝ)).add_const _).log hne).rpow_const (p := -θ⁻¹) (Or.inl hl)
  refine (nelsen20Generator θ hθ).hasUpperTailDependence_zero_of_hasDerivWithinAt
    hd.hasDerivWithinAt ?_
  simp only [zero_add, Real.log_exp, Real.one_rpow, mul_one, one_div]
  exact mul_ne_zero (inv_ne_zero hc.ne') (neg_ne_zero.mpr (inv_ne_zero hθ.ne'))

end Nelsen20

end ProbabilityTheory.Copula
