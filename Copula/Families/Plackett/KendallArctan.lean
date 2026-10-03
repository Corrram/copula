/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Plackett.Kendall
import Copula.Families.Plackett.Spearman
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Kendall's tau of the Plackett family: a one-dimensional integral

Starting from the rational representation `kendallTau_plackett_eq_rational`
(`Copula.Families.Plackett.Kendall`), the inner integral is elementary: for `0 < v < 1` write
`x = (θ-1)u + 1 - (θ+1)v` (`PlackettKendall.shift`) and `s = 2√θ √(v(1-v))`
(`PlackettKendall.arcScale`); then `disc = x² + s²` and the numerator is
`1 + (θ-1)(u+v-2uv) = (1-2v) x + 2(θ+1) v(1-v)`, so the `u`-integrand has the primitive
`((1-2v)/2 · log disc + (θ+1)/√θ · √(v(1-v)) · arctan(x/s)) / (θ-1)`
(`PlackettKendall.hasDerivAt_ratPrimitive`). The boundary terms are symmetric under
`v ↦ 1 - v`, and the logarithmic part integrates in closed form. The result is
(`kendallTau_plackett_eq_arctan`, `θ ≠ 1`)

`τ(C_θ) = (θ+1)/(θ-1) - 2θ(θ² - 1 - 2θ log θ)/(θ-1)⁴ + 4(θ+1)√θ/(θ-1)² · J(θ)`,

`J(θ) = ∫₀¹ √(v(1-v)) arctan((1 - (θ+1)v) / (2√θ √(v(1-v)))) dv` (`plackettTauIntegral`),

equivalently, with Mardia's `ρ(C_θ) = (θ² - 1 - 2θ log θ)/(θ-1)²` (`spearmanRho_plackett`),

`τ(C_θ) = (θ+1)/(θ-1) - 2θ ρ(C_θ)/(θ-1)² + 4(θ+1)√θ/(θ-1)² · J(θ)`
(`kendallTau_plackett_eq_spearmanRho_arctan`).

There is no elementary closed form for `J`; the formula reduces the computation of `τ(C_θ)`
to one bounded one-dimensional integral (checked numerically, e.g. `τ(C_2) ≈ 0.15305`,
`τ(C_5) ≈ 0.34550`, `τ(C_{20}) ≈ 0.59166`).
-/

open MeasureTheory Set Filter Real
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace PlackettKendall

/-- `x(u,v) = (θ-1)u + 1 - (θ+1)v`, so that `disc(u,v) = x² + 4θv(1-v)`. -/
def shift (θ u v : ℝ) : ℝ := (θ - 1) * u + 1 - (θ + 1) * v

/-- `s(v) = 2√θ √(v(1-v))`, so that `disc(u,v) = x(u,v)² + s(v)²`. -/
noncomputable def arcScale (θ v : ℝ) : ℝ := 2 * √θ * √(v * (1 - v))

theorem plackettDisc_eq_shift (θ u v : ℝ) :
    plackettDisc θ u v = shift θ u v ^ 2 + 4 * θ * v * (1 - v) :=
  PlackettSpearman.plackettDisc_eq_sq_add θ u v

theorem arcScale_sq {θ v : ℝ} (hθ : 0 ≤ θ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    arcScale θ v ^ 2 = 4 * θ * v * (1 - v) := by
  unfold arcScale
  have h1 := Real.sq_sqrt hθ
  have h2 := Real.sq_sqrt (mul_nonneg hv0 (sub_nonneg.mpr hv1))
  linear_combination (4 * v * (1 - v)) * h1 + 4 * √θ ^ 2 * h2

theorem arcScale_pos {θ v : ℝ} (hθ : 0 < θ) (hv0 : 0 < v) (hv1 : v < 1) : 0 < arcScale θ v := by
  unfold arcScale
  have := Real.sqrt_pos.mpr hθ
  have := Real.sqrt_pos.mpr (mul_pos hv0 (sub_pos.mpr hv1))
  positivity

theorem plackettDisc_pos_of_mem {θ v : ℝ} (hθ : 0 < θ) (hv0 : 0 < v) (hv1 : v < 1) (u : ℝ) :
    0 < plackettDisc θ u v := by
  rw [plackettDisc_eq_shift]
  have := mul_pos (mul_pos hθ hv0) (sub_pos.mpr hv1)
  nlinarith [sq_nonneg (shift θ u v)]

/-- The primitive in `u` of the rational part `(1 + (θ-1)(u+v-2uv))/disc`. -/
noncomputable def ratPrimitive (θ v u : ℝ) : ℝ :=
  ((1 - 2 * v) / 2 * Real.log (plackettDisc θ u v) +
    (θ + 1) / √θ * √(v * (1 - v)) * Real.arctan (shift θ u v / arcScale θ v)) / (θ - 1)

theorem hasDerivAt_ratPrimitive {θ v : ℝ} (hθ : 0 < θ) (hθ1 : θ ≠ 1) (hv0 : 0 < v) (hv1 : v < 1)
    (u : ℝ) : HasDerivAt (ratPrimitive θ v) (plackettRatPart θ u v) u := by
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have hs := arcScale_pos hθ hv0 hv1
  have hs2 := arcScale_sq hθ.le hv0.le hv1.le
  have hD := plackettDisc_pos_of_mem hθ hv0 hv1 u
  have hx : HasDerivAt (fun y => shift θ y v) (θ - 1) u := by
    unfold shift
    simpa using (((hasDerivAt_id u).const_mul (θ - 1)).add_const 1).sub_const ((θ + 1) * v)
  have hlog := (hasDerivAt_plackettDisc_left θ u v).log hD.ne'
  have harc := (hx.div_const (arcScale θ v)).arctan
  have h : HasDerivAt (ratPrimitive θ v) (((1 - 2 * v) / 2 *
      ((2 * plackettLinear θ u v * (θ - 1) - 4 * θ * (θ - 1) * v) / plackettDisc θ u v) +
      (θ + 1) / √θ * √(v * (1 - v)) *
        (1 / (1 + (shift θ u v / arcScale θ v) ^ 2) * ((θ - 1) / arcScale θ v))) / (θ - 1)) u :=
    ((hlog.const_mul ((1 - 2 * v) / 2)).add
      (harc.const_mul ((θ + 1) / √θ * √(v * (1 - v))))).div_const (θ - 1)
  convert h using 1
  have hr : 0 < √θ := Real.sqrt_pos.mpr hθ
  have hq : 0 < √(v * (1 - v)) := Real.sqrt_pos.mpr (mul_pos hv0 (sub_pos.mpr hv1))
  have hr2 : √θ ^ 2 = θ := Real.sq_sqrt hθ.le
  have hq2 : √(v * (1 - v)) ^ 2 = v * (1 - v) := Real.sq_sqrt (mul_pos hv0 (sub_pos.mpr hv1)).le
  have hDx : plackettDisc θ u v = shift θ u v ^ 2 + arcScale θ v ^ 2 := by
    rw [plackettDisc_eq_shift, hs2]
  have hD' : 2 * plackettLinear θ u v * (θ - 1) - 4 * θ * (θ - 1) * v =
      2 * (θ - 1) * shift θ u v := by
    unfold plackettLinear shift; ring
  have hN : 1 + (θ - 1) * (u + v - 2 * u * v) =
      (1 - 2 * v) * shift θ u v + 2 * (θ + 1) * (v * (1 - v)) := by
    unfold shift; ring
  have hsc : arcScale θ v = 2 * √θ * √(v * (1 - v)) := rfl
  rw [hD', plackettRatPart, hN, hDx, hsc]
  rw [hDx, hsc] at hD
  generalize shift θ u v = x at hD ⊢
  generalize √(v * (1 - v)) = q at hq hq2 hD ⊢
  rw [← hq2]
  have hθr : θ = √θ ^ 2 := hr2.symm
  generalize √θ = r at hr hθr hD ⊢
  subst hθr
  have hD2 : x ^ 2 + (2 * r * q) ^ 2 ≠ 0 := hD.ne'
  field_simp
  ring

theorem continuous_plackettRatPart_left {θ v : ℝ} (hθ : 0 < θ) (hv0 : 0 < v) (hv1 : v < 1) :
    Continuous (fun u => plackettRatPart θ u v) := by
  unfold plackettRatPart
  refine Continuous.div (by fun_prop) ?_ fun u => (plackettDisc_pos_of_mem hθ hv0 hv1 u).ne'
  unfold plackettDisc plackettLinear; fun_prop

/-- The `u`-integral of the rational part, by the fundamental theorem of calculus. -/
theorem integral_plackettRatPart_left {θ v : ℝ} (hθ : 0 < θ) (hθ1 : θ ≠ 1) (hv0 : 0 < v)
    (hv1 : v < 1) :
    (∫ u in (0 : ℝ)..1, plackettRatPart θ u v) = ratPrimitive θ v 1 - ratPrimitive θ v 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_ratPrimitive hθ hθ1 hv0 hv1 u)
    ((continuous_plackettRatPart_left hθ hv0 hv1).intervalIntegrable 0 1)

/-- The logarithmic part `(1 - 2v) log(1 + (θ-1)v)`. -/
noncomputable def logPart (θ v : ℝ) : ℝ := (1 - 2 * v) * Real.log (1 + (θ - 1) * v)

/-- The arctangent part `√(v(1-v)) arctan((1 - (θ+1)v)/(2√θ√(v(1-v))))`. -/
noncomputable def arcPart (θ v : ℝ) : ℝ :=
  √(v * (1 - v)) * Real.arctan ((1 - (θ + 1) * v) / arcScale θ v)

/-- Half of the boundary term: `∫₀¹ ratPart(u,v) du = half(v) + half(1-v)`. -/
noncomputable def half (θ v : ℝ) : ℝ := -(logPart θ v + (θ + 1) / √θ * arcPart θ v) / (θ - 1)

theorem ratPrimitive_sub (θ v : ℝ) :
    ratPrimitive θ v 1 - ratPrimitive θ v 0 = half θ v + half θ (1 - v) := by
  have e1 : (1 - v) * (1 - (1 - v)) = v * (1 - v) := by ring
  have e2 : 1 + (θ - 1) * (1 - v) = θ - (θ - 1) * v := by ring
  have e3 : 1 - (θ + 1) * (1 - v) = -shift θ 1 v := by unfold shift; ring
  have e4 : shift θ 0 v = 1 - (θ + 1) * v := by unfold shift; ring
  have hsym : arcScale θ (1 - v) = arcScale θ v := by unfold arcScale; rw [e1]
  have hl1 : Real.log (plackettDisc θ 1 v) = 2 * Real.log (θ - (θ - 1) * v) := by
    rw [plackettDisc_one_left, Real.log_pow]; norm_num
  have hl0 : Real.log (plackettDisc θ 0 v) = 2 * Real.log (1 + (θ - 1) * v) := by
    rw [plackettDisc_zero_left, Real.log_pow]; norm_num
  simp only [ratPrimitive, half, logPart, arcPart, hl1, hl0, e1, e2, e3, e4, hsym, neg_div,
    Real.arctan_neg]
  ring

theorem measurable_arcPart (θ : ℝ) : Measurable (arcPart θ) := by
  unfold arcPart arcScale
  have := Real.continuous_arctan.measurable
  fun_prop

theorem abs_arcPart_le {θ v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : |arcPart θ v| ≤ π / 2 := by
  unfold arcPart
  have hq0 : 0 ≤ √(v * (1 - v)) := Real.sqrt_nonneg _
  have hq1 : √(v * (1 - v)) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith)
  have ha : |Real.arctan ((1 - (θ + 1) * v) / arcScale θ v)| ≤ π / 2 :=
    abs_le.mpr ⟨(neg_pi_div_two_lt_arctan _).le, (arctan_lt_pi_div_two _).le⟩
  rw [abs_mul, abs_of_nonneg hq0]
  calc √(v * (1 - v)) * |Real.arctan ((1 - (θ + 1) * v) / arcScale θ v)| ≤ 1 * (π / 2) :=
        mul_le_mul hq1 ha (abs_nonneg _) zero_le_one
    _ = π / 2 := one_mul _

theorem integrable_arcPart (θ : ℝ) : Integrable (fun v : I => arcPart θ v) :=
  (integrable_const (π / 2)).mono' ((measurable_arcPart θ).comp measurable_subtype_coe
    ).aestronglyMeasurable (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs]; exact abs_arcPart_le v.2.1 v.2.2)

theorem one_add_mul_pos {θ v : ℝ} (hθ : 0 < θ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < 1 + (θ - 1) * v := by
  rcases le_total 1 θ with h | h
  · nlinarith [mul_nonneg (sub_nonneg.mpr h) hv0]
  · nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hv1)]

theorem continuousOn_logPart {θ : ℝ} (hθ : 0 < θ) : ContinuousOn (logPart θ) (Icc 0 1) := by
  unfold logPart
  refine ContinuousOn.mul (by fun_prop) (ContinuousOn.log (by fun_prop) fun v hv => ?_)
  exact (one_add_mul_pos hθ hv.1 hv.2).ne'

theorem integrable_logPart {θ : ℝ} (hθ : 0 < θ) : Integrable (fun v : I => logPart θ v) := by
  have hc : Continuous (fun v : I => logPart θ v) :=
    (continuousOn_logPart hθ).comp_continuous continuous_subtype_val fun v => v.2
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- A primitive of the logarithmic part. -/
noncomputable def logPrimitive (θ v : ℝ) : ℝ :=
  v ^ 2 / 2 - v * (v - 1) * Real.log (1 + (θ - 1) * v) - v * θ / (θ - 1) +
    θ * Real.log (1 + (θ - 1) * v) / (θ - 1) ^ 2

theorem hasDerivAt_logPrimitive {θ v : ℝ} (hθ1 : θ ≠ 1) (hv : 0 < 1 + (θ - 1) * v) :
    HasDerivAt (logPrimitive θ) (logPart θ v) v := by
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have hl : HasDerivAt (fun y => 1 + (θ - 1) * y) (θ - 1) v := by
    simpa using ((hasDerivAt_id v).const_mul (θ - 1)).const_add 1
  have hlog := hl.log hv.ne'
  have hp : HasDerivAt (fun y => y * (y - 1)) (1 * (v - 1) + v * 1) v :=
    (hasDerivAt_id v).mul ((hasDerivAt_id v).sub_const 1)
  have h : HasDerivAt (logPrimitive θ) (↑2 * v ^ (2 - 1) / 2 -
      ((1 * (v - 1) + v * 1) * Real.log (1 + (θ - 1) * v) +
        v * (v - 1) * ((θ - 1) / (1 + (θ - 1) * v))) - 1 * θ / (θ - 1) +
      θ * ((θ - 1) / (1 + (θ - 1) * v)) / (θ - 1) ^ 2) v :=
    ((((hasDerivAt_pow 2 v).div_const 2).sub (hp.mul hlog)).sub
      (((hasDerivAt_id v).mul_const θ).div_const (θ - 1))).add
      ((hlog.const_mul θ).div_const ((θ - 1) ^ 2))
  convert h using 1
  unfold logPart
  have hw : 1 + (θ - 1) * v ≠ 0 := hv.ne'
  generalize Real.log (1 + (θ - 1) * v) = L
  generalize hW : 1 + (θ - 1) * v = w at hw ⊢
  have hv' : v = (w - 1) / (θ - 1) := by
    field_simp
    linarith
  subst hv'
  have h1' : -1 + θ ≠ 0 := by rwa [neg_add_eq_sub]
  field_simp
  ring_nf
  field_simp
  ring

theorem integral_logPart {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≠ 1) :
    (∫ v : I, logPart θ v) = 1 / 2 - θ / (θ - 1) + θ * Real.log θ / (θ - 1) ^ 2 := by
  rw [integral_unitInterval (logPart θ),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := logPrimitive θ)
      (fun v hv => by
        rw [uIcc_of_le zero_le_one] at hv
        exact hasDerivAt_logPrimitive hθ1 (one_add_mul_pos hθ hv.1 hv.2))
      ((continuousOn_logPart hθ).intervalIntegrable_of_Icc zero_le_one)]
  unfold logPrimitive
  have e : 1 + (θ - 1) * 1 = θ := by ring
  simp only [e, mul_zero, add_zero, Real.log_one]
  ring

theorem integrable_half {θ : ℝ} (hθ : 0 < θ) : Integrable (fun v : I => half θ v) := by
  unfold half
  exact (((integrable_logPart hθ).add ((integrable_arcPart θ).const_mul _)).neg).div_const _

private theorem ae_coe_mem_Ioo' : ∀ᵐ v : I, (v : ℝ) ∈ Ioo (0 : ℝ) 1 := by
  have h : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ Ioo (0 : ℝ) 1 := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := 1)).mem_iff]
      with x hx
    exact hx.2
  exact unitInterval.measurePreserving_coe.quasiMeasurePreserving.ae h

/-- The double integral of the rational part as twice the integral of `half`. -/
theorem integral_plackettRatPart {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≠ 1) :
    (∫ v : I, ∫ u : I, plackettRatPart θ u v) = 2 * ∫ v : I, half θ v := by
  have hin : (fun v : I => ∫ u : I, plackettRatPart θ u v) =ᵐ[volume]
      fun v : I => half θ v + half θ (unitInterval.symm v) := by
    filter_upwards [ae_coe_mem_Ioo'] with v hv
    rw [integral_unitInterval (fun u => plackettRatPart θ u v),
      integral_plackettRatPart_left hθ hθ1 hv.1 hv.2, ratPrimitive_sub θ v,
      unitInterval.coe_symm_eq]
  have hrefl : (∫ v : I, half θ (unitInterval.symm v)) = ∫ v : I, half θ v :=
    unitInterval.measurePreserving_symm.integral_comp
      unitInterval.symmMeasurableEquiv.measurableEmbedding (fun v : I => half θ v)
  have hint2 : Integrable (fun v : I => half θ (unitInterval.symm v)) :=
    (unitInterval.measurePreserving_symm.integrable_comp_emb
      unitInterval.symmMeasurableEquiv.measurableEmbedding).2 (integrable_half hθ)
  rw [integral_congr_ae hin, integral_add (integrable_half hθ) hint2, hrefl]
  ring

end PlackettKendall

/-- The arctangent integral
`J(θ) = ∫₀¹ √(v(1-v)) arctan((1 - (θ+1)v)/(2√θ √(v(1-v)))) dv` appearing in Kendall's tau of
the Plackett copula. -/
noncomputable def plackettTauIntegral (θ : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, √(v * (1 - v)) *
    Real.arctan ((1 - (θ + 1) * v) / (2 * √θ * √(v * (1 - v))))

/-- **Kendall's tau of the Plackett copula as a one-dimensional integral** (`θ ≠ 1`):
`τ(C_θ) = (θ+1)/(θ-1) - 2θ(θ² - 1 - 2θ log θ)/(θ-1)⁴ + 4(θ+1)√θ/(θ-1)² · J(θ)`. -/
theorem kendallTau_plackett_eq_arctan {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≠ 1) :
    (plackett θ hθ).kendallTau = (θ + 1) / (θ - 1) -
      2 * θ * (θ ^ 2 - 1 - 2 * θ * Real.log θ) / (θ - 1) ^ 4 +
      4 * (θ + 1) * √θ / (θ - 1) ^ 2 * plackettTauIntegral θ := by
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have hr : 0 < √θ := Real.sqrt_pos.mpr hθ
  have hr2 : √θ ^ 2 = θ := Real.sq_sqrt hθ.le
  have hJ : plackettTauIntegral θ = ∫ v : I, PlackettKendall.arcPart θ v := by
    rw [integral_unitInterval]; rfl
  have hhalf : (∫ v : I, PlackettKendall.half θ v) =
      -((∫ v : I, PlackettKendall.logPart θ v) +
        (θ + 1) / √θ * ∫ v : I, PlackettKendall.arcPart θ v) / (θ - 1) := by
    unfold PlackettKendall.half
    rw [integral_div, integral_neg, integral_add (PlackettKendall.integrable_logPart hθ)
      ((PlackettKendall.integrable_arcPart θ).const_mul _), integral_const_mul]
  have hrat := kendallTau_plackett_eq_rational hθ hθ1
  have hR : (∫ v : I, ∫ u : I, (1 + (θ - 1) * (u + v - 2 * u * v)) / plackettDisc θ u v) =
      ∫ v : I, ∫ u : I, plackettRatPart θ u v := rfl
  rw [hrat, hR, PlackettKendall.integral_plackettRatPart hθ hθ1, hhalf,
    PlackettKendall.integral_logPart hθ hθ1, hJ]
  generalize (∫ v : I, PlackettKendall.arcPart θ v) = J
  have hθr : θ = √θ ^ 2 := hr2.symm
  generalize hL : Real.log θ = L
  generalize √θ = r at hr hθr ⊢
  subst hθr
  field_simp
  ring

/-- Kendall's tau of the Plackett copula in terms of Spearman's rho and `J(θ)` (`θ ≠ 1`):
`τ(C_θ) = (θ+1)/(θ-1) - 2θ ρ(C_θ)/(θ-1)² + 4(θ+1)√θ/(θ-1)² · J(θ)`. -/
theorem kendallTau_plackett_eq_spearmanRho_arctan {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≠ 1) :
    (plackett θ hθ).kendallTau = (θ + 1) / (θ - 1) -
      2 * θ * (plackett θ hθ).spearmanRho / (θ - 1) ^ 2 +
      4 * (θ + 1) * √θ / (θ - 1) ^ 2 * plackettTauIntegral θ := by
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  rw [kendallTau_plackett_eq_arctan hθ hθ1, spearmanRho_plackett hθ hθ1]
  field_simp
  ring

end ProbabilityTheory.Copula
