/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Plackett.Basic
import Copula.Rank.KendallConditionalProduct
import Copula.Rank.ConditionalDerivative

/-! # Kendall's tau of the Plackett family: integral representations

Kendall's tau of the Plackett copula `C_θ` (`Copula.Families.Plackett.Basic`; Nelsen 2006, §3.3.1)
has no elementary closed form. This file proves two explicit integral representations.

* The conditional distribution functions of `C_θ` are the explicit partial derivatives:
  `∂C_θ/∂u (u, v) = plackettDeriv θ v u` for almost every `u` (`conditionalCDF_plackett`), and
  by `kendallTau_conditional_product` and exchangeability (`kendallTau_plackett_eq_integral`)

  `τ(C_θ) = 1 - 4 ∫₀¹∫₀¹ ∂_u C_θ(u,v) ∂_v C_θ(u,v) du dv`,

  with `∂_v C_θ(u,v) = (1 - (1 + (θ-1)(u+v) - 2θu)/√disc(u,v))/2` (`plackettDeriv`).
* A rational representation (`kendallTau_plackett_eq_rational`, `θ ≠ 1`): writing
  `disc(u,v) = [1 + (θ-1)(u+v)]² - 4θ(θ-1)uv` (`plackettDisc`),

  `τ(C_θ) = (θ+1)/(θ-1) - 2θ/(θ-1) ∫₀¹∫₀¹ (1 + (θ-1)(u+v-2uv)) / disc(u,v) du dv`.

  It follows from the pointwise identity (`four_mul_plackettDeriv_mul`)
  `4 ∂_uC ∂_vC = -2/(θ-1) - 2(1-u-v)/√disc + 2θ(1 + (θ-1)(u+v-2uv))/((θ-1) disc)` and the
  vanishing of `∫∫ (1-u-v)/√disc` under the radial reflection `(u,v) ↦ (1-u,1-v)`, which
  leaves `disc` invariant (`integral_plackettOddPart`).

A one-dimensional arctangent-integral form is in `Copula.Families.Plackett.KendallArctan`; strict
monotonicity, sign and limits of `τ(C_θ)` are in `Copula.Families.Plackett.KendallOrder`.
-/

open MeasureTheory Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

/-! ## Partial derivatives for all parameters -/

/-- For `θ = 1` the derivative formula reduces to `∂(uv)/∂v = u`. -/
theorem plackettDeriv_one (u v : ℝ) : plackettDeriv 1 u v = u := by
  simp only [plackettDeriv, plackettDisc, plackettLinear]
  norm_num

/-- `∂C_θ/∂v (u,v) = plackettDeriv θ u v` on the closed unit square, for every `θ > 0`
(including `θ = 1`). -/
theorem hasDerivAt_plackettCDF_right_of_mem {θ u v : ℝ} (hθ : 0 < θ) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    HasDerivAt (fun y => plackettCDF θ u y) (plackettDeriv θ u v) v := by
  by_cases h : θ = 1
  · subst h
    rw [plackettDeriv_one]
    have hfun : (fun y => plackettCDF 1 u y) = fun y => u * y := by
      funext y; simp [plackettCDF]
    rw [hfun]
    simpa using (hasDerivAt_id v).const_mul u
  · exact hasDerivAt_plackettCDF_right h (plackettDisc_pos hθ hu0 hu1 hv0 hv1)

theorem measurable_plackettDeriv (θ : ℝ) :
    Measurable (fun q : I × I => plackettDeriv θ (q.1 : ℝ) (q.2 : ℝ)) := by
  simp only [plackettDeriv, plackettDisc, plackettLinear]
  fun_prop

theorem continuous_plackettDeriv {θ : ℝ} (hθ : 0 < θ) :
    Continuous (fun q : I × I => plackettDeriv θ (q.1 : ℝ) (q.2 : ℝ)) := by
  unfold plackettDeriv
  refine Continuous.div_const (continuous_const.sub (Continuous.div ?_ ?_ fun q => ?_)) 2
  · unfold plackettLinear; fun_prop
  · unfold plackettDisc plackettLinear; fun_prop
  · exact (Real.sqrt_pos.mpr (plackettDisc_pos hθ q.1.2.1 q.1.2.2 q.2.2.1 q.2.2.2)).ne'

private theorem ae_coe_mem_Ioo_unit : ∀ᵐ v : I, (v : ℝ) ∈ Ioo (0 : ℝ) 1 := by
  have h : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ Ioo (0 : ℝ) 1 := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := 1)).mem_iff]
      with x hx
    exact hx.2
  exact unitInterval.measurePreserving_coe.quasiMeasurePreserving.ae h

/-- The conditional distribution function of the Plackett copula is the explicit partial
derivative `∂C_θ/∂u (u, v) = plackettDeriv θ v u`, for almost every `u`. -/
theorem conditionalCDF_plackett {θ : ℝ} (hθ : 0 < θ) (v : I) :
    ∀ᵐ u : I, (plackett θ hθ).conditionalCDF u v = plackettDeriv θ v u := by
  filter_upwards [conditionalCDF_eq_deriv (plackett θ hθ) v, ae_coe_mem_Ioo_unit] with u hu hI
  rw [hu]
  apply HasDerivAt.deriv
  have he : cdfSection (plackett θ hθ) v =ᶠ[𝓝 (u : ℝ)] fun y => plackettCDF θ v y := by
    filter_upwards [Ioo_mem_nhds hI.1 hI.2] with y hy
    rw [cdfSection, cdf_plackett_two, projIcc_of_mem zero_le_one ⟨hy.1.le, hy.2.le⟩,
      plackettCDF_comm]
  exact (hasDerivAt_plackettCDF_right_of_mem hθ v.2.1 v.2.2 hI.1.le hI.2.le).congr_of_eventuallyEq
    he

/-! ## The partial-derivative representation -/

/-- **Kendall's tau of the Plackett copula** as a double integral of the product of the
explicit partial derivatives: `τ(C_θ) = 1 - 4 ∫∫ ∂_uC_θ ∂_vC_θ`. -/
theorem kendallTau_plackett_eq_integral {θ : ℝ} (hθ : 0 < θ) :
    (plackett θ hθ).kendallTau =
      1 - 4 * ∫ v : I, ∫ u : I, plackettDeriv θ v u * plackettDeriv θ u v := by
  set C := plackett θ hθ with hC
  have hCt : C.transpose = C := isExchangeable_plackett θ hθ
  have hA : ∀ v : I, ∀ᵐ u : I, C.conditionalCDF u v = plackettDeriv θ v u :=
    conditionalCDF_plackett hθ
  have hf : ∀ᵐ v : I, ∀ᵐ u : I, C.conditionalCDF u v = plackettDeriv θ v u :=
    Filter.Eventually.of_forall hA
  have hr : ∀ᵐ v : I, ∀ᵐ u : I, C.conditionalCDF v u = plackettDeriv θ u v := by
    have hm : MeasurableSet {q : I × I |
        C.conditionalCDF q.2 q.1 = plackettDeriv θ (q.1 : ℝ) (q.2 : ℝ)} :=
      measurableSet_eq_fun C.measurable_conditionalCDF (measurable_plackettDeriv θ)
    exact (Measure.ae_ae_comm (μ := (volume : Measure I)) (ν := (volume : Measure I))
      (p := fun u v => C.conditionalCDF v u = plackettDeriv θ u v) hm).mp
        (Filter.Eventually.of_forall hA)
  have hi : Integrable (fun q : I × I =>
      C.conditionalCDF q.1 q.2 * C.conditionalCDF q.2 q.1) := by
    simpa only [hCt] using crossConditional_integrable C
  change C.kendallTau = _
  rw [kendallTau_conditional_product, hCt, integral_integral_swap hi]
  congr 2
  apply integral_congr_ae
  filter_upwards [hf, hr] with v hv hv'
  apply integral_congr_ae
  filter_upwards [hv, hv'] with u hu hu'
  rw [hu, hu']

/-! ## The rational representation -/

theorem plackettDisc_reflect (θ u v : ℝ) :
    plackettDisc θ (1 - u) (1 - v) = plackettDisc θ u v := by
  rw [plackettDisc_eq, plackettDisc_eq]; ring

/-- The odd part `(1 - u - v)/√disc` of the integrand. -/
noncomputable def plackettOddPart (θ u v : ℝ) : ℝ := (1 - u - v) / √(plackettDisc θ u v)

/-- The rational part `(1 + (θ-1)(u+v-2uv))/disc` of the integrand (the Plackett density
times `√disc / θ`). -/
noncomputable def plackettRatPart (θ u v : ℝ) : ℝ :=
  (1 + (θ - 1) * (u + v - 2 * u * v)) / plackettDisc θ u v

/-- The pointwise decomposition `4 ∂_uC ∂_vC = -2/(θ-1) - 2(1-u-v)/√disc +
2θ(1 + (θ-1)(u+v-2uv))/((θ-1) disc)`. -/
theorem four_mul_plackettDeriv_mul {θ u v : ℝ} (hθ : θ ≠ 1) (hD : 0 < plackettDisc θ u v) :
    4 * (plackettDeriv θ v u * plackettDeriv θ u v) =
      -2 / (θ - 1) - 2 * plackettOddPart θ u v + 2 * θ / (θ - 1) * plackettRatPart θ u v := by
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ
  unfold plackettDeriv plackettOddPart plackettRatPart
  rw [plackettLinear_comm θ v u, plackettDisc_comm θ v u]
  have hr : 0 < √(plackettDisc θ u v) := Real.sqrt_pos.mpr hD
  have hr2 : √(plackettDisc θ u v) ^ 2 = plackettDisc θ u v := Real.sq_sqrt hD.le
  have hdef : plackettDisc θ u v = plackettLinear θ u v ^ 2 - 4 * θ * (θ - 1) * u * v := rfl
  have hL : plackettLinear θ u v = 1 + (θ - 1) * (u + v) := rfl
  generalize √(plackettDisc θ u v) = r at hr hr2 ⊢
  rw [← hr2] at hdef ⊢
  rw [hL] at hdef ⊢
  field_simp
  linear_combination (4 * θ + 4) * hdef

theorem continuous_plackettOddPart {θ : ℝ} (hθ : 0 < θ) :
    Continuous (fun q : I × I => plackettOddPart θ (q.1 : ℝ) (q.2 : ℝ)) := by
  unfold plackettOddPart
  refine Continuous.div (by fun_prop) ?_ fun q => ?_
  · unfold plackettDisc plackettLinear; fun_prop
  · exact (Real.sqrt_pos.mpr (plackettDisc_pos hθ q.1.2.1 q.1.2.2 q.2.2.1 q.2.2.2)).ne'

theorem continuous_plackettRatPart {θ : ℝ} (hθ : 0 < θ) :
    Continuous (fun q : I × I => plackettRatPart θ (q.1 : ℝ) (q.2 : ℝ)) := by
  unfold plackettRatPart
  refine Continuous.div (by fun_prop) ?_ fun q => ?_
  · unfold plackettDisc plackettLinear; fun_prop
  · exact (plackettDisc_pos hθ q.1.2.1 q.1.2.2 q.2.2.1 q.2.2.2).ne'

private theorem integrable_of_continuous_prod {f : I × I → ℝ} (hf : Continuous f) :
    Integrable f ((volume : Measure I).prod volume) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem integrable_section {f : I × I → ℝ} (hf : Continuous f) (v : I) :
    Integrable (fun u : I => f (u, v)) :=
  (hf.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem integrable_outer {f : I × I → ℝ} (hf : Continuous f) :
    Integrable (fun v : I => ∫ u : I, f (u, v)) := by
  have h := (integrable_of_continuous_prod (f := fun q : I × I => f (q.2, q.1))
    (hf.comp continuous_swap)).integral_prod_left
  simpa using h

/-- The odd part integrates to zero: the radial reflection `(u,v) ↦ (1-u,1-v)` preserves the
uniform measure and `disc`, and changes the sign of `1 - u - v`. -/
theorem integral_plackettOddPart (θ : ℝ) :
    (∫ v : I, ∫ u : I, plackettOddPart θ u v) = 0 := by
  have hrefl (f : I → ℝ) : (∫ u : I, f (unitInterval.symm u)) = ∫ u : I, f u :=
    unitInterval.measurePreserving_symm.integral_comp
      unitInterval.symmMeasurableEquiv.measurableEmbedding f
  have hodd (u v : I) : plackettOddPart θ (unitInterval.symm u) (unitInterval.symm v) =
      -plackettOddPart θ u v := by
    simp only [plackettOddPart, unitInterval.coe_symm_eq, plackettDisc_reflect]
    ring
  have h : (∫ v : I, ∫ u : I, plackettOddPart θ u v) =
      -∫ v : I, ∫ u : I, plackettOddPart θ u v := by
    calc (∫ v : I, ∫ u : I, plackettOddPart θ u v)
        = ∫ v : I, ∫ u : I, plackettOddPart θ (unitInterval.symm u) (unitInterval.symm v) := by
          rw [← hrefl (fun v : I => ∫ u : I, plackettOddPart θ u v)]
          congr 1; funext v
          exact (hrefl (fun u : I => plackettOddPart θ u (unitInterval.symm v))).symm
      _ = -∫ v : I, ∫ u : I, plackettOddPart θ u v := by
          simp_rw [hodd, integral_neg]
  linarith

/-- **Rational integral representation of Kendall's tau of the Plackett copula** (`θ ≠ 1`):
`τ(C_θ) = (θ+1)/(θ-1) - 2θ/(θ-1) ∫₀¹∫₀¹ (1 + (θ-1)(u+v-2uv))/disc(u,v) du dv`. -/
theorem kendallTau_plackett_eq_rational {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≠ 1) :
    (plackett θ hθ).kendallTau = (θ + 1) / (θ - 1) - 2 * θ / (θ - 1) *
      ∫ v : I, ∫ u : I, (1 + (θ - 1) * (u + v - 2 * u * v)) / plackettDisc θ u v := by
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have hO := continuous_plackettOddPart hθ
  have hR := continuous_plackettRatPart hθ
  have hpt (v u : I) : plackettDeriv θ v u * plackettDeriv θ u v =
      -1 / (2 * (θ - 1)) + (-(1 / 2) * plackettOddPart θ u v +
        θ / (2 * (θ - 1)) * plackettRatPart θ u v) := by
    have := four_mul_plackettDeriv_mul (u := u) (v := v) hθ1
      (plackettDisc_pos hθ u.2.1 u.2.2 v.2.1 v.2.2)
    have e : plackettDeriv θ v u * plackettDeriv θ u v =
        (4 * (plackettDeriv θ v u * plackettDeriv θ u v)) / 4 := by ring
    rw [e, this]
    field_simp
    ring
  have hinner (v : I) : (∫ u : I, plackettDeriv θ v u * plackettDeriv θ u v) =
      -1 / (2 * (θ - 1)) + (-(1 / 2) * (∫ u : I, plackettOddPart θ u v) +
        θ / (2 * (θ - 1)) * ∫ u : I, plackettRatPart θ u v) := by
    simp_rw [hpt v]
    rw [integral_add (integrable_const _), integral_const, integral_add, integral_const_mul,
      integral_const_mul]
    · simp
    · exact (integrable_section hO v).const_mul _
    · exact (integrable_section hR v).const_mul _
    · exact ((integrable_section hO v).const_mul _).add ((integrable_section hR v).const_mul _)
  rw [kendallTau_plackett_eq_integral hθ]
  simp_rw [hinner]
  rw [integral_add (integrable_const _), integral_const, integral_add, integral_const_mul,
    integral_const_mul, integral_plackettOddPart]
  · simp only [plackettRatPart, probReal_univ, smul_eq_mul, one_mul]
    field_simp
    ring
  · exact (integrable_outer hO).const_mul _
  · exact (integrable_outer hR).const_mul _
  · exact ((integrable_outer hO).const_mul _).add ((integrable_outer hR).const_mul _)

end ProbabilityTheory.Copula
