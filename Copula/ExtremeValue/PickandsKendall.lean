/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.ExtremeValue.PickandsSpearman
import Copula.Rank.KendallConditionalProduct
import Copula.Rank.ConditionalDerivative
import Mathlib.Analysis.Convex.Deriv

/-! # Kendall's tau of extreme-value copulas

For a Pickands dependence function `A` which is differentiable on `(0,1)`,

`τ(C_A) = 1 - ∫₀¹ (A(t) - t A'(t)) (A(t) + (1-t) A'(t)) / A(t)² dt`
(`kendallTau_pickandsCopula`),

and if moreover `A` is twice differentiable on `(0,1)` with integrable `A''`, integration by parts
gives the classical formula

`τ(C_A) = ∫₀¹ t (1-t) A''(t) / A(t) dt`   (`kendallTau_pickandsCopula_of_deriv2`),

i.e. `τ = ∫₀¹ t(1-t)/A(t) dA'(t)`.

Proof. By `kendallTau_conditional_product`, `τ = 1 - 4 ∬ ∂₁C ∂₂C`. For `C_A` the partial
derivatives are `∂₁C(u,v) = C(u,v) u⁻¹ (A(r) - r A'(r))` and
`∂₂C(u,v) = C(u,v) v⁻¹ (A(r) + (1-r) A'(r))` with `r = log v / log(uv)`; the conditional
distribution functions agree with them almost everywhere (`conditionalCDF_eq_deriv`, and the
transpose `C_A^T = C_{A(1-·)}`). The double integral is then computed with the same substitution
`u = v^{1/t - 1}` and Gamma integral as Spearman's rho (`Copula.ExtremeValue.PickandsSpearman`).

References: G. Gudendorf and J. Segers, *Extreme-value copulas* (2010); C. Genest and
L.-P. Rivest, *A characterization of Gumbel's family of extreme value distributions* (1989);
H. Joe, *Dependence Modeling with Copulas* (2014).
-/

open MeasureTheory Set Filter
open scoped unitInterval ENNReal Topology

namespace ProbabilityTheory.Copula

/-- The transpose of `C_A` is the Pickands copula of `t ↦ A(1 - t)`. -/
theorem transpose_pickandsCopula {A : ℝ → ℝ} (hA : IsPickandsFunction A) :
    (pickandsCopula A hA).transpose = pickandsCopula (fun t => A (1 - t)) hA.comp_one_sub := by
  apply ext_cdf_two
  intro u v
  rw [cdf_transpose, cdf_pickandsCopula_two, cdf_pickandsCopula_two, pickandsCDF, pickandsCDF,
    pickandsTail_swap A]
  simp only [or_comm]

namespace PickandsKendall

open PickandsSpearman

variable {A : ℝ → ℝ}

/-- The ratio `log y / log (x y)`, the Pickands coordinate of `(x,y)`. -/
noncomputable def ratio (x y : ℝ) : ℝ := Real.log y / Real.log (x * y)

theorem ratio_mem {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    ratio x y ∈ Ioo (0 : ℝ) 1 := by
  have hlx := Real.log_neg hx.1 hx.2
  have hly := Real.log_neg hy.1 hy.2
  rw [ratio, Real.log_mul hx.1.ne' hy.1.ne']
  exact ⟨div_pos_of_neg_of_neg hly (by linarith), (div_lt_one_of_neg (by linarith)).2
    (by linarith)⟩

/-- The partial derivative `∂₁ C_A(x,y) = C_A(x,y) x⁻¹ (A(r) - r A'(r))` on `(0,1)²`, and `0`
elsewhere. -/
noncomputable def d1 (A : ℝ → ℝ) (x y : ℝ) : ℝ :=
  if x ∈ Ioo (0 : ℝ) 1 ∧ y ∈ Ioo (0 : ℝ) 1 then
    kernel A x y * (x⁻¹ * (extend A (ratio x y) - ratio x y * deriv A (ratio x y)))
  else 0

theorem measurable_d1 (hA : IsPickandsFunction A) :
    Measurable (fun p : ℝ × ℝ => d1 A p.1 p.2) := by
  have he := measurable_extend hA
  have hd := measurable_deriv A
  unfold d1 kernel ratio
  refine Measurable.ite (measurableSet_Ioo.prod measurableSet_Ioo) ?_ measurable_const
  fun_prop

/-- Tangent-line bounds for a differentiable Pickands function: `0 ≤ A - tA' ≤ 1` and
`0 ≤ A + (1-t)A' ≤ 1`. -/
theorem deriv_bounds (hA : IsPickandsFunction A) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hd : DifferentiableAt ℝ A t) :
    0 ≤ A t - t * deriv A t ∧ A t - t * deriv A t ≤ 1 ∧
      0 ≤ A t + (1 - t) * deriv A t ∧ A t + (1 - t) * deriv A t ≤ 1 := by
  obtain ⟨ht0, ht1⟩ := ht
  have hmem : t ∈ Icc (0 : ℝ) 1 := ⟨ht0.le, ht1.le⟩
  have h1 := hA.convexOn.deriv_le_slope hmem (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
    ht1 hd
  have h0 := hA.convexOn.slope_le_deriv (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) 1) hmem
    ht0 hd
  rw [slope_def_field, hA.apply_one] at h1
  rw [slope_def_field, hA.apply_zero, sub_zero] at h0
  rw [le_div_iff₀ (by linarith)] at h1
  rw [div_le_iff₀ ht0] at h0
  have hmax := hA.max_le t hmem
  have hm1 := le_max_left t (1 - t)
  have hm2 := le_max_right t (1 - t)
  have hpos := hA.pos hmem
  refine ⟨?_, by nlinarith, ?_, by nlinarith⟩
  · by_cases hD : deriv A t ≤ 0
    · nlinarith
    · push Not at hD
      nlinarith
  · by_cases hD : 0 ≤ deriv A t
    · nlinarith
    · push Not at hD
      nlinarith

theorem d1_nonneg (hA : IsPickandsFunction A) (hdiff : DifferentiableOn ℝ A (Ioo 0 1))
    (x y : ℝ) : 0 ≤ d1 A x y := by
  unfold d1
  split_ifs with h
  · have hr := ratio_mem h.1 h.2
    have hb := (deriv_bounds hA hr (hdiff.differentiableAt (Ioo_mem_nhds hr.1 hr.2))).1
    rw [extend_eq hr]
    have : 0 < x⁻¹ := inv_pos.2 h.1.1
    have : 0 < kernel A x y := Real.exp_pos _
    positivity
  · exact le_rfl

/-- The derivative of the Pickands CDF in its first variable. -/
theorem hasDerivAt_kernel {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1)
    (hd : DifferentiableAt ℝ A (ratio u v)) :
    HasDerivAt (fun x => kernel A x v)
      (kernel A u v * (u⁻¹ * (extend A (ratio u v) - ratio u v * deriv A (ratio u v)))) u := by
  have hr := ratio_mem hu hv
  have hL0 := Real.log_neg hv.1 hv.2
  have hlu := Real.log_neg hu.1 hu.2
  have hg : HasDerivAt (fun x => Real.log x + Real.log v) u⁻¹ u :=
    (Real.hasDerivAt_log hu.1.ne').add_const (Real.log v)
  have hgne : Real.log u + Real.log v ≠ 0 := by linarith
  have hrd : HasDerivAt (fun x => Real.log v * (Real.log x + Real.log v)⁻¹)
      (Real.log v * (-u⁻¹ / (Real.log u + Real.log v) ^ 2)) u :=
    (hg.inv hgne).const_mul (Real.log v)
  have hr0 : Real.log v * (Real.log u + Real.log v)⁻¹ = ratio u v := by
    rw [ratio, Real.log_mul hu.1.ne' hv.1.ne', div_eq_mul_inv]
  have hext : HasDerivAt (extend A) (deriv A (ratio u v))
      (Real.log v * (Real.log u + Real.log v)⁻¹) := by
    rw [hr0]
    refine hd.hasDerivAt.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
    exact extend_eq hs
  have hcomp : HasDerivAt (fun x => extend A (Real.log v * (Real.log x + Real.log v)⁻¹))
      (deriv A (ratio u v) * (Real.log v * (-u⁻¹ / (Real.log u + Real.log v) ^ 2))) u :=
    hext.comp u hrd
  have hprod : HasDerivAt
      (fun x => (Real.log x + Real.log v) * extend A (Real.log v * (Real.log x + Real.log v)⁻¹))
      (u⁻¹ * extend A (Real.log v * (Real.log u + Real.log v)⁻¹) + (Real.log u + Real.log v) *
        (deriv A (ratio u v) * (Real.log v * (-u⁻¹ / (Real.log u + Real.log v) ^ 2)))) u :=
    hg.mul hcomp
  have hprod' : HasDerivAt
      (fun x => (Real.log x + Real.log v) * extend A (Real.log v * (Real.log x + Real.log v)⁻¹))
      (u⁻¹ * (extend A (ratio u v) - ratio u v * deriv A (ratio u v))) u := by
    refine hprod.congr_deriv ?_
    rw [hr0]
    generalize extend A (ratio u v) = X
    generalize deriv A (ratio u v) = D
    rw [← hr0]
    have hu0 : u ≠ 0 := hu.1.ne'
    field_simp
    ring
  have hkernel : Real.exp ((Real.log u + Real.log v) *
      extend A (Real.log v * (Real.log u + Real.log v)⁻¹)) = kernel A u v := by
    rw [kernel, Real.log_mul hu.1.ne' hv.1.ne', div_eq_mul_inv]
  refine (hprod'.exp.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Ioi_mem_nhds hu.1] with x hx
    simp only [kernel]
    rw [Real.log_mul (ne_of_gt hx) hv.1.ne', div_eq_mul_inv]
  · rw [hkernel]

/-- The CDF section of `C_A` has derivative `∂₁ C_A` at interior points. -/
theorem deriv_cdfSection (hA : IsPickandsFunction A) (hdiff : DifferentiableOn ℝ A (Ioo 0 1))
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) {v : I} (hv : (v : ℝ) ∈ Ioo (0 : ℝ) 1) :
    deriv ((pickandsCopula A hA).cdfSection v) u = d1 A u v := by
  have hr := ratio_mem hu hv
  have hk := hasDerivAt_kernel hu hv (hdiff.differentiableAt (Ioo_mem_nhds hr.1 hr.2))
  have heq : (pickandsCopula A hA).cdfSection v =ᶠ[𝓝 u] fun x => kernel A x v := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
    have h := cdf_eq_kernel hA hx hv
    rw [projIcc_val] at h
    exact h
  rw [heq.deriv_eq, hk.deriv, d1, ite_eq_left ⟨hu, hv⟩]

theorem ae_coe_mem_Ioo : ∀ᵐ v : I, (v : ℝ) ∈ Ioo (0 : ℝ) 1 := by
  have h : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ Ioo (0 : ℝ) 1 := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := 1)).mem_iff]
      with x hx
    exact hx.2
  exact unitInterval.measurePreserving_coe.quasiMeasurePreserving.ae h

/-- For each interior `w`, the conditional CDF of `C_A` is `∂₁ C_A(·, w)` almost everywhere. -/
theorem ae_conditionalCDF_eq (hA : IsPickandsFunction A) (hdiff : DifferentiableOn ℝ A (Ioo 0 1))
    {w : I} (hw : (w : ℝ) ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ u : I, (pickandsCopula A hA).conditionalCDF u w = d1 A u w := by
  filter_upwards [conditionalCDF_eq_deriv (pickandsCopula A hA) w, ae_coe_mem_Ioo] with u h1 h2
  rw [h1, deriv_cdfSection hA hdiff h2 hw]

theorem differentiableOn_comp_one_sub (hdiff : DifferentiableOn ℝ A (Ioo 0 1)) :
    DifferentiableOn ℝ (fun t => A (1 - t)) (Ioo 0 1) := by
  intro t ht
  have h1 : 1 - t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  exact ((hdiff.differentiableAt (Ioo_mem_nhds h1.1 h1.2)).comp t
    ((differentiableAt_const 1).sub differentiableAt_id)).differentiableWithinAt

/-- The integrand of Kendall's formula agrees a.e. with `∂₁C ∂₂C`. -/
theorem ae_cross_eq (hA : IsPickandsFunction A) (hdiff : DifferentiableOn ℝ A (Ioo 0 1)) :
    ∀ᵐ p ∂(volume : Measure (I × I)),
      (pickandsCopula A hA).conditionalCDF p.1 p.2 *
          (pickandsCopula A hA).transpose.conditionalCDF p.2 p.1 =
        d1 A p.1 p.2 * d1 (fun t => A (1 - t)) p.2 p.1 := by
  set C := pickandsCopula A hA
  set B := fun t => A (1 - t)
  have hB := hA.comp_one_sub
  have hdB := differentiableOn_comp_one_sub hdiff
  have hmc : Measurable fun p : I × I => C.conditionalCDF p.1 p.2 :=
    C.measurable_conditionalCDF.comp measurable_swap
  have hco : Measurable fun p : I × I => ((p.1 : ℝ), (p.2 : ℝ)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)
  have hco' : Measurable fun p : I × I => ((p.2 : ℝ), (p.1 : ℝ)) :=
    (measurable_subtype_coe.comp measurable_snd).prodMk (measurable_subtype_coe.comp measurable_fst)
  have hmd : Measurable fun p : I × I => d1 A p.1 p.2 :=
    (measurable_d1 hA).comp hco
  have hmct : Measurable fun p : I × I => C.transpose.conditionalCDF p.2 p.1 :=
    C.transpose.measurable_conditionalCDF
  have hmdt : Measurable fun p : I × I => d1 B p.2 p.1 :=
    (measurable_d1 hB).comp hco'
  have h1 : ∀ᵐ p ∂(volume : Measure (I × I)), C.conditionalCDF p.1 p.2 = d1 A p.1 p.2 := by
    rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hmc hmd),
      Measure.ae_ae_comm (p := fun u v : I => C.conditionalCDF u v = d1 A u v)
        (measurableSet_eq_fun hmc hmd)]
    filter_upwards [ae_coe_mem_Ioo] with v hv
    exact ae_conditionalCDF_eq hA hdiff hv
  have h2 : ∀ᵐ p ∂(volume : Measure (I × I)),
      C.transpose.conditionalCDF p.2 p.1 = d1 B p.2 p.1 := by
    rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hmct hmdt)]
    filter_upwards [ae_coe_mem_Ioo] with u hu
    have h := ae_conditionalCDF_eq hB hdB hu
    simp only [C, transpose_pickandsCopula hA]
    exact h
  filter_upwards [h1, h2] with p hp1 hp2
  rw [hp1, hp2]

theorem substMap_mem {y t : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    substMap y t ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨substMap_pos y t, ?_⟩
  have hL0 := Real.log_neg hy.1 hy.2
  have : 1 < t⁻¹ := (one_lt_inv₀ ht.1).2 ht.2
  have hneg : Real.log y * (t⁻¹ - 1) < 0 := mul_neg_of_neg_of_pos hL0 (by linarith)
  simpa [substMap] using Real.exp_lt_exp.2 hneg

theorem ratio_substMap_swap {y t : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ratio y (substMap y t) = 1 - t := by
  have hLne : Real.log y ≠ 0 := (Real.log_neg hy.1 hy.2).ne
  have ht0 : t ≠ 0 := ht.1.ne'
  rw [ratio, mul_comm, log_substMap_mul hy, substMap, Real.log_exp]
  field_simp

/-- The product `∂₁C_A(x,y) ∂₂C_A(x,y)`, written with the first partial derivative of the
transposed copula. -/
noncomputable def cross (A : ℝ → ℝ) (x y : ℝ) : ℝ := d1 A x y * d1 (fun t => A (1 - t)) y x

/-- The numerator `(A - tA')(A + (1-t)A')`. -/
noncomputable def pq (A : ℝ → ℝ) (t : ℝ) : ℝ :=
  (extend A t - t * deriv A t) * (extend A t + (1 - t) * deriv A t)

/-- The integrand of the Kendall computation after the substitution `x = y^{1/t - 1}`. -/
noncomputable def kernelK (A : ℝ → ℝ) (t y : ℝ) : ℝ :=
  -Real.log y * ((t⁻¹) ^ 2 * Real.exp (Real.log y * (2 * extend A t * t⁻¹ - 1))) * pq A t

theorem measurable_pq (hA : IsPickandsFunction A) : Measurable (pq A) := by
  have he := measurable_extend hA
  have hd := measurable_deriv A
  unfold pq
  fun_prop

theorem measurable_kernelK (hA : IsPickandsFunction A) :
    Measurable (fun p : ℝ × ℝ => kernelK A p.2 p.1) := by
  have he := measurable_extend hA
  have hp := measurable_pq hA
  unfold kernelK
  fun_prop

theorem pq_bounds (hA : IsPickandsFunction A) (hdiff : DifferentiableOn ℝ A (Ioo 0 1)) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : 0 ≤ pq A t ∧ pq A t ≤ 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := deriv_bounds hA ht (hdiff.differentiableAt (Ioo_mem_nhds ht.1 ht.2))
  rw [pq, extend_eq ht]
  exact ⟨mul_nonneg h1 h3, by nlinarith⟩

theorem substJac_mul_cross {y t : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    substJac y t * cross A (substMap y t) y = kernelK A t y := by
  have hm := substMap_mem hy ht
  have h1t : 1 - t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hext1 : extend (fun s => A (1 - s)) (1 - t) = extend A t := by
    rw [extend_eq h1t, extend_eq ht, sub_sub_cancel]
  have hder : deriv (fun s => A (1 - s)) (1 - t) = -deriv A t := by
    rw [deriv_comp_const_sub, sub_sub_cancel]
  have hyinv : y⁻¹ = Real.exp (-Real.log y) := by rw [Real.exp_neg, Real.exp_log hy.1]
  have hmm : substMap y t * (substMap y t)⁻¹ = 1 := mul_inv_cancel₀ (substMap_pos y t).ne'
  rw [cross, d1, ite_eq_left ⟨hm, hy⟩, d1, ite_eq_left ⟨hy, hm⟩, ratio_substMap_swap hy ht,
    show ratio (substMap y t) y = t from ratio_substMap hy t, kernel, kernel,
    show Real.log y / Real.log (substMap y t * y) = t from ratio_substMap hy t,
    show Real.log (substMap y t) / Real.log (y * substMap y t) = 1 - t from
      ratio_substMap_swap hy ht, mul_comm y (substMap y t), log_substMap_mul hy, hext1, hder,
    kernelK, pq, substJac, hyinv]
  have hexp : Real.exp (Real.log y * t⁻¹ * extend A t) * Real.exp (Real.log y * t⁻¹ * extend A t)
      * Real.exp (-Real.log y) = Real.exp (Real.log y * (2 * extend A t * t⁻¹ - 1)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  rw [← hexp]
  linear_combination (-Real.log y * (t⁻¹) ^ 2 * Real.exp (Real.log y * t⁻¹ * extend A t) *
    Real.exp (Real.log y * t⁻¹ * extend A t) * Real.exp (-Real.log y) *
    (extend A t - t * deriv A t) * (extend A t + (1 - t) * deriv A t)) * hmm

/-- The double integral `∬ ∂₁C_A ∂₂C_A = ∫₀¹ (A - tA')(A + (1-t)A') / (4A²) dt`. -/
theorem integral_cross (hA : IsPickandsFunction A) (hdiff : DifferentiableOn ℝ A (Ioo 0 1)) :
    ∫ p : I × I, cross A p.1 p.2 = ∫ t in Ioo (0 : ℝ) 1, pq A t / (4 * extend A t ^ 2) := by
  have hB := hA.comp_one_sub
  have hdB := differentiableOn_comp_one_sub hdiff
  have hnn : ∀ x y, 0 ≤ cross A x y := fun x y =>
    mul_nonneg (d1_nonneg hA hdiff x y) (d1_nonneg hB hdB y x)
  have hmc : Measurable fun p : ℝ × ℝ => cross A p.1 p.2 :=
    (measurable_d1 hA).mul ((measurable_d1 hB).comp measurable_swap)
  have hco : Measurable fun p : I × I => ((p.1 : ℝ), (p.2 : ℝ)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)
  have hmI : Measurable fun p : I × I => cross A p.1 p.2 := hmc.comp hco
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun p => hnn _ _) hmI.aestronglyMeasurable,
    Measure.volume_eq_prod, lintegral_prod_symm (fun p : I × I => ENNReal.ofReal (cross A p.1 p.2))
      (ENNReal.measurable_ofReal.comp hmI).aemeasurable]
  have hinner : ∀ v : I, ∫⁻ u : I, ENNReal.ofReal (cross A u v) =
      ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (cross A x v) :=
    fun v => lintegral_unitInterval_Ioo (fun x => ENNReal.ofReal (cross A x v))
  simp only [hinner]
  rw [lintegral_unitInterval_Ioo (fun y => ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (cross A x y))]
  have h1 : ∫⁻ y in Ioo (0 : ℝ) 1, ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (cross A x y) =
      ∫⁻ y in Ioo (0 : ℝ) 1, ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (kernelK A t y) := by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro y hy
    simp only
    rw [lintegral_subst hy]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    simp only
    rw [← ENNReal.ofReal_mul (substJac_nonneg hy t), substJac_mul_cross hy ht]
  have hm : Measurable (Function.uncurry fun y t => ENNReal.ofReal (kernelK A t y)) :=
    ENNReal.measurable_ofReal.comp (measurable_kernelK hA)
  rw [h1, lintegral_lintegral_swap hm.aemeasurable]
  have h2 : ∀ t ∈ Ioo (0 : ℝ) 1, ∫⁻ y in Ioo (0 : ℝ) 1, ENNReal.ofReal (kernelK A t y) =
      ENNReal.ofReal (pq A t / (4 * extend A t ^ 2)) := by
    intro t ht
    have hE := extend_pos hA t
    have hpq := (pq_bounds hA hdiff ht).1
    have hb0 : 0 < 2 * extend A t * t⁻¹ := by
      have := inv_pos.2 ht.1
      positivity
    have hpt : ∀ y, ENNReal.ofReal (kernelK A t y) = ENNReal.ofReal ((t⁻¹) ^ 2 * pq A t) *
        ENNReal.ofReal (-Real.log y * Real.exp (Real.log y * (2 * extend A t * t⁻¹ - 1))) := by
      intro y
      rw [← ENNReal.ofReal_mul (by positivity), kernelK]
      ring_nf
    simp only [hpt]
    rw [lintegral_const_mul _ (by fun_prop), lintegral_gamma hb0, ← ENNReal.ofReal_mul
      (by positivity)]
    congr 1
    have ht0 : t ≠ 0 := ht.1.ne'
    field_simp
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioo h2]
  have hbound : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ pq A t / (4 * extend A t ^ 2) ∧
      pq A t / (4 * extend A t ^ 2) ≤ 1 := by
    intro t ht
    have hE := extend_pos hA t
    have hE2 : 1 / 2 ≤ extend A t := by
      rw [extend_eq ht]
      exact hA.half_le (Ioo_subset_Icc_self ht)
    obtain ⟨hp0, hp1⟩ := pq_bounds hA hdiff ht
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    nlinarith
  have hint : IntegrableOn (fun t => pq A t / (4 * extend A t ^ 2)) (Ioo (0 : ℝ) 1) := by
    refine Measure.integrableOn_of_bounded (M := 1) measure_Ioo_lt_top.ne ?_ ?_
    · exact ((measurable_pq hA).div (((measurable_extend hA).pow_const 2).const_mul 4))
        |>.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hbound t ht).1]
      exact (hbound t ht).2
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun t ht => (hbound t ht).1)),
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioo fun t ht => (hbound t ht).1)]

end PickandsKendall

open PickandsSpearman PickandsKendall in
/-- **Kendall's tau of a Pickands copula** with `A` differentiable on `(0,1)`:
`τ(C_A) = 1 - ∫₀¹ (A(t) - t A'(t)) (A(t) + (1-t) A'(t)) / A(t)² dt`. -/
theorem kendallTau_pickandsCopula {A : ℝ → ℝ} (hA : IsPickandsFunction A)
    (hdiff : DifferentiableOn ℝ A (Ioo 0 1)) :
    (pickandsCopula A hA).kendallTau =
      1 - ∫ t in (0 : ℝ)..1, (A t - t * deriv A t) * (A t + (1 - t) * deriv A t) / A t ^ 2 := by
  set C := pickandsCopula A hA
  have hprod : (∫ u : I, ∫ v : I, C.conditionalCDF u v * C.transpose.conditionalCDF v u) =
      ∫ p : I × I, C.conditionalCDF p.1 p.2 * C.transpose.conditionalCDF p.2 p.1 :=
    (integral_prod _ (crossConditional_integrable C)).symm
  rw [kendallTau_conditional_product, hprod, integral_congr_ae (ae_cross_eq hA hdiff)]
  change 1 - 4 * ∫ p : I × I, cross A p.1 p.2 = _
  rw [integral_cross hA hdiff, ← integral_const_mul, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have hE : 0 < A t := hA.pos (Ioo_subset_Icc_self ht)
  simp only [pq, extend_eq ht]
  field_simp

/-- A Pickands function is continuous on `[0,1]`. -/
theorem IsPickandsFunction.continuousOn {A : ℝ → ℝ} (hA : IsPickandsFunction A) :
    ContinuousOn A (Icc 0 1) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    have hlow : Tendsto (fun s : ℝ => 1 - s) (𝓝[Icc 0 1] 0) (𝓝 1) := by
      have h : Tendsto (fun s : ℝ => 1 - s) (𝓝 0) (𝓝 (1 - 0)) :=
        (continuous_const.sub continuous_id).tendsto 0
      rw [sub_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h := tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
      (eventually_nhdsWithin_of_forall fun s hs => (le_max_right s (1 - s)).trans (hA.max_le s hs))
      (eventually_nhdsWithin_of_forall fun s hs => hA.le_one s hs)
    rw [ContinuousWithinAt, hA.apply_zero]
    exact h
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · subst h1
    have hlow : Tendsto (fun s : ℝ => s) (𝓝[Icc 0 1] 1) (𝓝 1) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h := tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
      (eventually_nhdsWithin_of_forall fun s hs => (le_max_left s (1 - s)).trans (hA.max_le s hs))
      (eventually_nhdsWithin_of_forall fun s hs => hA.le_one s hs)
    rw [ContinuousWithinAt, hA.apply_one]
    exact h
  · have hc := hA.convexOn.continuousOn_interior t (by rw [interior_Icc]; exact ⟨h0, h1⟩)
    rw [interior_Icc] at hc
    exact (hc.continuousAt (Ioo_mem_nhds h0 h1)).continuousWithinAt

open PickandsKendall in
/-- **Kendall's tau of a Pickands copula** (twice differentiable `A`):
`τ(C_A) = ∫₀¹ t (1-t) A''(t) / A(t) dt`, i.e. `τ = ∫₀¹ t(1-t)/A(t) dA'(t)`. -/
theorem kendallTau_pickandsCopula_of_deriv2 {A A'' : ℝ → ℝ} (hA : IsPickandsFunction A)
    (hdiff : DifferentiableOn ℝ A (Ioo 0 1))
    (h2 : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (deriv A) (A'' t) t)
    (hint : IntervalIntegrable A'' volume 0 1) :
    (pickandsCopula A hA).kendallTau = ∫ t in (0 : ℝ)..1, t * (1 - t) * A'' t / A t := by
  have hApos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < A t := fun t ht => hA.pos ht
  -- the bounded part `G1` and the second-derivative part `G2`
  set G1 : ℝ → ℝ := fun t =>
    ((1 - 2 * t) * deriv A t * A t - t * (1 - t) * deriv A t * deriv A t) / A t ^ 2 with hG1
  set G2 : ℝ → ℝ := fun t => t * (1 - t) * A'' t / A t with hG2
  set F : ℝ → ℝ := fun t => t * (1 - t) * deriv A t / A t with hF
  have hDb : ∀ t ∈ Ioo (0 : ℝ) 1, |deriv A t| ≤ 1 := by
    intro t ht
    obtain ⟨h1, h2', h3, h4⟩ := deriv_bounds hA ht (hdiff.differentiableAt (Ioo_mem_nhds ht.1 ht.2))
    have hmax := hA.max_le t (Ioo_subset_Icc_self ht)
    have hm1 := le_max_left t (1 - t)
    have hm2 := le_max_right t (1 - t)
    rw [abs_le]
    obtain ⟨ht0, ht1⟩ := ht
    constructor <;> nlinarith
  -- `F' = G1 + G2` on `(0,1)`
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt F (G1 t + G2 t) t := by
    intro t ht
    have hA' : HasDerivAt A (deriv A t) t :=
      (hdiff.differentiableAt (Ioo_mem_nhds ht.1 ht.2)).hasDerivAt
    have hp : HasDerivAt (fun s : ℝ => s * (1 - s)) (1 * (1 - t) + t * (0 - 1)) t :=
      (hasDerivAt_id t).mul ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
    have hq : HasDerivAt (fun s => s * (1 - s) * deriv A s / A s)
        ((((1 * (1 - t) + t * (0 - 1)) * deriv A t + t * (1 - t) * A'' t) * A t -
          t * (1 - t) * deriv A t * deriv A t) / A t ^ 2) t :=
      (hp.mul (h2 t ht)).div hA' (hApos t (Ioo_subset_Icc_self ht)).ne'
    refine hq.congr_deriv ?_
    have hAt := (hApos t (Ioo_subset_Icc_self ht)).ne'
    simp only [hG1, hG2]
    field_simp
    ring
  -- continuity of `F` on `[0,1]`
  have hFbound : ∀ t ∈ Icc (0 : ℝ) 1, |F t| ≤ 2 * (t * (1 - t)) := by
    intro t ht
    have hpos := hApos t ht
    have hhalf := hA.half_le ht
    have htt : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (by linarith [ht.2])
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · simp [hF, ← h0]
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · simp [hF, h1]
    have hd := hDb t ⟨h0, h1⟩
    simp only [hF]
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos, abs_mul, abs_of_nonneg htt]
    calc t * (1 - t) * |deriv A t| ≤ t * (1 - t) * 1 := mul_le_mul_of_nonneg_left hd htt
      _ ≤ 2 * (t * (1 - t)) * A t := by nlinarith
  have hFcont : ContinuousOn F (Icc 0 1) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · subst h0
      have hF0 : F 0 = 0 := by simp [hF]
      rw [ContinuousWithinAt, hF0]
      refine squeeze_zero_norm' (eventually_nhdsWithin_of_forall fun s hs => hFbound s hs) ?_
      have : Tendsto (fun s : ℝ => 2 * (s * (1 - s))) (𝓝 0) (𝓝 (2 * (0 * (1 - 0)))) :=
        ((continuous_const.mul (continuous_id.mul (continuous_const.sub continuous_id)))).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · subst h1
      have hF1 : F 1 = 0 := by simp [hF]
      rw [ContinuousWithinAt, hF1]
      refine squeeze_zero_norm' (eventually_nhdsWithin_of_forall fun s hs => hFbound s hs) ?_
      have : Tendsto (fun s : ℝ => 2 * (s * (1 - s))) (𝓝 1) (𝓝 (2 * (1 * (1 - 1)))) :=
        ((continuous_const.mul (continuous_id.mul (continuous_const.sub continuous_id)))).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · exact (hderiv t ⟨h0, h1⟩).continuousAt.continuousWithinAt
  -- integrability
  have hG1int : IntervalIntegrable G1 volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
      integrableOn_Ioc_iff_integrableOn_Ioo]
    have hmA : Measurable (PickandsSpearman.extend A) := PickandsSpearman.measurable_extend hA
    have hG1' : EqOn G1 (fun t => ((1 - 2 * t) * deriv A t * PickandsSpearman.extend A t -
        t * (1 - t) * deriv A t * deriv A t) / PickandsSpearman.extend A t ^ 2) (Ioo 0 1) := by
      intro t ht
      simp only [hG1, PickandsSpearman.extend_eq ht]
    refine IntegrableOn.congr_fun ?_ hG1'.symm measurableSet_Ioo
    have hmD := measurable_deriv A
    have hmeas : Measurable (fun t => ((1 - 2 * t) * deriv A t * PickandsSpearman.extend A t -
        t * (1 - t) * deriv A t * deriv A t) / PickandsSpearman.extend A t ^ 2) := by
      fun_prop
    refine Measure.integrableOn_of_bounded (M := 8) measure_Ioo_lt_top.ne
      hmeas.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun t ht => ?_))
    simp only [PickandsSpearman.extend_eq ht]
    have hpos := hApos t (Ioo_subset_Icc_self ht)
    have hhalf := hA.half_le (Ioo_subset_Icc_self ht)
    have hd := hDb t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hle1 := hA.le_one t ⟨ht0.le, ht1.le⟩
    have h12 : |1 - 2 * t| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    have hAa : |A t| ≤ 1 := by rw [abs_of_pos hpos]; exact hle1
    have hta : |t| ≤ 1 := by rw [abs_of_pos ht0]; exact ht1.le
    have h1t : |1 - t| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    have m1 {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
      (mul_le_of_le_one_left hb0 ha).trans hb
    have e1 : |(1 - 2 * t) * deriv A t * A t| ≤ 1 := by
      rw [abs_mul, abs_mul]
      exact m1 (m1 h12 (abs_nonneg _) hd) (abs_nonneg _) hAa
    have e2 : |t * (1 - t) * deriv A t * deriv A t| ≤ 1 := by
      rw [abs_mul, abs_mul, abs_mul]
      exact m1 (m1 (m1 hta (abs_nonneg _) h1t) (abs_nonneg _) hd)
        (abs_nonneg _) hd
    have hnum : |(1 - 2 * t) * deriv A t * A t - t * (1 - t) * deriv A t * deriv A t| ≤ 2 := by
      have a1 := abs_le.1 e1
      have a2 := abs_le.1 e2
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have hA2 : 1 / 4 ≤ A t ^ 2 := by nlinarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < A t ^ 2),
      div_le_iff₀ (by positivity)]
    nlinarith
  have hG2int : IntervalIntegrable G2 volume 0 1 := by
    have hc : ContinuousOn (fun t => t * (1 - t) / A t) (uIcc 0 1) := by
      rw [uIcc_of_le zero_le_one]
      exact ((continuous_id.mul (continuous_const.sub continuous_id)).continuousOn).div
        hA.continuousOn fun t ht => (hApos t ht).ne'
    refine (hint.mul_continuousOn hc).congr ?_
    intro t _
    simp only [hG2]
    ring
  -- integrate
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hFcont hderiv
    (hG1int.add hG2int)
  have hF0 : F 0 = 0 := by simp [hF]
  have hF1 : F 1 = 0 := by simp [hF]
  rw [hF0, hF1, sub_zero, intervalIntegral.integral_add hG1int hG2int] at hFTC
  rw [kendallTau_pickandsCopula hA hdiff]
  have hcongr : (∫ t in (0 : ℝ)..1, (A t - t * deriv A t) * (A t + (1 - t) * deriv A t) /
      A t ^ 2) = ∫ t in (0 : ℝ)..1, (1 + G1 t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    have hAt := (hApos t ht).ne'
    simp only [hG1]
    field_simp
    ring
  rw [hcongr, intervalIntegral.integral_add intervalIntegrable_const hG1int]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  linarith

end ProbabilityTheory.Copula
