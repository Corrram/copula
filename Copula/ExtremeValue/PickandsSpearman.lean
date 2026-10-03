/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.ExtremeValue.PickandsConverse
import Copula.Rank.SpearmanCDF
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Convex.Continuous

/-! # Spearman's rho of extreme-value copulas

For a Pickands dependence function `A`,

`ρ(C_A) = 12 ∫₀¹ (A(t) + 1)⁻² dt - 3`   (`spearmanRho_pickandsCopula`),

and hence `ρ(C) = 12 ∫₀¹ (A_C(t) + 1)⁻² dt - 3` for every bivariate extreme-value copula
(`IsExtremeValue.spearmanRho_eq`).

Proof. With `ρ = 12 ∬ C_A - 3`, substitute, for fixed `v ∈ (0,1)`, `u = v^{1/t - 1}`
(`t = log v / log(uv) ∈ (0,1)`), so that `C_A(u,v) = v^{A(t)/t}` and
`du = (-log v) t⁻² v^{1/t - 1} dt`. After exchanging the order of integration (Tonelli), the inner
integral is `∫₀¹ (-log v) v^{(A(t)+1)/t - 1} dv = t² / (A(t) + 1)²`, a Gamma integral
(substitute `v = e^{-s}`). All integrals are computed as lower Lebesgue integrals of nonnegative
functions, so no integrability bookkeeping is needed for the exchange.

References: G. Gudendorf and J. Segers, *Extreme-value copulas* (2010);
W. Hürlimann, *Hutchinson–Lai's conjecture for bivariate extreme value copulas* (2003);
P. Capéraà, A.-L. Fougères and C. Genest, *A nonparametric estimation procedure for bivariate
extreme value copulas* (1997).
-/

open MeasureTheory Set
open scoped unitInterval ENNReal

namespace ProbabilityTheory.Copula

namespace PickandsSpearman

variable {A : ℝ → ℝ}

private theorem exp_lt_one_of_neg {z : ℝ} (hz : z < 0) : Real.exp z < 1 := by
  simpa using Real.exp_lt_exp.2 hz

open Classical in
/-- `A` on `(0,1)`, extended by `1`: a measurable version of a Pickands function. -/
noncomputable def extend (A : ℝ → ℝ) : ℝ → ℝ := (Ioo (0 : ℝ) 1).piecewise A (fun _ => 1)

theorem extend_eq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : extend A t = A t :=
  Set.piecewise_eq_of_mem _ _ _ ht

theorem measurable_extend (hA : IsPickandsFunction A) : Measurable (extend A) := by
  have h := hA.convexOn.continuousOn_interior
  rw [interior_Icc] at h
  exact h.measurable_piecewise continuousOn_const measurableSet_Ioo

theorem extend_pos (hA : IsPickandsFunction A) (t : ℝ) : 0 < extend A t := by
  by_cases ht : t ∈ Ioo (0 : ℝ) 1
  · rw [extend_eq ht]
    exact hA.pos (Ioo_subset_Icc_self ht)
  · rw [extend, Set.piecewise_eq_of_notMem _ _ _ ht]
    norm_num

/-- The Pickands CDF on `(0,1)²` as a function of two real variables. -/
noncomputable def kernel (A : ℝ → ℝ) (x y : ℝ) : ℝ :=
  Real.exp (Real.log (x * y) * extend A (Real.log y / Real.log (x * y)))

/-- The integrand after the substitution `x = y^{1/t - 1}`. -/
noncomputable def kernelT (A : ℝ → ℝ) (t y : ℝ) : ℝ :=
  -Real.log y * ((t⁻¹) ^ 2 * Real.exp (Real.log y * ((extend A t + 1) * t⁻¹ - 1)))

theorem measurable_kernelT (hA : IsPickandsFunction A) :
    Measurable (fun p : ℝ × ℝ => kernelT A p.2 p.1) := by
  have he := measurable_extend hA
  unfold kernelT
  fun_prop

theorem kernelT_nonneg {t y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : 0 ≤ kernelT A t y := by
  unfold kernelT
  have : 0 ≤ -Real.log y := neg_nonneg.2 (Real.log_nonpos hy.1.le hy.2.le)
  positivity

/-- The substitution map `t ↦ y ^ (1/t - 1) = exp(log y (1/t - 1))` of `(0,1)` onto itself. -/
noncomputable def substMap (y t : ℝ) : ℝ := Real.exp (Real.log y * (t⁻¹ - 1))

/-- The Jacobian `|d/dt substMap y t| = (-log y) t⁻² substMap y t`. -/
noncomputable def substJac (y t : ℝ) : ℝ := -Real.log y * ((t⁻¹) ^ 2 * substMap y t)

theorem substMap_pos (y t : ℝ) : 0 < substMap y t := Real.exp_pos _

theorem substJac_nonneg {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (t : ℝ) : 0 ≤ substJac y t := by
  have : 0 ≤ -Real.log y := neg_nonneg.2 (Real.log_nonpos hy.1.le hy.2.le)
  have := substMap_pos y t
  unfold substJac
  positivity

/-- The substitution `x = y ^ (1/t - 1)` for lower integrals over `(0,1)`. -/
theorem lintegral_subst {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (g : ℝ → ℝ≥0∞) :
    ∫⁻ x in Ioo (0 : ℝ) 1, g x =
      ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (substJac y t) * g (substMap y t) := by
  obtain ⟨hy0, hy1⟩ := hy
  have hL0 : Real.log y < 0 := Real.log_neg hy0 hy1
  have hLne : Real.log y ≠ 0 := hL0.ne
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (substMap y)
      (substMap y t * (Real.log y * (-(t ^ 2)⁻¹))) (Ioo 0 1) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => Real.log y * (t⁻¹ - 1)) (Real.log y * (-(t ^ 2)⁻¹)) t :=
      ((hasDerivAt_inv ht.1.ne').sub_const 1).const_mul (Real.log y)
    exact h1.exp.hasDerivWithinAt
  have hinj : InjOn (substMap y) (Ioo 0 1) := by
    intro a _ b _ hab
    have h := Real.exp_injective hab
    have h2 : a⁻¹ = b⁻¹ := by
      have := mul_left_cancel₀ hLne h
      linarith
    exact inv_injective h2
  have himg : substMap y '' Ioo 0 1 = Ioo 0 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨substMap_pos _ _, exp_lt_one_of_neg ?_⟩
      have : 1 < t⁻¹ := (one_lt_inv₀ ht.1).2 ht.2
      nlinarith
    · rintro ⟨hx0, hx1⟩
      have hlx : Real.log x < 0 := Real.log_neg hx0 hx1
      have hden : Real.log x + Real.log y < 0 := by linarith
      refine ⟨Real.log y / (Real.log x + Real.log y),
        ⟨div_pos_of_neg_of_neg hL0 hden, (div_lt_one_of_neg hden).2 (by linarith)⟩, ?_⟩
      rw [substMap, inv_div, div_sub_one hLne, mul_div_cancel₀ _ hLne, add_sub_cancel_right,
        Real.exp_log hx0]
  have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hderiv hinj g
  rw [himg] at key
  rw [key]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hpos : 0 < substMap y t * (Real.log y * (-(t ^ 2)⁻¹)) :=
    mul_pos (substMap_pos _ _)
      (mul_pos_of_neg_of_neg hL0 (neg_neg_of_pos (inv_pos.2 (pow_pos ht.1 2))))
  simp only
  rw [abs_of_pos hpos, substJac, inv_pow]
  congr 2
  ring

theorem log_substMap_mul {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    Real.log (substMap y t * y) = Real.log y * t⁻¹ := by
  rw [Real.log_mul (substMap_pos y t).ne' hy.1.ne', substMap, Real.log_exp]
  ring

theorem ratio_substMap {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    Real.log y / Real.log (substMap y t * y) = t := by
  have hLne : Real.log y ≠ 0 := (Real.log_neg hy.1 hy.2).ne
  rw [log_substMap_mul hy]
  field_simp

/-- The Gamma integral `∫₀¹ (-log y) y^{b-1} dy = 1 / b²` for `b > 0`. -/
theorem lintegral_gamma {b : ℝ} (hb0 : 0 < b) :
    ∫⁻ y in Ioo (0 : ℝ) 1, ENNReal.ofReal (-Real.log y * Real.exp (Real.log y * (b - 1))) =
      ENNReal.ofReal (1 / b ^ 2) := by
  have hbinv : 0 < b⁻¹ := inv_pos.2 hb0
  have himg : (fun s : ℝ => Real.exp (-(s * b⁻¹))) '' Ioi 0 = Ioo 0 1 := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨Real.exp_pos _, exp_lt_one_of_neg (neg_neg_of_pos (mul_pos hs hbinv))⟩
    · rintro ⟨hy0, hy1⟩
      refine ⟨-Real.log y * b, mul_pos (neg_pos.2 (Real.log_neg hy0 hy1)) hb0, ?_⟩
      simp only
      rw [mul_assoc, mul_inv_cancel₀ hb0.ne', mul_one, neg_neg, Real.exp_log hy0]
  have hderiv : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun s : ℝ => Real.exp (-(s * b⁻¹)))
      (Real.exp (-(s * b⁻¹)) * -(1 * b⁻¹)) (Ioi 0) s := by
    intro s _
    exact (((hasDerivAt_id s).mul_const b⁻¹).neg.exp).hasDerivWithinAt
  have hinj : InjOn (fun s : ℝ => Real.exp (-(s * b⁻¹))) (Ioi 0) := by
    intro a _ c _ h
    have h' := Real.exp_injective h
    have : a * b⁻¹ = c * b⁻¹ := by linarith
    exact mul_right_cancel₀ hbinv.ne' this
  have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj
    (fun y => ENNReal.ofReal (-Real.log y * Real.exp (Real.log y * (b - 1))))
  rw [himg] at key
  rw [key]
  have hpt : EqOn (fun s => ENNReal.ofReal |Real.exp (-(s * b⁻¹)) * -(1 * b⁻¹)| *
      ENNReal.ofReal (-Real.log (Real.exp (-(s * b⁻¹))) *
        Real.exp (Real.log (Real.exp (-(s * b⁻¹))) * (b - 1))))
      (fun s => ENNReal.ofReal ((b⁻¹) ^ 2 * (Real.exp (-s) * s))) (Ioi 0) := by
    intro s _
    simp only
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [abs_of_neg (mul_neg_of_pos_of_neg (Real.exp_pos _) (by linarith)), Real.log_exp]
    have : Real.exp (-(s * b⁻¹)) * Real.exp (-(s * b⁻¹) * (b - 1)) = Real.exp (-s) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    rw [← this]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  have h1 : IntegrableOn (fun s : ℝ => Real.exp (-s) * s) (Ioi 0) := by
    refine (Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 2)).congr_fun
      (fun x _ => ?_) measurableSet_Ioi
    simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  have hint : IntegrableOn (fun s : ℝ => (b⁻¹) ^ 2 * (Real.exp (-s) * s)) (Ioi 0) :=
    h1.const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [integral_const_mul]
    have hg := Real.Gamma_eq_integral (by norm_num : (0 : ℝ) < 2)
    have h2 : Real.Gamma 2 = 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero, Real.Gamma_one,
        mul_one]
    simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, h2] at hg
    rw [← hg, mul_one, inv_pow, one_div]
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs => ?_)
    have : (0 : ℝ) < s := hs
    positivity

/-- The inner substitution `x = exp(log y (1/t - 1))` for the Pickands CDF. -/
theorem lintegral_kernel {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (kernel A x y) =
      ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (kernelT A t y) := by
  rw [lintegral_subst hy]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t _
  simp only
  rw [← ENNReal.ofReal_mul (substJac_nonneg hy t)]
  congr 1
  rw [kernel, ratio_substMap hy t, log_substMap_mul hy, kernelT, substJac, substMap]
  have hexp : Real.exp (Real.log y * (t⁻¹ - 1)) * Real.exp (Real.log y * t⁻¹ * extend A t) =
      Real.exp (Real.log y * ((extend A t + 1) * t⁻¹ - 1)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [← hexp]
  ring

/-- The inner Gamma integral `∫₀¹ (-log y) y^{b-1} dy · t⁻² = (A(t) + 1)⁻²`. -/
theorem lintegral_kernelT (hA : IsPickandsFunction A) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∫⁻ y in Ioo (0 : ℝ) 1, ENNReal.ofReal (kernelT A t y) =
      ENNReal.ofReal (1 / (extend A t + 1) ^ 2) := by
  have hE := extend_pos hA t
  have ht0 := ht.1
  have hb0 : 0 < (extend A t + 1) * t⁻¹ := mul_pos (by linarith) (inv_pos.2 ht0)
  have hpt : ∀ y, ENNReal.ofReal (kernelT A t y) = ENNReal.ofReal ((t⁻¹) ^ 2) *
      ENNReal.ofReal (-Real.log y * Real.exp (Real.log y * ((extend A t + 1) * t⁻¹ - 1))) := by
    intro y
    rw [← ENNReal.ofReal_mul (by positivity), kernelT]
    ring_nf
  simp only [hpt]
  rw [lintegral_const_mul _ (by fun_prop), lintegral_gamma hb0, ← ENNReal.ofReal_mul
    (by positivity)]
  congr 1
  field_simp

theorem lintegral_unitInterval_Ioo (G : ℝ → ℝ≥0∞) :
    ∫⁻ u : I, G u = ∫⁻ x in Ioo (0 : ℝ) 1, G x := by
  rw [unitInterval.measurePreserving_coe.lintegral_comp_emb unitInterval.measurableEmbedding_coe G]
  exact setLIntegral_congr Ioo_ae_eq_Icc.symm

theorem cdf_eq_kernel (hA : IsPickandsFunction A) {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    (pickandsCopula A hA).cdf ![projIcc 0 1 zero_le_one x, projIcc 0 1 zero_le_one y] =
      kernel A x y := by
  have hpx : ((projIcc 0 1 zero_le_one x : I) : ℝ) = x := by
    rw [projIcc_of_mem _ (Ioo_subset_Icc_self hx)]
  have hpy : ((projIcc 0 1 zero_le_one y : I) : ℝ) = y := by
    rw [projIcc_of_mem _ (Ioo_subset_Icc_self hy)]
  have hx0 : projIcc 0 1 zero_le_one x ≠ 0 := by
    intro h
    have := congrArg (fun z : I => (z : ℝ)) h
    simp only [hpx, Set.Icc.coe_zero] at this
    exact hx.1.ne' this
  have hy0 : projIcc 0 1 zero_le_one y ≠ 0 := by
    intro h
    have := congrArg (fun z : I => (z : ℝ)) h
    simp only [hpy, Set.Icc.coe_zero] at this
    exact hy.1.ne' this
  rw [cdf_pickandsCopula_eq_exp hA hx0 hy0, hpx, hpy, kernel]
  have hlx := Real.log_neg hx.1 hx.2
  have hly := Real.log_neg hy.1 hy.2
  have hmem : Real.log y / Real.log (x * y) ∈ Ioo (0 : ℝ) 1 := by
    rw [Real.log_mul hx.1.ne' hy.1.ne']
    exact ⟨div_pos_of_neg_of_neg hly (by linarith), (div_lt_one_of_neg (by linarith)).2
      (by linarith)⟩
  rw [extend_eq hmem]

/-- The double integral `∬ C_A = ∫₀¹ (A(t) + 1)⁻² dt`, as a lower Lebesgue integral. -/
theorem lintegral_cdf (hA : IsPickandsFunction A) :
    ∫⁻ x, ENNReal.ofReal ((pickandsCopula A hA).cdf x) ∂(independence 2).toMeasure =
      ENNReal.ofReal (∫ t in Ioo (0 : ℝ) 1, 1 / (extend A t + 1) ^ 2) := by
  set C := pickandsCopula A hA
  rw [toMeasure_independence]
  change ∫⁻ x, ENNReal.ofReal (C.cdf x) ∂(volume : Measure (Fin 2 → I)) = _
  rw [← ((volume_preserving_finTwoArrow I).symm _).lintegral_comp_emb
    MeasurableEquiv.finTwoArrow.symm.measurableEmbedding]
  have hsymm : ∀ p : I × I, MeasurableEquiv.finTwoArrow.symm p = ![p.1, p.2] := by
    intro p
    ext i
    fin_cases i <;> rfl
  simp only [hsymm]
  change ∫⁻ p : I × I, ENNReal.ofReal (C.cdf ![p.1, p.2]) ∂((volume : Measure I).prod volume) = _
  have hmeas : Measurable fun p : I × I => ENNReal.ofReal (C.cdf ![p.1, p.2]) :=
    ENNReal.measurable_ofReal.comp
      (C.continuous_cdf.comp (by fun_prop : Continuous fun p : I × I => ![p.1, p.2])).measurable
  rw [lintegral_prod_symm (fun p : I × I => ENNReal.ofReal (C.cdf ![p.1, p.2]))
    hmeas.aemeasurable]
  -- move both integrals to `(0,1) ⊆ ℝ`
  have hinner : ∀ v : I, ∫⁻ u : I, ENNReal.ofReal (C.cdf ![u, v]) =
      ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (C.cdf ![projIcc 0 1 zero_le_one x, v]) := by
    intro v
    rw [← lintegral_unitInterval_Ioo]
    simp only [projIcc_val]
  simp only [hinner]
  have houter : ∫⁻ y : I, ∫⁻ x in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (C.cdf ![projIcc 0 1 zero_le_one x, y]) =
      ∫⁻ y in Ioo (0 : ℝ) 1, ∫⁻ x in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (C.cdf ![projIcc 0 1 zero_le_one x, projIcc 0 1 zero_le_one y]) := by
    rw [← lintegral_unitInterval_Ioo]
    simp only [projIcc_val]
  rw [houter]
  · -- pointwise identification, substitution, swap, Gamma integral
    have h1 : ∫⁻ y in Ioo (0 : ℝ) 1, ∫⁻ x in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (C.cdf ![projIcc 0 1 zero_le_one x, projIcc 0 1 zero_le_one y]) =
        ∫⁻ y in Ioo (0 : ℝ) 1, ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (kernelT A t y) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro y hy
      simp only
      rw [← lintegral_kernel hy]
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro x hx
      simp only [C, cdf_eq_kernel hA hx hy]
    have hm : Measurable (Function.uncurry fun y t => ENNReal.ofReal (kernelT A t y)) :=
      ENNReal.measurable_ofReal.comp (measurable_kernelT hA)
    rw [h1, lintegral_lintegral_swap hm.aemeasurable]
    rw [setLIntegral_congr_fun measurableSet_Ioo (fun t ht => lintegral_kernelT hA ht)]
    have hint : IntegrableOn (fun t => 1 / (extend A t + 1) ^ 2) (Ioo (0 : ℝ) 1) := by
      refine Measure.integrableOn_of_bounded (M := 1) measure_Ioo_lt_top.ne ?_ ?_
      · exact (((measurable_extend hA).add_const 1).pow_const 2).const_div 1 |>.aestronglyMeasurable
      · refine ae_of_all _ fun t => ?_
        have := extend_pos hA t
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
        rw [div_le_one (by positivity)]
        nlinarith
    rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun t => by
      have := extend_pos hA t
      positivity)]

end PickandsSpearman

open PickandsSpearman in
/-- **Spearman's rho of a Pickands copula**: `ρ(C_A) = 12 ∫₀¹ (A(t) + 1)⁻² dt - 3`. -/
theorem spearmanRho_pickandsCopula {A : ℝ → ℝ} (hA : IsPickandsFunction A) :
    (pickandsCopula A hA).spearmanRho = 12 * (∫ t in (0 : ℝ)..1, 1 / (A t + 1) ^ 2) - 3 := by
  rw [spearmanRho_eq_integral_cdf, integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun x => cdf_nonneg _ x) (continuous_cdf _).aestronglyMeasurable,
    lintegral_cdf hA, ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioo fun t _ => by
      have := extend_pos hA t
      positivity), intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  congr 2
  exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by simp only [extend_eq ht]

/-- Spearman's rho of a bivariate extreme-value copula:
`ρ(C) = 12 ∫₀¹ (A_C(t) + 1)⁻² dt - 3`. -/
theorem IsExtremeValue.spearmanRho_eq {C : Copula 2} (hC : C.IsExtremeValue) :
    C.spearmanRho = 12 * (∫ t in (0 : ℝ)..1, 1 / (pickandsOf C t + 1) ^ 2) - 3 := by
  have h := spearmanRho_pickandsCopula hC.isPickandsFunction_pickandsOf
  rwa [← hC.eq_pickandsCopula] at h

end ProbabilityTheory.Copula
