/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Measures.Uniform
import Copula.Measures.CDFDistanceBenchmarks
import Copula.Rearrangement.PrimitiveIntegral
import Copula.Rearrangement.SI

/-! # Sharp upper bounds for the Schweizer–Wolff `σ` and Hoeffding's `Φ²`

Nelsen, *An Introduction to Copulas*, 2nd ed., §5.3.1: the normalized `L¹` and `L²` distances to
independence satisfy `σ(C) ≤ 1` and `Φ²(C) ≤ 1`, with equality if and only if `C = M` or
`C = W`. The uniform version satisfies `κ(C) ≤ 1` with equality if and only if `|β(C)| = 1`.

The proof works sectionwise. For fixed `v`, the section `F(u) = C(u,v) - uv` is the primitive of
the mean-zero function `∂₁C(·,v) - v`. By the primitive comparison lemma
(`Copula.Rearrangement.PrimitiveIntegral`), `∫ |F| ≤ ∫ G` and `∫ F² ≤ ∫ G²` where
`G(u) = C↑(u,v) - uv` is the section of the SI rearrangement `C↑` (`upRearr`), and the
inequalities are strict when `F` changes sign. Since `Π ≤ C↑ ≤ M`, `0 ≤ G ≤ M - Π`, which gives
`σ(C) ≤ σ(C↑) ≤ σ(M) = 1` and `Φ²(C) ≤ Φ²(C↑) ≤ Φ²(M) = 1`. In the equality case almost every
section has constant sign and coincides with the section of `M` (nonnegative case) or of `W`
(nonpositive case); the two cases cannot both occur for sections in `(0,1)`, and continuity
in `v` gives `C = M` or `C = W`.
-/

open MeasureTheory Set Filter
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-! ## Auxiliary facts on the unit interval -/

theorem integrable_of_continuous_unit {f : I → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- A parametric integral of a jointly continuous function is integrable in the parameter. -/
theorem integrable_integral_of_continuous {f : I → I → ℝ}
    (hf : Continuous fun p : I × I => f p.1 p.2) : Integrable fun v : I => ∫ u : I, f u v := by
  have hi : Integrable (fun p : I × I => f p.2 p.1) ((volume : Measure I).prod volume) :=
    (hf.comp continuous_swap).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact hi.integral_prod_left

/-- Two continuous functions `a ≤ b` on the unit interval with equal integrals coincide. -/
theorem eq_of_le_of_integral_eq_unit {a b : I → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hab : ∀ u, a u ≤ b u) (h : (∫ u, a u) = ∫ u, b u) : a = b := by
  have hi : Integrable (fun u => b u - a u) := integrable_of_continuous_unit (hb.sub ha)
  have h0 : (∫ u, (b u - a u)) = 0 := by
    rw [integral_sub (integrable_of_continuous_unit hb) (integrable_of_continuous_unit ha), h,
      sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg (fun u => sub_nonneg.mpr (hab u)) hi).mp h0
  have heq := (Continuous.ae_eq_iff_eq volume (hb.sub ha) continuous_zero).mp hae
  funext u
  have hu := congrFun heq u
  simp only [Pi.zero_apply, Pi.sub_apply] at hu
  linarith

theorem continuous_cdf_pair (C : Copula 2) : Continuous fun p : I × I => C.cdf ![p.1, p.2] :=
  C.continuous_cdf.comp (by fun_prop)

theorem continuous_cdf_section (C : Copula 2) (v : I) : Continuous fun u : I => C.cdf ![u, v] :=
  C.continuous_cdf.comp (by fun_prop)

theorem continuous_cdf_section_right (C : Copula 2) (u : I) :
    Continuous fun v : I => C.cdf ![u, v] :=
  C.continuous_cdf.comp (by fun_prop)

theorem continuous_cdf_sub_mul_section (C : Copula 2) (v : I) :
    Continuous fun u : I => C.cdf ![u, v] - (u : ℝ) * v :=
  (C.continuous_cdf_section v).sub (by fun_prop)

theorem continuous_cdf_sub_mul_pair (C : Copula 2) :
    Continuous fun p : I × I => C.cdf ![p.1, p.2] - (p.1 : ℝ) * p.2 :=
  C.continuous_cdf_pair.sub (by fun_prop)

/-- Two bivariate copulas whose `v`-sections agree for almost every `v` are equal. -/
theorem eq_of_ae_section {C D : Copula 2}
    (h : ∀ᵐ v : I, ∀ u : I, C.cdf ![u, v] = D.cdf ![u, v]) : C = D := by
  apply ext_cdf_two
  intro u v
  have hc := (Continuous.ae_eq_iff_eq volume (C.continuous_cdf_section_right u)
    (D.continuous_cdf_section_right u)).mp (h.mono fun w hw => hw u)
  exact congrFun hc v

/-! ## Sections and the SI rearrangement -/

theorem cdf_sub_mul_eq_primDev (C : Copula 2) (u v : I) :
    C.cdf ![u, v] - (u : ℝ) * v = primDev (condSection C v) (v : ℝ) u := by
  rw [cdf_eq_integral_condSection]
  rfl

theorem upRearr_cdf_sub_mul_eq_rearrDev (C : Copula 2) (u v : I) :
    (upRearr C).cdf ![u, v] - (u : ℝ) * v = rearrDev (condSection C v) (v : ℝ) u := by
  rw [upRearr_cdf_eq_integral]
  rfl

theorem mul_le_upRearr_cdf (C : Copula 2) (u v : I) :
    (u : ℝ) * v ≤ (upRearr C).cdf ![u, v] :=
  upRearr_isPQD C u v

/-- Sectionwise `L¹` comparison with the SI rearrangement. -/
theorem integral_abs_cdf_sub_mul_le_upRearr (C : Copula 2) (v : I) :
    (∫ u : I, |C.cdf ![u, v] - (u : ℝ) * v|) ≤
      ∫ u : I, ((upRearr C).cdf ![u, v] - (u : ℝ) * v) := by
  simp only [upRearr_cdf_sub_mul_eq_rearrDev]
  simp only [cdf_sub_mul_eq_primDev]
  exact integral_abs_primDev_le (condSection_nonneg C v) (condSection_le_one C v)
    (condSection_measurable C v) (integral_condSection C v)

/-- Sectionwise `L²` comparison with the SI rearrangement. -/
theorem integral_sq_cdf_sub_mul_le_upRearr (C : Copula 2) (v : I) :
    (∫ u : I, (C.cdf ![u, v] - (u : ℝ) * v) ^ 2) ≤
      ∫ u : I, ((upRearr C).cdf ![u, v] - (u : ℝ) * v) ^ 2 := by
  simp only [upRearr_cdf_sub_mul_eq_rearrDev]
  simp only [cdf_sub_mul_eq_primDev]
  exact integral_sq_primDev_le (condSection_nonneg C v) (condSection_le_one C v)
    (condSection_measurable C v) (integral_condSection C v)

/-- Strict sectionwise `L¹` comparison when the section changes sign. -/
theorem integral_abs_cdf_sub_mul_lt_upRearr (C : Copula 2) (v : I) {t₁ t₂ : I}
    (h₁ : 0 < C.cdf ![t₁, v] - (t₁ : ℝ) * v) (h₂ : C.cdf ![t₂, v] - (t₂ : ℝ) * v < 0) :
    (∫ u : I, |C.cdf ![u, v] - (u : ℝ) * v|) <
      ∫ u : I, ((upRearr C).cdf ![u, v] - (u : ℝ) * v) := by
  rw [cdf_sub_mul_eq_primDev] at h₁ h₂
  simp only [upRearr_cdf_sub_mul_eq_rearrDev]
  simp only [cdf_sub_mul_eq_primDev]
  exact integral_abs_primDev_lt (condSection_nonneg C v) (condSection_le_one C v)
    (condSection_measurable C v) (integral_condSection C v) h₁ h₂

/-- Strict sectionwise `L²` comparison when the section changes sign. -/
theorem integral_sq_cdf_sub_mul_lt_upRearr (C : Copula 2) (v : I) {t₁ t₂ : I}
    (h₁ : 0 < C.cdf ![t₁, v] - (t₁ : ℝ) * v) (h₂ : C.cdf ![t₂, v] - (t₂ : ℝ) * v < 0) :
    (∫ u : I, (C.cdf ![u, v] - (u : ℝ) * v) ^ 2) <
      ∫ u : I, ((upRearr C).cdf ![u, v] - (u : ℝ) * v) ^ 2 := by
  rw [cdf_sub_mul_eq_primDev] at h₁ h₂
  simp only [upRearr_cdf_sub_mul_eq_rearrDev]
  simp only [cdf_sub_mul_eq_primDev]
  exact integral_sq_primDev_lt (condSection_nonneg C v) (condSection_le_one C v)
    (condSection_measurable C v) (integral_condSection C v) h₁ h₂

/-! ## Sectionwise comparison with the Fréchet–Hoeffding bounds -/

theorem cdf_sub_mul_le_comonotonic (C : Copula 2) (u v : I) :
    C.cdf ![u, v] - (u : ℝ) * v ≤ (comonotonic 2).cdf ![u, v] - (u : ℝ) * v :=
  sub_le_sub_right (C.cdf_le_comonotonic _) _

theorem comonotonic_cdf_sub_mul_nonneg (u v : I) :
    0 ≤ (comonotonic 2).cdf ![u, v] - (u : ℝ) * v := by
  rw [cdf_comonotonic_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  apply sub_nonneg.mpr
  apply le_min
  · nlinarith [u.property.1, v.property.2]
  · nlinarith [v.property.1, u.property.2]

/-- The section of `u v - W(u,v)` is the reflected section of `M(u,v) - u v`. -/
theorem mul_sub_countermonotonic_cdf (u v : I) :
    (u : ℝ) * v - countermonotonic.cdf ![u, v] =
      (comonotonic 2).cdf ![unitInterval.symm u, v] - (unitInterval.symm u : ℝ) * v := by
  rw [cdf_comonotonic_two, cdf_countermonotonic]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, unitInterval.coe_symm_eq]
  rcases le_total (1 - (u : ℝ)) v with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_left (by linarith)]
    ring

theorem neg_cdf_sub_mul_le (C : Copula 2) (u v : I) :
    -(C.cdf ![u, v] - (u : ℝ) * v) ≤
      (comonotonic 2).cdf ![unitInterval.symm u, v] - (unitInterval.symm u : ℝ) * v := by
  rw [← mul_sub_countermonotonic_cdf]
  linarith [C.cdf_countermonotonic_le ![u, v]]

/-- For a function `φ` of the deviation, reflecting the first coordinate of the section of
`M - Π` does not change its integral. -/
theorem integral_comp_comonotonic_symm (φ : ℝ → ℝ) (v : I) :
    (∫ u : I, φ ((comonotonic 2).cdf ![unitInterval.symm u, v] -
        (unitInterval.symm u : ℝ) * v)) =
      ∫ u : I, φ ((comonotonic 2).cdf ![u, v] - (u : ℝ) * v) :=
  unitInterval.measurePreserving_symm.integral_comp
    unitInterval.symmMeasurableEquiv.measurableEmbedding
    (fun u : I => φ ((comonotonic 2).cdf ![u, v] - (u : ℝ) * v))

/-- If a monotone, sign-invariant, injective-on-`[0,∞)` function `φ` of a constant-sign
section of `C - Π` has the same integral as that of `M - Π`, then the section is the
section of `M` or of `W`. -/
theorem section_eq_of_integral_comp_eq {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hmono : ∀ s t, 0 ≤ s → s ≤ t → φ s ≤ φ t)
    (hinj : ∀ s t, 0 ≤ s → 0 ≤ t → φ s = φ t → s = t) (hneg : ∀ t, φ (-t) = φ t)
    (C : Copula 2) (v : I)
    (hsign : (∀ u : I, 0 ≤ C.cdf ![u, v] - (u : ℝ) * v) ∨
      (∀ u : I, C.cdf ![u, v] - (u : ℝ) * v ≤ 0))
    (heq : (∫ u : I, φ (C.cdf ![u, v] - (u : ℝ) * v)) =
      ∫ u : I, φ ((comonotonic 2).cdf ![u, v] - (u : ℝ) * v)) :
    (∀ u, C.cdf ![u, v] = (comonotonic 2).cdf ![u, v]) ∨
      (∀ u, C.cdf ![u, v] = countermonotonic.cdf ![u, v]) := by
  have hF := C.continuous_cdf_sub_mul_section v
  have hH := (comonotonic 2).continuous_cdf_sub_mul_section v
  rcases hsign with hpos | hnpos
  · left
    have he := eq_of_le_of_integral_eq_unit (a := fun u : I => φ (C.cdf ![u, v] - (u : ℝ) * v))
      (b := fun u : I => φ ((comonotonic 2).cdf ![u, v] - (u : ℝ) * v)) (hφ.comp hF)
      (hφ.comp hH) (fun u => hmono _ _ (hpos u) (C.cdf_sub_mul_le_comonotonic u v)) heq
    intro u
    have hu := hinj _ _ (hpos u) (comonotonic_cdf_sub_mul_nonneg u v) (congrFun he u)
    linarith
  · right
    have hK : Continuous fun u : I =>
        (comonotonic 2).cdf ![unitInterval.symm u, v] - (unitInterval.symm u : ℝ) * v :=
      ((comonotonic 2).continuous_cdf_sub_mul_section v).comp unitInterval.continuous_symm
    have hi : (∫ u : I, φ (-(C.cdf ![u, v] - (u : ℝ) * v))) =
        ∫ u : I, φ ((comonotonic 2).cdf ![unitInterval.symm u, v] -
          (unitInterval.symm u : ℝ) * v) := by
      simp only [hneg]
      rw [heq, integral_comp_comonotonic_symm φ v]
    have he := eq_of_le_of_integral_eq_unit
      (a := fun u : I => φ (-(C.cdf ![u, v] - (u : ℝ) * v)))
      (b := fun u : I => φ ((comonotonic 2).cdf ![unitInterval.symm u, v] -
        (unitInterval.symm u : ℝ) * v)) (hφ.comp hF.neg) (hφ.comp hK)
      (fun u => hmono _ _ (by linarith [hnpos u]) (C.neg_cdf_sub_mul_le u v)) hi
    intro u
    have hu := hinj _ _ (by linarith [hnpos u])
      (comonotonic_cdf_sub_mul_nonneg (unitInterval.symm u) v) (congrFun he u)
    rw [← mul_sub_countermonotonic_cdf] at hu
    linarith

/-- A section of `M` in `(0,1)` and a section of `W` in `(0,1)` cannot belong to the same
copula. -/
theorem not_section_comonotonic_and_countermonotonic (C : Copula 2) {v₁ v₂ : I}
    (h₁0 : 0 < (v₁ : ℝ)) (h₂0 : 0 < (v₂ : ℝ)) (h₁1 : (v₁ : ℝ) < 1) (h₂1 : (v₂ : ℝ) < 1)
    (h₁ : ∀ u, C.cdf ![u, v₁] = (comonotonic 2).cdf ![u, v₁])
    (h₂ : ∀ u, C.cdf ![u, v₂] = countermonotonic.cdf ![u, v₂]) : False := by
  simp only [cdf_comonotonic_two, cdf_countermonotonic, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h₁ h₂
  rcases le_total v₁ v₂ with hle | hle
  · have hmono : C.cdf ![v₁, v₁] ≤ C.cdf ![v₁, v₂] := by
      apply C.monotone_cdf
      intro i
      fin_cases i
      · exact le_rfl
      · exact hle
    rw [h₁ v₁, h₂ v₁, min_self] at hmono
    have : max 0 ((v₁ : ℝ) + v₂ - 1) < v₁ := max_lt h₁0 (by linarith)
    linarith
  · have hl := C.abs_cdf_sub_le_sum_abs ![unitInterval.symm v₂, v₁] ![unitInterval.symm v₂, v₂]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sub_self,
      abs_zero, zero_add] at hl
    rw [h₁, h₂, unitInterval.coe_symm_eq, show 1 - (v₂ : ℝ) + v₂ - 1 = 0 by ring, max_self,
      sub_zero, abs_of_nonneg (sub_nonneg.mpr (show (v₂ : ℝ) ≤ v₁ from hle))] at hl
    have hm : 0 ≤ min (1 - (v₂ : ℝ)) v₁ := le_min (by linarith) h₁0.le
    rw [abs_of_nonneg hm] at hl
    rcases min_choice (1 - (v₂ : ℝ)) v₁ with h | h <;> rw [h] at hl <;> linarith

/-- If almost every `v`-section of `C` is a section of `M` or of `W`, then `C = M` or
`C = W`. -/
theorem eq_comonotonic_or_countermonotonic_of_ae_section (C : Copula 2)
    (h : ∀ᵐ v : I, (∀ u, C.cdf ![u, v] = (comonotonic 2).cdf ![u, v]) ∨
      (∀ u, C.cdf ![u, v] = countermonotonic.cdf ![u, v])) :
    C = comonotonic 2 ∨ C = countermonotonic := by
  have h0 : ∀ᵐ v : I, v ≠ 0 := by simp [ae_iff]
  have h1 : ∀ᵐ v : I, v ≠ 1 := by simp [ae_iff]
  have hpos (v : I) (hv : v ≠ 0) : 0 < (v : ℝ) := by
    have := unitInterval.pos_iff_ne_zero.mpr hv
    exact_mod_cast this
  have hlt (v : I) (hv : v ≠ 1) : (v : ℝ) < 1 := by
    have := unitInterval.lt_one_iff_ne_one.mpr hv
    exact_mod_cast this
  by_cases hex : ∃ v₁ : I, 0 < (v₁ : ℝ) ∧ (v₁ : ℝ) < 1 ∧
      ∀ u, C.cdf ![u, v₁] = (comonotonic 2).cdf ![u, v₁]
  · obtain ⟨v₁, hv₁0, hv₁1, hv₁⟩ := hex
    left
    apply eq_of_ae_section
    filter_upwards [h, h0, h1] with v hv hv0 hv1
    rcases hv with hv | hv
    · exact hv
    · exact (C.not_section_comonotonic_and_countermonotonic hv₁0 (hpos v hv0) hv₁1
        (hlt v hv1) hv₁ hv).elim
  · right
    apply eq_of_ae_section
    filter_upwards [h, h0, h1] with v hv hv0 hv1
    rcases hv with hv | hv
    · exact (hex ⟨v, hpos v hv0, hlt v hv1, hv⟩).elim
    · exact hv

/-! ## The Schweizer–Wolff `σ` -/

/-- Sectionwise, the `L¹` deviation of `C` from `Π` is dominated by that of `M`. -/
theorem integral_abs_cdf_sub_mul_le_comonotonic (C : Copula 2) (v : I) :
    (∫ u : I, |C.cdf ![u, v] - (u : ℝ) * v|) ≤
      ∫ u : I, |(comonotonic 2).cdf ![u, v] - (u : ℝ) * v| := by
  refine (C.integral_abs_cdf_sub_mul_le_upRearr v).trans (integral_mono
    (integrable_of_continuous_unit ((upRearr C).continuous_cdf_sub_mul_section v))
    (integrable_of_continuous_unit ((comonotonic 2).continuous_cdf_sub_mul_section v).abs)
    fun u => ?_)
  exact ((upRearr C).cdf_sub_mul_le_comonotonic u v).trans (le_abs_self _)

/-- The Schweizer–Wolff measure is dominated by that of the SI rearrangement,
`σ(C) ≤ σ(C↑) = ρ(C↑)`. -/
theorem schweizerWolff_le_schweizerWolff_upRearr (C : Copula 2) :
    C.schweizerWolff ≤ (upRearr C).schweizerWolff := by
  rw [schweizerWolff_eq_iterated, schweizerWolff_eq_iterated]
  have h := integral_mono
    (integrable_integral_of_continuous (f := fun u v : I => |C.cdf ![u, v] - (u : ℝ) * v|)
      C.continuous_cdf_sub_mul_pair.abs)
    (integrable_integral_of_continuous
      (f := fun u v : I => |(upRearr C).cdf ![u, v] - (u : ℝ) * v|)
      (upRearr C).continuous_cdf_sub_mul_pair.abs)
    (fun v => (C.integral_abs_cdf_sub_mul_le_upRearr v).trans (le_of_eq (integral_congr_ae
      (Eventually.of_forall fun u => (abs_of_nonneg (sub_nonneg.mpr
        (C.mul_le_upRearr_cdf u v))).symm))))
  linarith

/-- The Schweizer–Wolff measure is at most one (Nelsen §5.3.1). -/
theorem schweizerWolff_le_one (C : Copula 2) : C.schweizerWolff ≤ 1 := by
  have hM := schweizerWolff_comonotonic
  rw [schweizerWolff_eq_iterated] at hM ⊢
  have h := integral_mono
    (integrable_integral_of_continuous (f := fun u v : I => |C.cdf ![u, v] - (u : ℝ) * v|)
      C.continuous_cdf_sub_mul_pair.abs)
    (integrable_integral_of_continuous
      (f := fun u v : I => |(comonotonic 2).cdf ![u, v] - (u : ℝ) * v|)
      (comonotonic 2).continuous_cdf_sub_mul_pair.abs)
    (C.integral_abs_cdf_sub_mul_le_comonotonic)
  linarith

theorem schweizerWolff_mem_Icc (C : Copula 2) : C.schweizerWolff ∈ Icc (0 : ℝ) 1 :=
  ⟨C.schweizerWolff_nonneg, C.schweizerWolff_le_one⟩

/-- A section with the maximal `L¹` deviation has constant sign. -/
theorem section_sign_of_integral_abs_eq (C : Copula 2) (v : I)
    (h : (∫ u : I, |C.cdf ![u, v] - (u : ℝ) * v|) =
      ∫ u : I, |(comonotonic 2).cdf ![u, v] - (u : ℝ) * v|) :
    (∀ u : I, 0 ≤ C.cdf ![u, v] - (u : ℝ) * v) ∨ (∀ u : I, C.cdf ![u, v] - (u : ℝ) * v ≤ 0) := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨t₂, ht₂⟩, ⟨t₁, ht₁⟩⟩ := hc
  have hlt := C.integral_abs_cdf_sub_mul_lt_upRearr v ht₁ ht₂
  have hle : (∫ u : I, ((upRearr C).cdf ![u, v] - (u : ℝ) * v)) ≤
      ∫ u : I, |(comonotonic 2).cdf ![u, v] - (u : ℝ) * v| :=
    integral_mono (integrable_of_continuous_unit ((upRearr C).continuous_cdf_sub_mul_section v))
      (integrable_of_continuous_unit ((comonotonic 2).continuous_cdf_sub_mul_section v).abs)
      fun u => ((upRearr C).cdf_sub_mul_le_comonotonic u v).trans (le_abs_self _)
  linarith

/-- `σ(C) = 1` if and only if `C` is one of the Fréchet–Hoeffding bounds (Nelsen §5.3.1). -/
theorem schweizerWolff_eq_one_iff (C : Copula 2) :
    C.schweizerWolff = 1 ↔ C = comonotonic 2 ∨ C = countermonotonic := by
  constructor
  · intro h1
    apply eq_comonotonic_or_countermonotonic_of_ae_section
    have hS := integrable_integral_of_continuous
      (f := fun u v : I => |C.cdf ![u, v] - (u : ℝ) * v|) C.continuous_cdf_sub_mul_pair.abs
    have hT := integrable_integral_of_continuous
      (f := fun u v : I => |(comonotonic 2).cdf ![u, v] - (u : ℝ) * v|)
      (comonotonic 2).continuous_cdf_sub_mul_pair.abs
    have hM := schweizerWolff_comonotonic
    rw [schweizerWolff_eq_iterated] at hM h1
    have hint : (∫ v : I, ((∫ u : I, |(comonotonic 2).cdf ![u, v] - (u : ℝ) * v|) -
        ∫ u : I, |C.cdf ![u, v] - (u : ℝ) * v|)) = 0 := by
      rw [integral_sub hT hS]
      linarith
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun v => sub_nonneg.mpr (C.integral_abs_cdf_sub_mul_le_comonotonic v)) (hT.sub hS)).mp hint
    filter_upwards [hae] with v hv
    have hv' : (∫ u : I, |C.cdf ![u, v] - (u : ℝ) * v|) =
        ∫ u : I, |(comonotonic 2).cdf ![u, v] - (u : ℝ) * v| := by
      simp only [Pi.zero_apply] at hv
      linarith
    exact section_eq_of_integral_comp_eq (φ := fun t => |t|) continuous_abs
      (fun s t hs hst => by rw [abs_of_nonneg hs, abs_of_nonneg (hs.trans hst)]; exact hst)
      (fun s t hs ht hst => by rwa [abs_of_nonneg hs, abs_of_nonneg ht] at hst)
      (fun t => abs_neg t) C v (C.section_sign_of_integral_abs_eq v hv') hv'
  · rintro (rfl | rfl)
    · exact schweizerWolff_comonotonic
    · exact schweizerWolff_countermonotonic

/-! ## Hoeffding's `Φ²` -/

/-- Sectionwise, the `L²` deviation of `C` from `Π` is dominated by that of `M`. -/
theorem integral_sq_cdf_sub_mul_le_comonotonic (C : Copula 2) (v : I) :
    (∫ u : I, (C.cdf ![u, v] - (u : ℝ) * v) ^ 2) ≤
      ∫ u : I, ((comonotonic 2).cdf ![u, v] - (u : ℝ) * v) ^ 2 := by
  refine (C.integral_sq_cdf_sub_mul_le_upRearr v).trans (integral_mono
    (integrable_of_continuous_unit (((upRearr C).continuous_cdf_sub_mul_section v).pow 2))
    (integrable_of_continuous_unit (((comonotonic 2).continuous_cdf_sub_mul_section v).pow 2))
    fun u => ?_)
  have h0 := sub_nonneg.mpr (C.mul_le_upRearr_cdf u v)
  have h1 := (upRearr C).cdf_sub_mul_le_comonotonic u v
  exact pow_le_pow_left₀ h0 h1 2

/-- Hoeffding's `Φ²` is dominated by that of the SI rearrangement. -/
theorem hoeffdingPhiSq_le_hoeffdingPhiSq_upRearr (C : Copula 2) :
    C.hoeffdingPhiSq ≤ (upRearr C).hoeffdingPhiSq := by
  rw [hoeffdingPhiSq_eq_iterated, hoeffdingPhiSq_eq_iterated]
  have h := integral_mono
    (integrable_integral_of_continuous (f := fun u v : I => (C.cdf ![u, v] - (u : ℝ) * v) ^ 2)
      (C.continuous_cdf_sub_mul_pair.pow 2))
    (integrable_integral_of_continuous
      (f := fun u v : I => ((upRearr C).cdf ![u, v] - (u : ℝ) * v) ^ 2)
      ((upRearr C).continuous_cdf_sub_mul_pair.pow 2))
    (C.integral_sq_cdf_sub_mul_le_upRearr)
  linarith

/-- Hoeffding's `Φ²` is at most one (Nelsen §5.3.1). -/
theorem hoeffdingPhiSq_le_one (C : Copula 2) : C.hoeffdingPhiSq ≤ 1 := by
  have hM := hoeffdingPhiSq_comonotonic
  rw [hoeffdingPhiSq_eq_iterated] at hM ⊢
  have h := integral_mono
    (integrable_integral_of_continuous (f := fun u v : I => (C.cdf ![u, v] - (u : ℝ) * v) ^ 2)
      (C.continuous_cdf_sub_mul_pair.pow 2))
    (integrable_integral_of_continuous
      (f := fun u v : I => ((comonotonic 2).cdf ![u, v] - (u : ℝ) * v) ^ 2)
      ((comonotonic 2).continuous_cdf_sub_mul_pair.pow 2))
    (C.integral_sq_cdf_sub_mul_le_comonotonic)
  linarith

theorem hoeffdingPhiSq_mem_Icc (C : Copula 2) : C.hoeffdingPhiSq ∈ Icc (0 : ℝ) 1 :=
  ⟨C.hoeffdingPhiSq_nonneg, C.hoeffdingPhiSq_le_one⟩

/-- A section with the maximal `L²` deviation has constant sign. -/
theorem section_sign_of_integral_sq_eq (C : Copula 2) (v : I)
    (h : (∫ u : I, (C.cdf ![u, v] - (u : ℝ) * v) ^ 2) =
      ∫ u : I, ((comonotonic 2).cdf ![u, v] - (u : ℝ) * v) ^ 2) :
    (∀ u : I, 0 ≤ C.cdf ![u, v] - (u : ℝ) * v) ∨ (∀ u : I, C.cdf ![u, v] - (u : ℝ) * v ≤ 0) := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨t₂, ht₂⟩, ⟨t₁, ht₁⟩⟩ := hc
  have hlt := C.integral_sq_cdf_sub_mul_lt_upRearr v ht₁ ht₂
  have hle : (∫ u : I, ((upRearr C).cdf ![u, v] - (u : ℝ) * v) ^ 2) ≤
      ∫ u : I, ((comonotonic 2).cdf ![u, v] - (u : ℝ) * v) ^ 2 :=
    integral_mono
      (integrable_of_continuous_unit (((upRearr C).continuous_cdf_sub_mul_section v).pow 2))
      (integrable_of_continuous_unit (((comonotonic 2).continuous_cdf_sub_mul_section v).pow 2))
      fun u => pow_le_pow_left₀ (sub_nonneg.mpr (C.mul_le_upRearr_cdf u v))
        ((upRearr C).cdf_sub_mul_le_comonotonic u v) 2
  linarith

/-- `Φ²(C) = 1` if and only if `C` is one of the Fréchet–Hoeffding bounds (Nelsen §5.3.1). -/
theorem hoeffdingPhiSq_eq_one_iff (C : Copula 2) :
    C.hoeffdingPhiSq = 1 ↔ C = comonotonic 2 ∨ C = countermonotonic := by
  constructor
  · intro h1
    apply eq_comonotonic_or_countermonotonic_of_ae_section
    have hS := integrable_integral_of_continuous
      (f := fun u v : I => (C.cdf ![u, v] - (u : ℝ) * v) ^ 2) (C.continuous_cdf_sub_mul_pair.pow 2)
    have hT := integrable_integral_of_continuous
      (f := fun u v : I => ((comonotonic 2).cdf ![u, v] - (u : ℝ) * v) ^ 2)
      ((comonotonic 2).continuous_cdf_sub_mul_pair.pow 2)
    have hM := hoeffdingPhiSq_comonotonic
    rw [hoeffdingPhiSq_eq_iterated] at hM h1
    have hint : (∫ v : I, ((∫ u : I, ((comonotonic 2).cdf ![u, v] - (u : ℝ) * v) ^ 2) -
        ∫ u : I, (C.cdf ![u, v] - (u : ℝ) * v) ^ 2)) = 0 := by
      rw [integral_sub hT hS]
      linarith
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun v => sub_nonneg.mpr (C.integral_sq_cdf_sub_mul_le_comonotonic v)) (hT.sub hS)).mp hint
    filter_upwards [hae] with v hv
    have hv' : (∫ u : I, (C.cdf ![u, v] - (u : ℝ) * v) ^ 2) =
        ∫ u : I, ((comonotonic 2).cdf ![u, v] - (u : ℝ) * v) ^ 2 := by
      simp only [Pi.zero_apply] at hv
      linarith
    exact section_eq_of_integral_comp_eq (φ := fun t => t ^ 2) (continuous_pow 2)
      (fun s t hs hst => pow_le_pow_left₀ hs hst 2)
      (fun s t hs ht hst => le_antisymm (by nlinarith) (by nlinarith))
      (fun t => neg_sq t) C v (C.section_sign_of_integral_sq_eq v hv') hv'
  · rintro (rfl | rfl)
    · exact hoeffdingPhiSq_comonotonic
    · exact hoeffdingPhiSq_countermonotonic

/-! ## The uniform distance `κ` -/

/-- The only point where `|C(u,v) - uv|` can reach `1/4` is the centre `(1/2, 1/2)`. -/
theorem eq_half_of_four_mul_abs_cdf_sub_mul_eq_one (C : Copula 2) {u v : I}
    (h : 4 * |C.cdf ![u, v] - (u : ℝ) * v| = 1) : (u : ℝ) = 1 / 2 ∧ (v : ℝ) = 1 / 2 := by
  have hM := C.cdf_le_comonotonic ![u, v]
  have hW := C.cdf_countermonotonic_le ![u, v]
  rw [cdf_comonotonic_two] at hM
  rw [cdf_countermonotonic] at hW
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hM hW
  have hu0 := u.property.1
  have hu1 := u.property.2
  have hv0 := v.property.1
  have hv1 := v.property.2
  have hMu := hM.trans (min_le_left _ _)
  have hMv := hM.trans (min_le_right _ _)
  have hW0 := (le_max_left _ _).trans hW
  have hW1 := (le_max_right _ _).trans hW
  rcases abs_cases (C.cdf ![u, v] - (u : ℝ) * v) with ⟨habs, _⟩ | ⟨habs, _⟩ <;> rw [habs] at h
  · -- `C(u,v) = uv + 1/4 ≤ min(u, v)`
    have e1 : (u : ℝ) * (1 - v) ≥ 1 / 4 := by linarith
    have e2 : (v : ℝ) * (1 - u) ≥ 1 / 4 := by linarith
    have hu : (u : ℝ) = 1 / 2 := by
      nlinarith [sq_nonneg ((u : ℝ) - 1 / 2), sq_nonneg ((v : ℝ) - 1 / 2),
        sq_nonneg ((u : ℝ) - v), mul_nonneg hu0 hv0, mul_nonneg (sub_nonneg.mpr hu1)
        (sub_nonneg.mpr hv1)]
    refine ⟨hu, ?_⟩
    rw [hu] at e1 e2
    linarith
  · -- `C(u,v) = uv - 1/4 ≥ max(0, u + v - 1)`
    have e1 : (u : ℝ) * v ≥ 1 / 4 := by linarith
    have e2 : (1 - (u : ℝ)) * (1 - v) ≥ 1 / 4 := by linarith
    have hs : (u : ℝ) + v = 1 := by
      nlinarith [sq_nonneg ((u : ℝ) - v), mul_nonneg hu0 hv0,
        mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hv1)]
    have hu : (u : ℝ) = 1 / 2 := by
      have hv : (v : ℝ) = 1 - u := by linarith
      rw [hv] at e1
      nlinarith [sq_nonneg ((u : ℝ) - 1 / 2)]
    exact ⟨hu, by linarith⟩

/-- `κ(C) = 1` if and only if `|β(C)| = 1`, where `β` is Blomqvist's beta. -/
theorem schweizerWolffKappa_eq_one_iff (C : Copula 2) :
    C.schweizerWolffKappa = 1 ↔ |C.blomqvistBeta| = 1 := by
  constructor
  · intro h
    obtain ⟨u, v, huv⟩ := C.exists_schweizerWolffKappa_eq
    rw [h] at huv
    obtain ⟨hu, hv⟩ := C.eq_half_of_four_mul_abs_cdf_sub_mul_eq_one huv
    have hu' : u = unitHalf := Subtype.ext hu
    have hv' : v = unitHalf := Subtype.ext hv
    rw [hu', hv'] at huv
    have hh : ((unitHalf : I) : ℝ) = 1 / 2 := rfl
    rw [hh] at huv
    unfold blomqvistBeta
    rw [show 4 * C.cdf ![unitHalf, unitHalf] - 1 =
      4 * (C.cdf ![unitHalf, unitHalf] - 1 / 2 * (1 / 2)) by ring, abs_mul]
    norm_num at huv ⊢
    linarith
  · intro h
    exact le_antisymm C.schweizerWolffKappa_le_one
      (h ▸ C.abs_blomqvistBeta_le_schweizerWolffKappa)

@[simp] theorem schweizerWolffKappa_comonotonic : (comonotonic 2).schweizerWolffKappa = 1 :=
  (schweizerWolffKappa_eq_one_iff _).mpr (by simp)

@[simp] theorem schweizerWolffKappa_countermonotonic : countermonotonic.schweizerWolffKappa = 1 :=
  (schweizerWolffKappa_eq_one_iff _).mpr (by simp)

end ProbabilityTheory.Copula
