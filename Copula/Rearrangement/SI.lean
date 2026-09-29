/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rearrangement.Decreasing
import Copula.Rank.ConditionalCDF
import Copula.Classical.Bivariate
import Copula.Order.Schur
import Copula.Order.Orthant
import Copula.Dependence.Basic
import Copula.Reflection.Bivariate

/-! # The SI rearrangement of a copula

For a bivariate copula `C`, the *SI rearrangement* of Strothmann, Dette and Siburg
(*Rearranged dependence measures*, Bernoulli, 2024) is
`C↑(u,v) = ∫_0^u (∂₁C(·,v))↓(t) dt`: the conditional distribution functions `u ↦ P(V ≤ v | U = u)`
are rearranged decreasingly in the conditioning variable.

This file constructs `upRearr C = C↑` and proves:
`C↑` is a copula, it is stochastically increasing (hence `Π ≤ C↑`), `C ≤ C↑`, its conditional
CDFs are the decreasing rearrangements of those of `C`, it is Schur equivalent to `C`, and
`ξ(C↑) = ξ(C)`. Sectionwise norm inequalities follow from the primitive comparison lemma in
`Copula.Rearrangement.PrimitiveIntegral`; see `Copula.Measures.Bounds`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The conditional section `u ↦ P(V ≤ v | U = u)`. -/
noncomputable def condSection (C : Copula 2) (v : I) : I → ℝ := fun u => C.conditionalCDF u v

theorem condSection_nonneg (C : Copula 2) (v : I) (u : I) : 0 ≤ condSection C v u :=
  C.conditionalCDF_nonneg u v

theorem condSection_le_one (C : Copula 2) (v : I) (u : I) : condSection C v u ≤ 1 :=
  C.conditionalCDF_le_one u v

theorem condSection_measurable (C : Copula 2) (v : I) : Measurable (condSection C v) :=
  C.measurable_conditionalCDF_left v

theorem condSection_mono (C : Copula 2) {v w : I} (h : v ≤ w) (u : I) :
    condSection C v u ≤ condSection C w u :=
  measureReal_mono (Iic_subset_Iic.mpr h)

theorem integral_condSection (C : Copula 2) (v : I) : (∫ u, condSection C v u) = (v : ℝ) :=
  C.integral_conditionalCDF v

theorem cdf_eq_integral_condSection (C : Copula 2) (u v : I) :
    C.cdf ![u, v] = ∫ t in Iic u, condSection C v t :=
  C.cdf_eq_integral_conditionalCDF u v

theorem condSection_one (C : Copula 2) (u : I) : condSection C 1 u = 1 := by
  unfold condSection Copula.conditionalCDF
  rw [show Iic (1 : I) = univ from Iic_top]
  simp

theorem condSection_zero_ae (C : Copula 2) : condSection C 0 =ᵐ[volume] fun _ => (0 : ℝ) := by
  apply C.conditionalCDF_ae_eq_of_integral 0 (integrable_const 0) (fun _ => le_rfl)
  intro u
  simp only [integral_zero]
  exact (C.cdf_eq_zero_of_coord_eq_zero _ 1 rfl).symm

/-- The SI rearranged copula, as a CDF. -/
noncomputable def upRearrCDF (C : Copula 2) (u v : I) : ℝ :=
  ∫ s in Iic u, decRearr (condSection C v) s

theorem decRearr_condSection_nonneg (C : Copula 2) (v s : I) :
    0 ≤ decRearr (condSection C v) s :=
  decRearr_nonneg (condSection_le_one C v) s.property.1

theorem decRearr_condSection_le_one (C : Copula 2) (v s : I) :
    decRearr (condSection C v) s ≤ 1 :=
  decRearr_le_one (condSection_le_one C v) s.property.1

theorem integrable_decRearr_condSection (C : Copula 2) (v : I) :
    Integrable (fun s : I => decRearr (condSection C v) s) :=
  integrable_decRearr (condSection_le_one C v)

theorem upRearrCDF_zero_left (C : Copula 2) (v : I) : upRearrCDF C 0 v = 0 := by
  unfold upRearrCDF
  apply setIntegral_measure_zero
  rw [unitInterval.volume_Iic]
  simp

theorem upRearrCDF_zero_right (C : Copula 2) (u : I) : upRearrCDF C u 0 = 0 := by
  unfold upRearrCDF
  rw [decRearr_congr (condSection_zero_ae C)]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro s _
  exact decRearr_const_zero s.property.1

theorem upRearrCDF_one_left (C : Copula 2) (v : I) : upRearrCDF C 1 v = (v : ℝ) := by
  unfold upRearrCDF
  rw [show Iic (1 : I) = univ from Iic_top, Measure.restrict_univ]
  have h := integral_comp_decRearr (condSection_nonneg C v) (condSection_le_one C v)
    (condSection_measurable C v) (φ := id) measurable_id
  simp only [id] at h
  rw [h]
  exact C.integral_conditionalCDF v

theorem upRearrCDF_one_right (C : Copula 2) (u : I) : upRearrCDF C u 1 = (u : ℝ) := by
  unfold upRearrCDF
  have he : condSection C 1 = fun _ => (1 : ℝ) := funext (condSection_one C)
  rw [he]
  have hae : ∀ᵐ s : I, s ≠ 1 := by simp [ae_iff]
  rw [setIntegral_congr_ae measurableSet_Iic (g := fun _ => (1 : ℝ)) (by
    filter_upwards [hae] with s hs _
    exact decRearr_const_one s.property.1
      (lt_of_le_of_ne s.property.2 (fun e => hs (Subtype.ext e))))]
  simp [measureReal_def, unitInterval.volume_Iic, ENNReal.toReal_ofReal u.property.1]

theorem decRearr_condSection_mono (C : Copula 2) {v w : I} (h : v ≤ w) (s : I) :
    decRearr (condSection C v) s ≤ decRearr (condSection C w) s :=
  decRearr_mono (condSection_le_one C w) (Eventually.of_forall (condSection_mono C h))
    s.property.1

theorem upRearrCDF_rectangle (C : Copula 2) (a b c d : I) (hab : a ≤ b) (hcd : c ≤ d) :
    0 ≤ upRearrCDF C b d - upRearrCDF C a d - upRearrCDF C b c + upRearrCDF C a c := by
  unfold upRearrCDF
  set h : I → ℝ := fun s => decRearr (condSection C d) s - decRearr (condSection C c) s
  have hi : Integrable h :=
    (integrable_decRearr_condSection C d).sub (integrable_decRearr_condSection C c)
  have hn : ∀ s, 0 ≤ h s := fun s => sub_nonneg.mpr (decRearr_condSection_mono C hcd s)
  have hb : (∫ s in Iic b, h s) = (∫ s in Iic b, decRearr (condSection C d) s) -
      ∫ s in Iic b, decRearr (condSection C c) s :=
    integral_sub (integrable_decRearr_condSection C d).integrableOn
      (integrable_decRearr_condSection C c).integrableOn
  have ha : (∫ s in Iic a, h s) = (∫ s in Iic a, decRearr (condSection C d) s) -
      ∫ s in Iic a, decRearr (condSection C c) s :=
    integral_sub (integrable_decRearr_condSection C d).integrableOn
      (integrable_decRearr_condSection C c).integrableOn
  have hm : (∫ s in Iic a, h s) ≤ ∫ s in Iic b, h s :=
    setIntegral_mono_set hi.integrableOn (Eventually.of_forall hn)
      (Eventually.of_forall (Iic_subset_Iic.mpr hab))
  linarith

theorem upRearrCDF_isClassical (C : Copula 2) :
    IsClassical (fun u : Fin 2 → I => upRearrCDF C (u 0) (u 1)) :=
  IsClassical.ofBivariate _ (upRearrCDF_zero_left C) (upRearrCDF_zero_right C)
    (upRearrCDF_one_left C) (upRearrCDF_one_right C) (upRearrCDF_rectangle C)

/-- The SI rearrangement `C↑` of a copula. -/
noncomputable def upRearr (C : Copula 2) : Copula 2 := ofClassical _ (upRearrCDF_isClassical C)

theorem upRearr_cdf (C : Copula 2) (u v : I) : (upRearr C).cdf ![u, v] = upRearrCDF C u v := by
  rw [upRearr, cdf_ofClassical]
  rfl

theorem upRearr_cdf_eq_integral (C : Copula 2) (u v : I) :
    (upRearr C).cdf ![u, v] = ∫ s in Iic u, decRearr (condSection C v) s :=
  upRearr_cdf C u v

/-- The conditional distribution functions of `C↑` are the decreasing rearrangements of those
of `C`. -/
theorem upRearr_conditionalCDF (C : Copula 2) (v : I) :
    (fun u => (upRearr C).conditionalCDF u v) =ᵐ[volume]
      fun u => decRearr (condSection C v) u :=
  (upRearr C).conditionalCDF_ae_eq_of_integral v (integrable_decRearr_condSection C v)
    (decRearr_condSection_nonneg C v) (fun u => (upRearr_cdf C u v).symm)

/-- `C↑` is stochastically increasing. -/
theorem upRearr_isSI (C : Copula 2) : (upRearr C).IsSI := by
  intro a b c v hab hbc
  simp only [upRearr_cdf]
  unfold upRearrCDF
  set f := fun s : I => decRearr (condSection C v) s
  have hfi : Integrable f := integrable_decRearr_condSection C v
  have hanti : ∀ s t : I, s ≤ t → f t ≤ f s := fun s t hst =>
    decRearr_antitoneOn (condSection_le_one C v) s.property.1 t.property.1 hst
  have hdiff (x y : I) (hxy : x ≤ y) :
      (∫ s in Iic y, f s) - (∫ s in Iic x, f s) = ∫ s in Ioc x y, f s := by
    rw [← Iic_sdiff_Iic, setIntegral_sdiff measurableSet_Iic hfi.integrableOn
      (Iic_subset_Iic.mpr hxy)]
  have hlen (x y : I) (hxy : x ≤ y) : volume.real (Ioc x y) = (y : ℝ) - x := by
    rw [measureReal_def, unitInterval.volume_Ioc]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr hxy)
  have h1 : ((b : ℝ) - a) * f b ≤ ∫ s in Ioc a b, f s := by
    have := setIntegral_ge_of_const_le_real (μ := volume) (s := Ioc a b) (f := f)
      measurableSet_Ioc (by rw [unitInterval.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      (fun s hs => hanti s b hs.2) hfi.integrableOn
    rwa [hlen a b hab, mul_comm] at this
  have h2 : (∫ s in Ioc b c, f s) ≤ ((c : ℝ) - b) * f b := by
    have := setIntegral_mono_on (μ := volume) (s := Ioc b c) hfi.integrableOn
      (integrableOn_const (C := f b)
        (by rw [unitInterval.volume_Ioc]; exact ENNReal.ofReal_ne_top))
      measurableSet_Ioc (fun s hs => hanti b s (le_of_lt hs.1))
    rwa [setIntegral_const, smul_eq_mul, hlen b c hbc] at this
  have e1 := hdiff a b hab
  have e2 := hdiff b c hbc
  have hba : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr hab
  have hcb : 0 ≤ (c : ℝ) - b := sub_nonneg.mpr hbc
  nlinarith [mul_le_mul_of_nonneg_left h1 hcb, mul_le_mul_of_nonneg_left h2 hba]

/-- `C↑` is positively quadrant dependent, i.e. `Π ≤ C↑`. -/
theorem upRearr_isPQD (C : Copula 2) : (upRearr C).IsPQD := (upRearr_isSI C).isPQD

/-- `C ≤ C↑` pointwise (Hardy–Littlewood). -/
theorem cdf_le_upRearr (C : Copula 2) (u v : I) : C.cdf ![u, v] ≤ (upRearr C).cdf ![u, v] := by
  rw [upRearr_cdf, C.cdf_eq_integral_conditionalCDF]
  exact integral_Iic_le_decRearr (condSection_nonneg C v) (condSection_le_one C v)
    (condSection_measurable C v) u

theorem lowerOrthantLE_upRearr (C : Copula 2) : C.LowerOrthantLE (upRearr C) := by
  intro w
  have hw : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
  rw [hw]
  exact cdf_le_upRearr C (w 0) (w 1)

/-- `C↑` is Schur equivalent to `C`: every conditional section is equimeasurable with its
rearrangement. -/
theorem upRearr_schur_equiv (C : Copula 2) : (upRearr C).SchurLE C ∧ C.SchurLE (upRearr C) := by
  have he (v : I) (φ : ℝ → ℝ) (hφ : Continuous φ) :
      (∫ u : I, φ ((upRearr C).conditionalCDF u v)) = ∫ u : I, φ (C.conditionalCDF u v) := by
    rw [integral_congr_ae (g := fun u : I => φ (decRearr (condSection C v) (u : ℝ))) (by
      filter_upwards [upRearr_conditionalCDF C v] with u hu
      exact congrArg φ hu)]
    exact integral_comp_decRearr (condSection_nonneg C v) (condSection_le_one C v)
      (condSection_measurable C v) hφ.measurable
  exact ⟨fun v φ hc _ => (he v φ hc).le, fun v φ hc _ => (he v φ hc).ge⟩

/-- The SI rearrangement leaves Chatterjee's xi unchanged. -/
theorem chatterjeeXi_upRearr (C : Copula 2) : (upRearr C).chatterjeeXi = C.chatterjeeXi :=
  le_antisymm (upRearr_schur_equiv C).1.chatterjeeXi_le (upRearr_schur_equiv C).2.chatterjeeXi_le

end ProbabilityTheory.Copula
