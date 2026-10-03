/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.MarkovProduct.Algebra
import Copula.Rank.Chatterjee

/-! # Invertible copulas and complete dependence

The characterization of the invertible elements of the Markov product (Darsow, Nguyen and Olsen,
*Copulas and Markov processes*, Illinois J. Math. 36 (1992); Durante and Sempi 2016, §5.2):
a bivariate copula has a left inverse if and only if it is completely
dependent, i.e. `V = f(U)` almost surely for a measurable `f`, and then `Cᵀ` is a left inverse.

The new ingredient is the converse of `IsCompletelyDependent.chatterjeeXi_eq_one`
(`isCompletelyDependent_of_chatterjeeXi_eq_one`): if `ξ(C) = 1`, then the conditional
distribution functions take only the values `0` and `1` almost everywhere
(`∫∫ h(1-h) = 1/2 - ∫∫ h² = 0`), hence almost every conditional law is a Dirac mass
(`eq_dirac_of_ae_cdf`), located at the conditional mean `f(u) = ∫₀¹ (1 - h(u,t)) dt`, a measurable
function of `u`. Consequently:

* `C.IsCompletelyDependent ↔ ξ(C) = 1 ↔ Cᵀ * C = M ↔ ∃ A, A * C = M`;
* `Cᵀ.IsCompletelyDependent ↔ ∃ B, C * B = M`;
* `C` is mutually completely dependent if and only if it is invertible, with inverse `Cᵀ`;
* `M` is the only idempotent copula with a left inverse (in particular the only completely
  dependent idempotent).
-/

open MeasureTheory Set Filter
open scoped unitInterval ProbabilityTheory

namespace ProbabilityTheory.Copula

/-! ## Probability measures with two-valued distribution functions -/

/-- A probability measure on `[0,1]` whose distribution function takes only the values `0` and
`1` (almost everywhere) is the Dirac mass at its mean `∫₀¹ (1 - F)`. -/
theorem eq_dirac_of_ae_cdf {ν : Measure I} [IsProbabilityMeasure ν]
    (h : ∀ᵐ t : I, ν.real (Iic t) * (1 - ν.real (Iic t)) = 0) :
    ν = Measure.dirac (projIcc 0 1 zero_le_one (∫ t : I, (1 - ν.real (Iic t)))) := by
  set F : I → ℝ := fun t => ν.real (Iic t) with hFdef
  have hF0 : ∀ t, 0 ≤ F t := fun t => measureReal_nonneg
  have hF1 : ∀ t, F t ≤ 1 := fun t => measureReal_le_one
  have hFm : Monotone F := fun s t hst => measureReal_mono (Iic_subset_Iic.mpr hst)
  have hmeas : Measurable F := by
    have : Monotone F := hFm
    exact this.measurable
  have hint : Integrable (fun t : I => 1 - F t) := by
    refine (integrable_const (1 : ℝ)).mono' (measurable_const.sub hmeas).aestronglyMeasurable ?_
    exact Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hF1 t])]; linarith [hF0 t]
  set c := ∫ t : I, (1 - F t) with hc
  have hc0 : 0 ≤ c := integral_nonneg fun t => sub_nonneg.mpr (hF1 t)
  have hc1 : c ≤ 1 := by
    have := integral_mono hint (integrable_const (1 : ℝ)) (fun t => by linarith [hF0 t])
    simpa using this
  have hvol : ∀ t : I, (volume : Measure I).real (Iic t) = t := fun t => by
    simp [Measure.real, unitInterval.volume_Iic, t.2.1]
  -- above the mean the distribution function is one
  have hup : ∀ t : I, c < t → F t = 1 := by
    intro t hct
    by_contra hne
    have hlt : F t < 1 := lt_of_le_of_ne (hF1 t) hne
    have hae : ∀ᵐ s : I, s ∈ Iic t → 1 - F s = 1 := by
      filter_upwards [h] with s hs hst
      have : F s < 1 := (hFm hst).trans_lt hlt
      have hF : F s = 0 := by
        rcases mul_eq_zero.mp hs with h0 | h0
        · exact h0
        · exact absurd (by linarith : F s = 1) this.ne
      rw [hF]; ring
    have h1 : (∫ s in Iic t, (1 - F s)) = t := by
      rw [setIntegral_congr_ae measurableSet_Iic hae, setIntegral_const, hvol, smul_eq_mul,
        mul_one]
    have h2 : (∫ s in Iic t, (1 - F s)) ≤ c :=
      setIntegral_le_integral hint (Eventually.of_forall fun s => sub_nonneg.mpr (hF1 s))
    linarith
  -- below the mean the distribution function is zero
  have hdown : ∀ t : I, (t : ℝ) < c → F t = 0 := by
    intro t htc
    by_contra hne
    have hpos : 0 < F t := lt_of_le_of_ne (hF0 t) (Ne.symm hne)
    have hae : ∀ᵐ s : I, s ∈ Ioi t → 1 - F s = 0 := by
      filter_upwards [h] with s hs hst
      have : 0 < F s := hpos.trans_le (hFm (le_of_lt hst))
      rcases mul_eq_zero.mp hs with h0 | h0
      · exact absurd h0 this.ne'
      · exact h0
    have hsplit := integral_add_compl (μ := (volume : Measure I)) measurableSet_Iic hint (s := Iic t)
    rw [compl_Iic, setIntegral_congr_ae measurableSet_Ioi hae, integral_zero, add_zero] at hsplit
    have hle : (∫ s in Iic t, (1 - F s)) ≤ ∫ s in Iic t, (1 : ℝ) :=
      setIntegral_mono hint.integrableOn (integrable_const _).integrableOn
        (fun s => by linarith [hF0 s])
    rw [setIntegral_const, hvol, smul_eq_mul, mul_one] at hle
    linarith
  set c' : I := projIcc 0 1 zero_le_one c with hc'def
  have hc' : (c' : ℝ) = c := by rw [hc'def, projIcc_of_mem _ ⟨hc0, hc1⟩]
  -- no mass above the mean
  have hIoi : ν (Ioi c') = 0 := by
    set T : ℕ → I := fun n => projIcc 0 1 zero_le_one (c + 1 / ((n : ℝ) + 1)) with hT
    have hTn : ∀ n, ν (Ioi (T n)) = 0 := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      by_cases hcT : c < T n
      · have h1 := hup (T n) hcT
        have hcompl := prob_compl_eq_one_sub (μ := ν) (measurableSet_Iic (a := T n))
        rw [compl_Iic] at hcompl
        rw [hcompl]
        have : ν (Iic (T n)) = 1 := by
          have h1' : ν.real (Iic (T n)) = 1 := h1
          rw [measureReal_def] at h1'
          rw [← ENNReal.ofReal_toReal (measure_ne_top ν (Iic (T n))), h1', ENNReal.ofReal_one]
        rw [this, tsub_self]
      · push Not at hcT
        have hT1 : T n = 1 := by
          apply Subtype.ext
          have hcoe : (T n : ℝ) = max 0 (min 1 (c + 1 / ((n : ℝ) + 1))) := rfl
          rw [hcoe] at hcT ⊢
          rcases le_total 1 (c + 1 / ((n : ℝ) + 1)) with h1 | h1
          · rw [min_eq_left h1, max_eq_right zero_le_one]; rfl
          · rw [min_eq_right h1, max_eq_right (by linarith)] at hcT; linarith
        rw [hT1]
        have : Ioi (1 : I) = ∅ := Set.eq_empty_of_forall_notMem fun x hx => not_le.mpr hx x.2.2
        rw [this, measure_empty]
    apply measure_mono_null _ (measure_iUnion_null hTn)
    intro x hx
    have hx' : c < (x : ℝ) := by rw [← hc']; exact hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx')
    refine mem_iUnion.mpr ⟨n, ?_⟩
    change T n < x
    show (T n : ℝ) < x
    have hle1 : c + 1 / ((n : ℝ) + 1) ≤ 1 := by linarith [x.2.2]
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hcoe : (T n : ℝ) = c + 1 / ((n : ℝ) + 1) := by
      show ((projIcc 0 1 zero_le_one (c + 1 / ((n : ℝ) + 1)) : I) : ℝ) = _
      rw [projIcc_of_mem _ ⟨by linarith, hle1⟩]
    rw [hcoe]; linarith
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.dirac_apply' _ measurableSet_Iic]
  by_cases hct : c' ≤ t
  · rw [indicator_of_mem (show c' ∈ Iic t from hct)]
    have hcompl := prob_compl_eq_one_sub (μ := ν) (measurableSet_Ioi (a := t))
    rw [compl_Ioi] at hcompl
    rw [hcompl, measure_mono_null (Ioi_subset_Ioi hct) hIoi, tsub_zero]
    rfl
  · rw [indicator_of_notMem (show c' ∉ Iic t from hct)]
    have htc : (t : ℝ) < c := by rw [← hc']; exact not_le.mp hct
    have h0 : ν.real (Iic t) = 0 := hdown t htc
    exact (measureReal_eq_zero_iff).mp h0

/-! ## `ξ = 1` forces complete dependence -/

/-- If `ξ(C) = 1`, then for almost every `u` the conditional distribution function
`t ↦ h(u,t)` takes only the values `0` and `1` (almost everywhere). -/
theorem ae_ae_conditionalCDF_mul_one_sub_eq_zero {C : Copula 2} (h : C.chatterjeeXi = 1) :
    ∀ᵐ u : I, ∀ᵐ t : I, C.conditionalCDF u t * (1 - C.conditionalCDF u t) = 0 := by
  set Φ : I × I → ℝ := fun p => C.conditionalCDF p.2 p.1 * (1 - C.conditionalCDF p.2 p.1)
    with hΦ
  have hm : Measurable Φ :=
    C.measurable_conditionalCDF.mul (measurable_const.sub C.measurable_conditionalCDF)
  have hΦ0 : ∀ p, 0 ≤ Φ p := fun p =>
    mul_nonneg (C.conditionalCDF_nonneg _ _) (sub_nonneg.mpr (C.conditionalCDF_le_one _ _))
  have hΦ1 : ∀ p, Φ p ≤ 1 := fun p => by
    have h0 := C.conditionalCDF_nonneg p.2 p.1
    have h1 := C.conditionalCDF_le_one p.2 p.1
    simp only [hΦ]; nlinarith
  have hint : Integrable Φ ((volume : Measure I).prod volume) := by
    refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hΦ0 p)]; exact hΦ1 p
  have hinner : ∀ t : I, (∫ u : I, Φ (t, u)) = t - ∫ u : I, C.conditionalCDF u t ^ 2 := by
    intro t
    simp only [hΦ]
    have : (fun u : I => C.conditionalCDF u t * (1 - C.conditionalCDF u t)) =
        fun u => C.conditionalCDF u t - C.conditionalCDF u t ^ 2 := by funext u; ring
    rw [this, integral_sub (C.integrable_conditionalCDF t) (C.integrable_conditionalCDF_sq t),
      C.integral_conditionalCDF]
  have hid : Integrable (fun t : I => (t : ℝ)) := by
    refine (integrable_const (1 : ℝ)).mono' measurable_subtype_coe.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg t.2.1]; exact t.2.2
  have ht : (∫ t : I, (t : ℝ)) = 1 / 2 := by
    rw [integral_unitInterval (fun x => x), integral_id]; norm_num
  have hzero : (∫ p, Φ p ∂((volume : Measure I).prod volume)) = 0 := by
    rw [integral_prod Φ hint]
    simp_rw [hinner]
    rw [integral_sub hid C.integrable_integral_conditionalCDF_sq, ht]
    have hxi := h
    unfold chatterjeeXi at hxi
    linarith
  have hae : ∀ᵐ p ∂((volume : Measure I).prod volume), Φ p = 0 :=
    (integral_eq_zero_iff_of_nonneg hΦ0 hint).mp hzero
  have h2 := Measure.ae_ae_of_ae_prod hae
  rwa [Measure.ae_ae_comm (p := fun t u => Φ (t, u) = 0)
    (measurableSet_eq_fun hm measurable_const)] at h2

/-- Converse of `IsCompletelyDependent.chatterjeeXi_eq_one`: `ξ(C) = 1` implies that `V` is
almost surely a measurable function of `U`. -/
theorem isCompletelyDependent_of_chatterjeeXi_eq_one {C : Copula 2} (h : C.chatterjeeXi = 1) :
    C.IsCompletelyDependent := by
  set f : I → I := fun u => projIcc 0 1 zero_le_one (∫ t : I, (1 - C.conditionalCDF u t))
    with hf
  have hfm : Measurable f := by
    have hm : StronglyMeasurable (fun p : I × I => 1 - C.conditionalCDF p.1 p.2) :=
      (measurable_const.sub (C.measurable_conditionalCDF.comp measurable_swap)).stronglyMeasurable
    exact continuous_projIcc.measurable.comp hm.integral_prod_right'.measurable
  have hκ : C.conditionalKernel =ᵐ[volume] Kernel.deterministic f hfm := by
    filter_upwards [ae_ae_conditionalCDF_mul_one_sub_eq_zero h] with u hu
    rw [Kernel.deterministic_apply]
    exact eq_dirac_of_ae_cdf hu
  have hmp : MeasurePreserving f volume volume := by
    refine ⟨hfm, ?_⟩
    rw [← Measure.deterministic_comp_eq_map hfm, ← Measure.bind_congr_right hκ]
    exact C.conditionalKernel_comp_volume
  have hC : C = graphCopula f hmp :=
    eq_of_conditionalKernel_ae_eq (hκ.trans (conditionalKernel_graphCopula f hmp).symm)
  rw [hC]
  exact isCompletelyDependent_graphCopula f hmp

/-- A copula is completely dependent if and only if Chatterjee's xi equals one. -/
theorem isCompletelyDependent_iff_chatterjeeXi_eq_one (C : Copula 2) :
    C.IsCompletelyDependent ↔ C.chatterjeeXi = 1 :=
  ⟨IsCompletelyDependent.chatterjeeXi_eq_one, isCompletelyDependent_of_chatterjeeXi_eq_one⟩

/-! ## Invertibility -/

/-- `C` is completely dependent if and only if `Cᵀ * C = M`. -/
theorem isCompletelyDependent_iff_transpose_markovProduct_self (C : Copula 2) :
    C.IsCompletelyDependent ↔ C.transpose.markovProduct C = comonotonic 2 := by
  rw [isCompletelyDependent_iff_chatterjeeXi_eq_one,
    transpose_markovProduct_self_eq_comonotonic_iff]

/-- Darsow–Nguyen–Olsen: a copula has a left inverse for the Markov product if and only if it
is completely dependent (`V = f(U)` almost surely). -/
theorem exists_left_inverse_iff_isCompletelyDependent (C : Copula 2) :
    (∃ A : Copula 2, A.markovProduct C = comonotonic 2) ↔ C.IsCompletelyDependent := by
  rw [exists_left_inverse_iff, isCompletelyDependent_iff_chatterjeeXi_eq_one]

/-- A copula has a right inverse if and only if its transpose is completely dependent
(`U = g(V)` almost surely). -/
theorem exists_right_inverse_iff_isCompletelyDependent (C : Copula 2) :
    (∃ B : Copula 2, C.markovProduct B = comonotonic 2) ↔ C.transpose.IsCompletelyDependent := by
  rw [exists_right_inverse_iff, isCompletelyDependent_iff_chatterjeeXi_eq_one]

/-- A copula is invertible (`Cᵀ * C = C * Cᵀ = M`) if and only if it is mutually completely
dependent. -/
theorem isMutuallyCompletelyDependent_iff (C : Copula 2) :
    C.IsMutuallyCompletelyDependent ↔
      C.transpose.markovProduct C = comonotonic 2 ∧
        C.markovProduct C.transpose = comonotonic 2 := by
  rw [IsMutuallyCompletelyDependent, isCompletelyDependent_iff_transpose_markovProduct_self,
    isCompletelyDependent_iff_transpose_markovProduct_self, transpose_transpose]

/-- An idempotent copula with a left inverse is `M`. -/
theorem IsIdempotent.eq_comonotonic_of_left_inverse {A C : Copula 2} (hC : C.IsIdempotent)
    (hA : A.markovProduct C = comonotonic 2) : C = comonotonic 2 := by
  calc C = (A.markovProduct C).markovProduct C := by rw [hA, comonotonic_markovProduct]
    _ = A.markovProduct (C.markovProduct C) := markovProduct_assoc _ _ _
    _ = comonotonic 2 := by rw [hC, hA]

/-- The only completely dependent idempotent copula is `M`. -/
theorem IsIdempotent.eq_comonotonic_of_isCompletelyDependent {C : Copula 2}
    (hC : C.IsIdempotent) (hd : C.IsCompletelyDependent) : C = comonotonic 2 := by
  obtain ⟨A, hA⟩ := (exists_left_inverse_iff_isCompletelyDependent C).mpr hd
  exact hC.eq_comonotonic_of_left_inverse hA

end ProbabilityTheory.Copula
