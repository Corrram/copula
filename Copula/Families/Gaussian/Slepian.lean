/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Gaussian.Sheppard
import Copula.Order.Orthant
import Copula.Dependence.Basic
import Copula.OrdinalSum.Basic

/-! # Slepian's inequality and quadrant dependence of the Gaussian copula

The bivariate Gaussian copulas are increasing in the concordance (pointwise) order:
`r ≤ r'` implies `C_r ≤ C_{r'}` (Slepian's inequality in dimension two, Slepian 1962). In
particular `C_r` is positively quadrant dependent iff `r ≥ 0` and negatively quadrant dependent iff
`r ≤ 0`.

## Proof
For `r ∈ [0, 1]` the bivariate normal vector has the *common factor* representation
`(√r W + √(1−r) Z₁, √r W + √(1−r) Z₂)` with `W, Z₁, Z₂` i.i.d. standard normal, hence
`P(X ≤ x, Y ≤ y) = E[K(x − √r W) K(y − √r W)]` with `K` the `N(0, 1 − r)` CDF
(`bivariateNormal_real_Iic_eq_integral`). For `0 ≤ r ≤ r'` split `√r' W = √r W + √(r'−r) V`;
conditionally on `W` both factors are antitone in `V`, and Chebyshev's integral inequality
(`integral_mul_integral_le_integral_mul_of_antitone`) removes the common `V`, which turns `r'`
into `r`. Negative correlations follow by reflection (`reflect_second_bivariateGaussian`).

## Main results
* `bivariateGaussian_lowerOrthantLE`, `bivariateGaussian_concordanceLE`: `r ≤ r' → C_r ≤ C_{r'}`.
* `isPQD_bivariateGaussian_iff`, `isNQD_bivariateGaussian_iff`.

## References
* D. Slepian, *The one-sided barrier problem for Gaussian noise*, Bell System Tech. J. 41 (1962).
* H. Joe, *Dependence Modeling with Copulas*, CRC Press 2014, §4.3 (concordance ordering of the
  Gaussian family); R. B. Nelsen, *An Introduction to Copulas*, 2nd ed., 2006, §5.2 (PQD).
-/

open MeasureTheory Set Real
open scoped unitInterval ENNReal NNReal

namespace ProbabilityTheory.Copula

/-! ### Chebyshev's integral inequality -/

/-- **Chebyshev's integral inequality**: for two antitone functions with values in `[0, 1]`,
`∫ f · ∫ g ≤ ∫ f g` under a probability measure. -/
theorem integral_mul_integral_le_integral_mul_of_antitone (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f g : ℝ → ℝ} (hf : Antitone f) (hg : Antitone g) (hf01 : ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ ∫ x, f x * g x ∂μ := by
  have hfm := hf.measurable
  have hgm := hg.measurable
  have hint : ∀ h : ℝ × ℝ → ℝ, Measurable h → (∀ z, h z ∈ Icc (0 : ℝ) 1) →
      Integrable h (μ.prod μ) := fun h hm h01 =>
    Integrable.of_mem_Icc 0 1 hm.aemeasurable (ae_of_all _ h01)
  have hmul : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → a * b ∈ Icc (0 : ℝ) 1 :=
    fun a b ha hb => ⟨mul_nonneg ha.1 hb.1, by nlinarith [ha.1, ha.2, hb.1, hb.2]⟩
  have i11 := hint (fun z => f z.1 * g z.1) (by fun_prop) fun z => hmul _ _ (hf01 _) (hg01 _)
  have i22 := hint (fun z => f z.2 * g z.2) (by fun_prop) fun z => hmul _ _ (hf01 _) (hg01 _)
  have i12 := hint (fun z => f z.1 * g z.2) (by fun_prop) fun z => hmul _ _ (hf01 _) (hg01 _)
  have i21 := hint (fun z => g z.1 * f z.2) (by fun_prop) fun z => hmul _ _ (hg01 _) (hf01 _)
  have key : 0 ≤ ∫ z, (f z.1 - f z.2) * (g z.1 - g z.2) ∂(μ.prod μ) := by
    apply integral_nonneg
    intro z
    rcases le_total z.1 z.2 with h | h
    · exact mul_nonneg (sub_nonneg.2 (hf h)) (sub_nonneg.2 (hg h))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hf h)) (sub_nonpos.2 (hg h))
  have e : (fun z : ℝ × ℝ => (f z.1 - f z.2) * (g z.1 - g z.2)) =
      fun z => (f z.1 * g z.1 + f z.2 * g z.2) - (f z.1 * g z.2 + g z.1 * f z.2) := by
    funext z
    ring
  have i1 : Integrable (fun z : ℝ × ℝ => f z.1 * g z.1 + f z.2 * g z.2) (μ.prod μ) := i11.add i22
  have i2 : Integrable (fun z : ℝ × ℝ => f z.1 * g z.2 + g z.1 * f z.2) (μ.prod μ) := i12.add i21
  rw [e, integral_sub i1 i2, integral_add i11 i22, integral_add i12 i21,
    integral_fun_fst (f := fun x => f x * g x), integral_fun_snd (f := fun x => f x * g x),
    integral_prod_mul (f := f) (g := g), integral_prod_mul (f := g) (g := f)] at key
  simp only [probReal_univ, one_smul] at key
  linarith

/-! ### Scaled normal CDFs -/

/-- `P(e Z ≤ t)` for a standard normal `Z`; for `e ≥ 0` this is the `N(0, e²)` CDF at `t`. -/
noncomputable def scaledNormalCDF (e t : ℝ) : ℝ := (gaussianReal 0 1).real {z | e * z ≤ t}

theorem scaledNormalCDF_mono (e : ℝ) : Monotone (scaledNormalCDF e) := fun _ _ h =>
  measureReal_mono fun _ hz => le_trans hz h

theorem scaledNormalCDF_mem_Icc (e t : ℝ) : scaledNormalCDF e t ∈ Icc (0 : ℝ) 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

theorem measurable_scaledNormalCDF (e : ℝ) : Measurable (scaledNormalCDF e) :=
  (scaledNormalCDF_mono e).measurable

/-- `P(e Z ≤ t) = P(N(0, e²) ≤ t)`, written through `gaussianReal`. -/
theorem scaledNormalCDF_eq (e t : ℝ) :
    scaledNormalCDF e t = (gaussianReal 0 (e ^ 2).toNNReal).real (Iic t) := by
  have h : (gaussianReal 0 1).map (fun x => e * x) = gaussianReal 0 (e ^ 2).toNNReal := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · apply NNReal.eq
      simp [sq_nonneg]
  rw [scaledNormalCDF, ← h, map_measureReal_apply (by fun_prop) measurableSet_Iic]
  rfl

/-- Convolution of scaled normal CDFs: `E[K_e(t − d V)] = K_{√(d² + e²)}(t)`. -/
theorem integral_scaledNormalCDF_sub (d e t : ℝ) :
    ∫ v, scaledNormalCDF e (t - d * v) ∂(gaussianReal 0 1) =
      scaledNormalCDF (√(d ^ 2 + e ^ 2)) t := by
  have hS : MeasurableSet {p : ℝ × ℝ | d * p.1 + e * p.2 ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  have h1 : ∫ v, scaledNormalCDF e (t - d * v) ∂(gaussianReal 0 1) =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).real {p : ℝ × ℝ | d * p.1 + e * p.2 ≤ t} := by
    rw [← integral_measureReal_prodMk _ _ hS]
    congr 1
    funext v
    rw [scaledNormalCDF]
    congr 1
    ext z
    simp only [mem_ofPred_eq, mem_preimage]
    constructor <;> intro h <;> linarith
  rw [h1, scaledNormalCDF_eq, Real.sq_sqrt (by positivity)]
  have hpre : {p : ℝ × ℝ | d * p.1 + e * p.2 ≤ t} =
      (fun p : ℝ × ℝ => d * p.1 + e * p.2) ⁻¹' Iic t :=
    rfl
  rw [hpre, ← map_measureReal_apply (by fun_prop) measurableSet_Iic, map_linear_prod_gaussianReal]
  congr 3
  simp

/-- A Gaussian scale can be split into two independent pieces inside an integral:
`E[F(√(c² + d²) W)] = E[F(c W + d V)]` for independent standard normal `W, V`. -/
theorem integral_comp_sqrt_add_sq (F : ℝ → ℝ) (hF : Measurable F) (hF01 : ∀ s, F s ∈ Icc (0 : ℝ) 1)
    (c d : ℝ) :
    ∫ w, F (√(c ^ 2 + d ^ 2) * w) ∂(gaussianReal 0 1) =
      ∫ w, ∫ v, F (c * w + d * v) ∂(gaussianReal 0 1) ∂(gaussianReal 0 1) := by
  have hint : Integrable (fun z : ℝ × ℝ => F (c * z.1 + d * z.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    Integrable.of_mem_Icc 0 1 (by fun_prop) (ae_of_all _ fun z => hF01 _)
  rw [← integral_prod _ hint]
  have h1 : ∫ z, F (c * z.1 + d * z.2) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      ∫ s, F s ∂(((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (fun z : ℝ × ℝ => c * z.1 + d * z.2)) :=
    (integral_map (by fun_prop) hF.aestronglyMeasurable).symm
  have h2 : ∫ w, F (√(c ^ 2 + d ^ 2) * w) ∂(gaussianReal 0 1) =
      ∫ s, F s ∂((gaussianReal 0 1).map (fun w => √(c ^ 2 + d ^ 2) * w)) :=
    (integral_map (by fun_prop) hF.aestronglyMeasurable).symm
  rw [h1, h2, map_linear_prod_gaussianReal, gaussianReal_map_const_mul]
  congr 2
  all_goals first
    | (apply NNReal.eq; simp [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ c ^ 2 + d ^ 2)]; positivity)
    | simp

/-- For `e > 0`, `P(e Z ≤ t) = Φ(t / e)`. -/
theorem scaledNormalCDF_of_pos {e : ℝ} (he : 0 < e) (t : ℝ) :
    scaledNormalCDF e t = ProbabilityTheory.cdf (gaussianReal 0 1) (t / e) := by
  rw [scaledNormalCDF, cdf_eq_real]
  congr 1
  ext z
  simp only [mem_ofPred_eq, mem_Iic]
  rw [le_div_iff₀ he, mul_comm]

/-- **Conditional representation of the bivariate normal CDF**:
`P(X ≤ x, Y ≤ y) = ∫_{z ≤ x} P(√(1 − r²) Z ≤ y − r z) dΦ(z)`; for `|r| < 1` the integrand is
`Φ((y − r z)/√(1 − r²))` (`scaledNormalCDF_of_pos`). -/
theorem bivariateNormal_real_Iic_eq_setIntegral (r x y : ℝ) :
    (bivariateNormal r).real {p | p.1 ≤ x ∧ p.2 ≤ y} =
      ∫ z in Iic x, scaledNormalCDF (√(1 - r ^ 2)) (y - r * z) ∂(gaussianReal 0 1) := by
  set M : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, r * p.1 + √(1 - r ^ 2) * p.2) with hM
  have hMm : Measurable M := by fun_prop
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 ≤ x ∧ p.2 ≤ y} :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_snd measurable_const)
  rw [bivariateNormal, map_measureReal_apply hMm hmeas,
    ← integral_measureReal_prodMk _ _ (hmeas.preimage hMm), ← integral_indicator measurableSet_Iic]
  congr 1
  funext z
  by_cases hz : z ≤ x
  · rw [indicator_of_mem (show z ∈ Iic x from hz), scaledNormalCDF]
    congr 1
    ext w
    simp only [hM, mem_preimage, mem_ofPred_eq, hz, true_and]
    constructor <;> intro h <;> linarith
  · rw [indicator_of_notMem (show z ∉ Iic x from hz)]
    have hempty : Prod.mk z ⁻¹' (M ⁻¹' {p : ℝ × ℝ | p.1 ≤ x ∧ p.2 ≤ y}) = ∅ := by
      ext w
      simp only [hM, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun h => absurd h hz
    rw [hempty, measureReal_empty]

/-! ### Slepian's inequality for the bivariate normal law -/

/-- **Common factor representation** of the bivariate normal law with correlation `r ∈ [0, 1]`:
`P(X ≤ x, Y ≤ y) = E[K(x − √r W) K(y − √r W)]` with `K = P(√(1 − r) Z ≤ ·)`. -/
theorem bivariateNormal_real_Iic_eq_integral {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (x y : ℝ) :
    (bivariateNormal r).real {p | p.1 ≤ x ∧ p.2 ≤ y} =
      ∫ w, scaledNormalCDF (√(1 - r)) (x - √r * w) * scaledNormalCDF (√(1 - r)) (y - √r * w)
        ∂(gaussianReal 0 1) := by
  set γ := gaussianReal 0 1 with hγ
  set c := √r with hc
  set e := √(1 - r) with he
  have hc2 : c ^ 2 = r := Real.sq_sqrt hr0
  have he2 : e ^ 2 = 1 - r := Real.sq_sqrt (by linarith)
  set M : ℝ × (ℝ × ℝ) → ℝ × ℝ := fun z => (c * z.1 + e * z.2.1, c * z.1 + e * z.2.2) with hM_def
  have hMm : Measurable M := by fun_prop
  have hM : (γ.prod (γ.prod γ)).map M = bivariateNormal r := by
    refine eq_bivariateNormal_of_linear_laws ⟨by linarith, hr1⟩ fun a b => ?_
    rw [Measure.map_map (by fun_prop) hMm]
    have h : ((fun p : ℝ × ℝ => a * p.1 + b * p.2) ∘ M) =
        (fun t : ℝ × ℝ => ((a + b) * c) * t.1 + 1 * t.2) ∘
          Prod.map id (fun q : ℝ × ℝ => (a * e) * q.1 + (b * e) * q.2) := by
      funext z
      simp only [Function.comp_apply, hM_def, Prod.map_fst, Prod.map_snd, id_eq]
      ring
    rw [h, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id,
      map_linear_prod_gaussianReal, map_linear_prod_gaussianReal]
    congr 2
    rw [Real.coe_toNNReal _ (by positivity)]
    simp only [NNReal.coe_one, mul_one, one_pow, one_mul]
    linear_combination (a + b) ^ 2 * hc2 + (a ^ 2 + b ^ 2) * he2
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 ≤ x ∧ p.2 ≤ y} :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_snd measurable_const)
  rw [← hM, map_measureReal_apply hMm hmeas, ← integral_measureReal_prodMk _ _ (hmeas.preimage hMm)]
  congr 1
  funext w
  have hsec : Prod.mk w ⁻¹' (M ⁻¹' {p : ℝ × ℝ | p.1 ≤ x ∧ p.2 ≤ y}) =
      {z | e * z ≤ x - c * w} ×ˢ {z | e * z ≤ y - c * w} := by
    ext q
    simp only [hM_def, mem_preimage, mem_ofPred_eq, mem_prod]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hsec, measureReal_prod_prod]
  rfl

/-- **Slepian's inequality** (bivariate, nonnegative correlations): for `0 ≤ r ≤ r' ≤ 1`, the
orthant probabilities of the bivariate normal law increase with the correlation. -/
theorem bivariateNormal_real_Iic_mono {r r' : ℝ} (hr0 : 0 ≤ r) (hrr : r ≤ r') (hr1 : r' ≤ 1)
    (x y : ℝ) :
    (bivariateNormal r).real {p | p.1 ≤ x ∧ p.2 ≤ y} ≤
      (bivariateNormal r').real {p | p.1 ≤ x ∧ p.2 ≤ y} := by
  set γ := gaussianReal 0 1 with hγ
  set e := √(1 - r') with he
  set c := √r with hc
  set d := √(r' - r) with hd
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hsplit : √r' = √(c ^ 2 + d ^ 2) := by
    rw [Real.sq_sqrt hr0, Real.sq_sqrt (by linarith)]
    ring_nf
  have he' : √(1 - r) = √(d ^ 2 + e ^ 2) := by
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    ring_nf
  have hK := measurable_scaledNormalCDF
  have hmul : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → a * b ∈ Icc (0 : ℝ) 1 :=
    fun a b ha hb => ⟨mul_nonneg ha.1 hb.1, by nlinarith [ha.1, ha.2, hb.1, hb.2]⟩
  set F : ℝ → ℝ := fun s => scaledNormalCDF e (x - s) * scaledNormalCDF e (y - s) with hF
  have hFm : Measurable F :=
    ((hK e).comp (measurable_const.sub measurable_id)).mul
      ((hK e).comp (measurable_const.sub measurable_id))
  have hF01 : ∀ s, F s ∈ Icc (0 : ℝ) 1 := fun s =>
    hmul _ _ (scaledNormalCDF_mem_Icc _ _) (scaledNormalCDF_mem_Icc _ _)
  rw [bivariateNormal_real_Iic_eq_integral hr0 (hrr.trans hr1),
    bivariateNormal_real_Iic_eq_integral (hr0.trans hrr) hr1]
  change _ ≤ ∫ w, F (√r' * w) ∂γ
  rw [hsplit, integral_comp_sqrt_add_sq F hFm hF01 c d, he']
  have hint : Integrable (fun z : ℝ × ℝ => F (c * z.1 + d * z.2)) (γ.prod γ) :=
    Integrable.of_mem_Icc 0 1 (by fun_prop) (ae_of_all _ fun z => hF01 _)
  refine integral_mono (Integrable.of_mem_Icc 0 1 ?_ (ae_of_all _ fun w => hmul _ _
    (scaledNormalCDF_mem_Icc _ _) (scaledNormalCDF_mem_Icc _ _))) hint.integral_prod_left
    fun w => ?_
  · exact (((hK _).comp (measurable_const.sub (measurable_const.mul measurable_id))).mul
      ((hK _).comp (measurable_const.sub (measurable_const.mul measurable_id)))).aemeasurable
  · have hanti : ∀ t : ℝ, Antitone fun v => scaledNormalCDF e (t - d * v) := fun t v₁ v₂ h =>
      scaledNormalCDF_mono e (by nlinarith [mul_le_mul_of_nonneg_left h hd0])
    have hcheb := integral_mul_integral_le_integral_mul_of_antitone γ (hanti (x - c * w))
      (hanti (y - c * w)) (fun _ => scaledNormalCDF_mem_Icc _ _)
      (fun _ => scaledNormalCDF_mem_Icc _ _)
    rw [integral_scaledNormalCDF_sub, integral_scaledNormalCDF_sub] at hcheb
    refine hcheb.trans (le_of_eq ?_)
    congr 1
    funext v
    simp only [hF]
    congr 2 <;> ring

/-! ### Concordance ordering of the Gaussian copulas -/

/-- To compare two bivariate copulas pointwise it suffices to compare them at the points
`(Φ(x), Φ(y))`, which exhaust the open unit square. -/
theorem lowerOrthantLE_of_normalCDFPair {C D : Copula 2}
    (h : ∀ q : ℝ × ℝ, C.cdf (normalCDFPair q) ≤ D.cdf (normalCDFPair q)) :
    C.LowerOrthantLE D := by
  intro w
  have hw : w = ![w 0, w 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hw]
  rcases eq_or_lt_of_le (w 0).2.1 with hu0 | hu0
  · rw [show w 0 = 0 from Subtype.ext hu0.symm]
    simp
  rcases eq_or_lt_of_le (w 0).2.2 with hu1 | hu1
  · rw [show w 0 = 1 from Subtype.ext hu1]
    simp
  rcases eq_or_lt_of_le (w 1).2.1 with hv0 | hv0
  · rw [show w 1 = 0 from Subtype.ext hv0.symm]
    simp
  rcases eq_or_lt_of_le (w 1).2.2 with hv1 | hv1
  · rw [show w 1 = 1 from Subtype.ext hv1]
    simp
  obtain ⟨x, hx⟩ := exists_standardNormalCDFUnit_eq hu0 hu1
  obtain ⟨y, hy⟩ := exists_standardNormalCDFUnit_eq hv0 hv1
  have := h (x, y)
  simp only [normalCDFPair] at this
  rwa [hx, hy] at this

theorem bivariateGaussian_lowerOrthantLE_of_nonneg {r r' : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1)
    (hr' : r' ∈ Icc (-1 : ℝ) 1) (hr0 : 0 ≤ r) (hrr : r ≤ r') :
    (bivariateGaussian r hr).LowerOrthantLE (bivariateGaussian r' hr') :=
  lowerOrthantLE_of_normalCDFPair fun q => by
    rw [cdf_bivariateGaussian, cdf_bivariateGaussian]
    exact bivariateNormal_real_Iic_mono hr0 hrr hr'.2 q.1 q.2

theorem bivariateGaussian_lowerOrthantLE_of_nonpos {r r' : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1)
    (hr' : r' ∈ Icc (-1 : ℝ) 1) (hr0 : r' ≤ 0) (hrr : r ≤ r') :
    (bivariateGaussian r hr).LowerOrthantLE (bivariateGaussian r' hr') := by
  have hneg := bivariateGaussian_lowerOrthantLE_of_nonneg (neg_mem_corrInterval hr')
    (neg_mem_corrInterval hr) (by linarith) (by linarith : -r' ≤ -r)
  have e1 : bivariateGaussian r hr =
      (bivariateGaussian (-r) (neg_mem_corrInterval hr)).reflect {1} := by
    rw [reflect_second_bivariateGaussian]
    exact bivariateGaussian_congr (neg_neg r).symm _ _
  have e2 : bivariateGaussian r' hr' =
      (bivariateGaussian (-r') (neg_mem_corrInterval hr')).reflect {1} := by
    rw [reflect_second_bivariateGaussian]
    exact bivariateGaussian_congr (neg_neg r').symm _ _
  intro w
  have hw : w = ![w 0, w 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hw, e1, e2, cdf_reflect_second, cdf_reflect_second]
  linarith [hneg ![w 0, unitInterval.symm (w 1)]]

/-- **Slepian's inequality / concordance ordering**: the bivariate Gaussian copulas increase
pointwise with the correlation, `r ≤ r' → C_r ≤ C_{r'}`. -/
theorem bivariateGaussian_lowerOrthantLE {r r' : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1)
    (hr' : r' ∈ Icc (-1 : ℝ) 1) (hrr : r ≤ r') :
    (bivariateGaussian r hr).LowerOrthantLE (bivariateGaussian r' hr') := by
  rcases le_total 0 r with h0 | h0
  · exact bivariateGaussian_lowerOrthantLE_of_nonneg hr hr' h0 hrr
  rcases le_total r' 0 with h1 | h1
  · exact bivariateGaussian_lowerOrthantLE_of_nonpos hr hr' h1 hrr
  have h00 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  exact (bivariateGaussian_lowerOrthantLE_of_nonpos hr h00 le_rfl h0).trans
    (bivariateGaussian_lowerOrthantLE_of_nonneg h00 hr' le_rfl h1)

/-- The Gaussian copulas are increasing in `r` for the concordance order (lower and upper
orthants). -/
theorem bivariateGaussian_concordanceLE {r r' : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1)
    (hr' : r' ∈ Icc (-1 : ℝ) 1) (hrr : r ≤ r') :
    (bivariateGaussian r hr).ConcordanceLE (bivariateGaussian r' hr') :=
  (concordanceLE_iff_lowerOrthantLE _ _).2 (bivariateGaussian_lowerOrthantLE hr hr' hrr)

/-- The bivariate Gaussian copula is positively quadrant dependent iff `r ≥ 0`. -/
theorem isPQD_bivariateGaussian_iff {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateGaussian r hr).IsPQD ↔ 0 ≤ r := by
  have h00 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  constructor
  · intro h
    have hβ := h unitHalf unitHalf
    have hb := blomqvistBeta_bivariateGaussian hr
    rw [blomqvistBeta] at hb
    rw [show ((unitHalf : I) : ℝ) = 1 / 2 from rfl] at hβ
    have : 0 ≤ arcsin r := by
      have hπ := pi_pos
      have h2 : 0 ≤ 2 / π * arcsin r := by rw [← hb]; norm_num at hβ ⊢; linarith
      exact nonneg_of_mul_nonneg_right (by linarith) (by positivity : (0 : ℝ) < 2 / π)
    exact arcsin_nonneg.1 this
  · intro h0 u v
    have := bivariateGaussian_lowerOrthantLE h00 hr h0 ![u, v]
    rw [bivariateGaussian_zero, cdf_independence, Fin.prod_univ_two] at this
    simpa using this

/-- The bivariate Gaussian copula is negatively quadrant dependent iff `r ≤ 0`. -/
theorem isNQD_bivariateGaussian_iff {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateGaussian r hr).IsNQD ↔ r ≤ 0 := by
  have h00 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  constructor
  · intro h
    have hβ := h unitHalf unitHalf
    have hb := blomqvistBeta_bivariateGaussian hr
    rw [blomqvistBeta] at hb
    rw [show ((unitHalf : I) : ℝ) = 1 / 2 from rfl] at hβ
    have : arcsin r ≤ 0 := by
      have hπ := pi_pos
      have h2 : 2 / π * arcsin r ≤ 0 := by rw [← hb]; norm_num at hβ ⊢; linarith
      exact nonpos_of_mul_nonpos_right h2 (by positivity : (0 : ℝ) < 2 / π)
    exact arcsin_nonpos.1 this
  · intro h0 u v
    have := bivariateGaussian_lowerOrthantLE hr h00 h0 ![u, v]
    rw [bivariateGaussian_zero, cdf_independence, Fin.prod_univ_two] at this
    simpa using this

end ProbabilityTheory.Copula
