/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Elliptical.ScaleMixture
import Copula.Families.Gaussian.Sheppard
import Copula.Families.ScaleMixtures

/-! # Kendall's tau and Blomqvist's beta of bivariate Gaussian scale mixtures

Let `(X, Y) = S · (G₁, G₂)` where `G ~ N(0, R)` with `R = !![1, r; r, 1]` and `S > 0` is an
independent scale (`gaussianScaleMixture`). This covers the Student-t, Cauchy, variance-gamma,
Laplace, slash and normal–lognormal copulas of the library. Then, whatever the mixing law,

* `kendallTau_gaussianScaleMixture`: `τ = (2/π) arcsin r` (Lindskog, McNeil and Schmock 2003);
* `blomqvistBeta_gaussianScaleMixture`: `β = (2/π) arcsin r`;
* the same values for the Student-t (any `ν > 0`), Cauchy, variance-gamma, Laplace, slash and
  normal–lognormal copulas with correlation matrix `!![1, r; r, 1]`.

Both reduce to Sheppard's formula conditionally on the scales: given `S = s, S' = s'`, the vector
`(s' G'₁ − s G₁, s' G'₂ − s G₂)` is centered bivariate normal with correlation `r`
(`multivariateGaussian_corrMatrix_orthant_sub`). In contrast to the Gaussian case, Spearman's rho of
a scale mixture depends on the mixing law and is not treated here.

## References
* F. Lindskog, A. McNeil, U. Schmock, *Kendall's tau for elliptical distributions*, in
  Credit Risk (2003), 149–156.
* H. Joe, *Dependence Modeling with Copulas*, CRC Press 2014, §4.3 and §2.12.
-/

open MeasureTheory Set Real
open scoped unitInterval ENNReal NNReal

namespace ProbabilityTheory.Copula

/-! ### Mixtures -/

/-- A set whose sections have constant mass `c` (for a.e. value of the second factor) has mass
`c` under a product of probability measures. -/
theorem measure_prod_eq_const_of_ae {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (N : Measure E) (μ : Measure F) [IsProbabilityMeasure N] [IsProbabilityMeasure μ]
    {A : Set (E × F)} (hA : MeasurableSet A) {c : ℝ≥0∞}
    (h : ∀ᵐ t ∂μ, N {g | (g, t) ∈ A} = c) :
    (N.prod μ) A = c := by
  rw [Measure.prod_apply_symm hA]
  exact (lintegral_congr_ae h).trans (by rw [lintegral_const, measure_univ, mul_one])

/-- Two-fold mixture version of `measure_prod_eq_const_of_ae`: if conditionally on the mixing
variables `t, t'` the set has `N ⊗ N`-mass `c`, then it has mass `c` under `(N ⊗ μ) ⊗ (N ⊗ μ)`. -/
theorem measure_prod_prod_eq_const_of_ae {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (N : Measure E) (μ : Measure F) [IsProbabilityMeasure N] [IsProbabilityMeasure μ]
    {A : Set ((E × F) × (E × F))} (hA : MeasurableSet A) {c : ℝ≥0∞}
    (h : ∀ᵐ t ∂μ, ∀ᵐ t' ∂μ, (N.prod N) {g : E × E | ((g.1, t), (g.2, t')) ∈ A} = c) :
    ((N.prod μ).prod (N.prod μ)) A = c := by
  set f : (E × F) × (E × F) → ℝ≥0∞ := A.indicator 1 with hf_def
  have hf : Measurable f := measurable_one.indicator hA
  rw [← lintegral_indicator_one hA, lintegral_prod _ hf.aemeasurable,
    lintegral_prod_symm _ (hf.lintegral_prod_right').aemeasurable]
  have hin : ∀ g t, ∫⁻ q', f ((g, t), q') ∂(N.prod μ) =
      ∫⁻ t', ∫⁻ g', f ((g, t), (g', t')) ∂N ∂μ := fun g t =>
    lintegral_prod_symm _ (hf.comp (by fun_prop)).aemeasurable
  simp_rw [hin]
  have hsw : ∀ t, ∫⁻ g, ∫⁻ t', ∫⁻ g', f ((g, t), (g', t')) ∂N ∂μ ∂N =
      ∫⁻ t', ∫⁻ g, ∫⁻ g', f ((g, t), (g', t')) ∂N ∂N ∂μ := fun t =>
    lintegral_lintegral_swap (Measurable.aemeasurable
      (Measurable.lintegral_prod_right' (f := fun p : (E × F) × E => f ((p.1.1, t), (p.2, p.1.2)))
        (hf.comp (by fun_prop))))
  simp_rw [hsw]
  have hpair : ∀ t t', ∫⁻ g, ∫⁻ g', f ((g, t), (g', t')) ∂N ∂N =
      (N.prod N) {g : E × E | ((g.1, t), (g.2, t')) ∈ A} := by
    intro t t'
    have hm : MeasurableSet {g : E × E | ((g.1, t), (g.2, t')) ∈ A} :=
      hA.preimage (f := fun g : E × E => ((g.1, t), (g.2, t'))) (by fun_prop)
    rw [← lintegral_indicator_one hm, lintegral_prod _ (measurable_one.indicator hm).aemeasurable]
    rfl
  simp_rw [hpair]
  rw [lintegral_congr_ae (h.mono fun t ht => (lintegral_congr_ae ht).trans
    ((lintegral_const c).trans (by rw [measure_univ, mul_one]))), lintegral_const, measure_univ,
    mul_one]

/-! ### Orthant probabilities of the normal law with correlation matrix `corrMatrix r` -/

/-- Sheppard's formula for `N(0, corrMatrix r)`. -/
theorem multivariateGaussian_corrMatrix_orthant {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (corrMatrix r)).real
        {g | g 0 ≤ 0 ∧ g 1 ≤ 0} = 1 / 4 + arcsin r / (2 * π) :=
  orthant_nonpos_of_linear_laws _ (by fun_prop) (by fun_prop) hr one_pos fun a b => by
    rw [map_linear_multivariateGaussian_corrMatrix hr]
    congr 2
    ring

/-- Sheppard's formula for scaled differences of two independent `N(0, corrMatrix r)` vectors. -/
theorem multivariateGaussian_corrMatrix_orthant_sub {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (corrMatrix r)).prod
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (corrMatrix r))).real
        {z | b * z.2 0 - a * z.1 0 ≤ 0 ∧ b * z.2 1 - a * z.1 1 ≤ 0} =
      1 / 4 + arcsin r / (2 * π) := by
  set N := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (corrMatrix r)
  have hscale : ∀ (c p q : ℝ), N.map (fun g => c * (p * g 0 + q * g 1)) =
      gaussianReal 0 (c ^ 2 * (p ^ 2 + 2 * p * q * r + q ^ 2)).toNNReal := by
    intro c p q
    have hcomp : (fun g : EuclideanSpace ℝ (Fin 2) => c * (p * g 0 + q * g 1)) =
        (fun x => c * x) ∘ fun g => p * g 0 + q * g 1 := rfl
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
      map_linear_multivariateGaussian_corrMatrix hr, gaussianReal_map_const_mul]
    congr 1
    · ring
    · apply NNReal.eq
      simp [Real.coe_toNNReal _ (corr_quadratic_nonneg hr p q),
        Real.coe_toNNReal _ (mul_nonneg (sq_nonneg c) (corr_quadratic_nonneg hr p q))]
  refine orthant_nonpos_of_linear_laws (N.prod N) (by fun_prop) (by fun_prop) hr
    (by positivity : 0 < a ^ 2 + b ^ 2) fun p q => ?_
  have h : (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      p * (b * z.2 0 - a * z.1 0) + q * (b * z.2 1 - a * z.1 1)) =
      (fun t : ℝ × ℝ => (-1) * t.1 + 1 * t.2) ∘
        Prod.map (fun g => a * (p * g 0 + q * g 1)) (fun g => b * (p * g 0 + q * g 1)) := by
    funext z
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
    ring
  rw [h, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), hscale, hscale,
    map_linear_prod_gaussianReal,
    Real.coe_toNNReal _ (mul_nonneg (sq_nonneg a) (corr_quadratic_nonneg hr p q)),
    Real.coe_toNNReal _ (mul_nonneg (sq_nonneg b) (corr_quadratic_nonneg hr p q))]
  congr 2
  ring

/-! ### Medians of symmetric marginals -/

/-- A symmetric atomless law has median `0`: `F(0) = 1/2`. -/
theorem cdf_zero_of_map_neg_eq {ν : Measure ℝ} [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (h : ν.map (fun x => -x) = ν) : ProbabilityTheory.cdf ν 0 = 1 / 2 := by
  have hc : ν.real (Iic 0) = 1 - ν.real (Iic 0) := by
    conv_lhs => rw [← h]
    rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
    have hpre : (fun t : ℝ => -t) ⁻¹' Iic 0 = (Iio 0)ᶜ := by
      ext t
      simp
    rw [hpre, probReal_compl_eq_one_sub measurableSet_Iio, measureReal_congr Iio_ae_eq_Iic]
  rw [cdf_eq_real]
  linarith

/-- The marginals of a Gaussian scale mixture are symmetric. -/
theorem marginal_gaussianScaleMixtureLaw_map_neg {d : ℕ} (R : Matrix (Fin d) (Fin d) ℝ)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ)
    (hs : Measurable s) (i : Fin d) :
    (marginal (gaussianScaleMixtureLaw R μ s) i).map (fun x => -x) =
      marginal (gaussianScaleMixtureLaw R μ s) i := by
  have hmarg : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R).map
      (fun x => x i) = gaussianReal 0 1 := by
    have h := (measurePreserving_eval_multivariateGaussian
      (μ := (0 : EuclideanSpace ℝ (Fin d))) hR (i := i)).map_eq
    have hz : (0 : EuclideanSpace ℝ (Fin d)) i = (0 : ℝ) := rfl
    rw [hz, hdiag, Real.toNNReal_one] at h
    exact h
  set N := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R
  set g : ℝ × ℝ → ℝ := fun p => s p.2 * p.1 with hg
  have he : marginal (gaussianScaleMixtureLaw R μ s) i =
      ((gaussianReal 0 1).prod μ.toMeasure).map g := by
    change Measure.map (fun x => x i) (Measure.map (fun p (j : Fin d) => s p.2 * p.1 j)
      (N.prod μ.toMeasure)) = _
    rw [Measure.map_map (by fun_prop) (Measurable.of_eval fun j => by fun_prop), ← hmarg,
      ← Measure.map_id (μ := μ.toMeasure), Measure.map_prod_map _ _ (by fun_prop) measurable_id,
      Measure.map_map (by fun_prop) (by fun_prop), Measure.map_id]
    rfl
  have hneg : ((gaussianReal 0 1).map (fun x => -x)) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  rw [he, Measure.map_map (by fun_prop) (by fun_prop)]
  calc ((gaussianReal 0 1).prod μ.toMeasure).map ((fun x => -x) ∘ g)
      = ((gaussianReal 0 1).prod μ.toMeasure).map (g ∘ Prod.map (fun x => -x) id) := by
        congr 1
        funext p
        simp only [hg, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
        ring
    _ = (((gaussianReal 0 1).prod μ.toMeasure).map (Prod.map (fun x => -x) id)).map g :=
        (Measure.map_map (by fun_prop) (by fun_prop)).symm
    _ = ((gaussianReal 0 1).prod μ.toMeasure).map g := by
        rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id, hneg, Measure.map_id]

/-! ### Blomqvist's beta and Kendall's tau -/

theorem sheppard_nonneg (r : ℝ) : 0 ≤ 1 / 4 + arcsin r / (2 * π) := by
  have h := neg_pi_div_two_le_arcsin r
  have hπ := pi_pos
  rw [div_add_div _ _ (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
  nlinarith

/-- The marginal medians of a bivariate Gaussian scale mixture are `0`, so the marginal transform
maps `0` to `(1/2, 1/2)`. -/
theorem marginalTransform_zero_gaussianScaleMixtureLaw {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hpos : ∀ᵐ t ∂μ.toMeasure, 0 < s t) :
    marginalTransform (gaussianScaleMixtureLaw (corrMatrix r) μ s) 0 = ![unitHalf, unitHalf] := by
  have key : ∀ i, ProbabilityTheory.cdf (marginal (gaussianScaleMixtureLaw (corrMatrix r) μ s) i)
      0 = 1 / 2 := fun i => by
    let := atomless_gaussianScaleMixtureLaw_marginal (corrMatrix r) (posSemidef_corrMatrix hr)
      (corrMatrix_diag r) μ s hs hpos i
    exact cdf_zero_of_map_neg_eq (marginal_gaussianScaleMixtureLaw_map_neg _
      (posSemidef_corrMatrix hr) (corrMatrix_diag r) μ s hs i)
  funext i
  apply Subtype.ext
  fin_cases i <;> simp [marginalTransform, key, unitHalf]

/-- **Blomqvist's beta of an elliptical (Gaussian scale mixture) copula**:
`β = (2/π) arcsin r`, independently of the mixing law. -/
theorem blomqvistBeta_gaussianScaleMixture {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hpos : ∀ᵐ t ∂μ.toMeasure, 0 < s t) :
    (gaussianScaleMixture (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r) μ s hs
      hpos).blomqvistBeta = 2 / π * arcsin r := by
  set N := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (corrMatrix r)
  set f : EuclideanSpace ℝ (Fin 2) × ℝ → Fin 2 → ℝ := fun p i => s p.2 * p.1 i with hf_def
  have hf : Measurable f := Measurable.of_eval fun i => by fun_prop
  have hsk := isSklarCopula_gaussianScaleMixture (corrMatrix r) (posSemidef_corrMatrix hr)
    (corrMatrix_diag r) μ s hs hpos 0
  rw [marginalTransform_zero_gaussianScaleMixtureLaw hr μ s hs hpos] at hsk
  have hA : MeasurableSet (f ⁻¹' Iic (0 : Fin 2 → ℝ)) := measurableSet_Iic.preimage hf
  have hP : (gaussianScaleMixtureLaw (corrMatrix r) μ s).toMeasure (Iic 0) =
      ENNReal.ofReal (1 / 4 + arcsin r / (2 * π)) := by
    change Measure.map f (N.prod μ.toMeasure) (Iic 0) = _
    rw [Measure.map_apply hf measurableSet_Iic]
    apply measure_prod_eq_const_of_ae N μ.toMeasure hA
    filter_upwards [hpos] with t ht
    have key : ∀ x : ℝ, s t * x ≤ 0 ↔ x ≤ 0 := fun x => by
      constructor <;> intro h <;> nlinarith
    have hset : {g | (g, t) ∈ f ⁻¹' Iic (0 : Fin 2 → ℝ)} = {g | g 0 ≤ 0 ∧ g 1 ≤ 0} := by
      ext g
      simp only [hf_def, mem_preimage, mem_Iic, Pi.le_def, Fin.forall_fin_two, Pi.zero_apply,
        mem_ofPred_eq, key]
    rw [hset, ← ofReal_measureReal, multivariateGaussian_corrMatrix_orthant hr]
  rw [blomqvistBeta, hsk, measureReal_def, hP, ENNReal.toReal_ofReal (sheppard_nonneg r)]
  field_simp
  ring

/-- **Kendall's tau of an elliptical (Gaussian scale mixture) copula** (Lindskog–McNeil–Schmock):
`τ = (2/π) arcsin r`, independently of the mixing law. -/
theorem kendallTau_gaussianScaleMixture {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hpos : ∀ᵐ t ∂μ.toMeasure, 0 < s t) :
    (gaussianScaleMixture (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r) μ s hs
      hpos).kendallTau = 2 / π * arcsin r := by
  set C := gaussianScaleMixture (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r) μ s
    hs hpos
  set P := gaussianScaleMixtureLaw (corrMatrix r) μ s
  set N := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (corrMatrix r)
  set f : EuclideanSpace ℝ (Fin 2) × ℝ → Fin 2 → ℝ := fun p i => s p.2 * p.1 i with hf_def
  have hf : Measurable f := Measurable.of_eval fun i => by fun_prop
  have hsk := isSklarCopula_gaussianScaleMixture (corrMatrix r) (posSemidef_corrMatrix hr)
    (corrMatrix_diag r) μ s hs hpos
  have hS : MeasurableSet {z : (Fin 2 → ℝ) × (Fin 2 → ℝ) | z.2 ≤ z.1} :=
    measurableSet_le measurable_snd measurable_fst
  have hint : ∫ x, C.cdf x ∂C.toMeasure =
      (P.toMeasure.prod P.toMeasure).real {z | z.2 ≤ z.1} := by
    change ∫ x, C.cdf x ∂(P.toMeasure.map (marginalTransform P)) = _
    rw [integral_map (measurable_marginalTransform P).aemeasurable
      (continuous_cdf C).aestronglyMeasurable, ← integral_measureReal_prodMk _ _ hS]
    congr 1
    funext x
    rw [hsk x]
    rfl
  have hA : MeasurableSet (Prod.map f f ⁻¹' {z : (Fin 2 → ℝ) × (Fin 2 → ℝ) | z.2 ≤ z.1}) :=
    hS.preimage (hf.prodMap hf)
  have hPP : (P.toMeasure.prod P.toMeasure) {z | z.2 ≤ z.1} =
      ENNReal.ofReal (1 / 4 + arcsin r / (2 * π)) := by
    change ((N.prod μ.toMeasure).map f).prod ((N.prod μ.toMeasure).map f) _ = _
    rw [Measure.map_prod_map _ _ hf hf, Measure.map_apply (hf.prodMap hf) hS]
    apply measure_prod_prod_eq_const_of_ae N μ.toMeasure hA
    filter_upwards [hpos] with t ht
    filter_upwards [hpos] with t' ht'
    have hset : {g : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
        ((g.1, t), (g.2, t')) ∈ Prod.map f f ⁻¹' {z : (Fin 2 → ℝ) × (Fin 2 → ℝ) | z.2 ≤ z.1}} =
        {z | s t' * z.2 0 - s t * z.1 0 ≤ 0 ∧ s t' * z.2 1 - s t * z.1 1 ≤ 0} := by
      ext g
      simp only [hf_def, mem_preimage, Prod.map_fst, Prod.map_snd, mem_ofPred_eq, Pi.le_def,
        Fin.forall_fin_two, sub_nonpos]
    rw [hset, ← ofReal_measureReal, multivariateGaussian_corrMatrix_orthant_sub hr ht ht']
  rw [kendallTau, hint, measureReal_def, hPP, ENNReal.toReal_ofReal (sheppard_nonneg r)]
  field_simp
  ring

/-! ### Named elliptical families -/

section Families

variable {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1)
include hr

/-- Kendall's tau of the Student-t copula: `τ = (2/π) arcsin r` for every `ν > 0`. -/
theorem kendallTau_studentT (ν : ℝ) (hν : 0 < ν) :
    (studentT (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r) ν hν).kendallTau =
      2 / π * arcsin r :=
  kendallTau_gaussianScaleMixture hr _ _ _ _

/-- Blomqvist's beta of the Student-t copula: `β = (2/π) arcsin r` for every `ν > 0`. -/
theorem blomqvistBeta_studentT (ν : ℝ) (hν : 0 < ν) :
    (studentT (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r) ν hν).blomqvistBeta =
      2 / π * arcsin r :=
  blomqvistBeta_gaussianScaleMixture hr _ _ _ _

theorem kendallTau_cauchy :
    (cauchy (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r)).kendallTau =
      2 / π * arcsin r :=
  kendallTau_studentT hr 1 one_pos

theorem kendallTau_varianceGamma (κ : ℝ) (hκ : 0 < κ) :
    (varianceGamma (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r) κ
      hκ).kendallTau = 2 / π * arcsin r :=
  kendallTau_gaussianScaleMixture hr _ _ _ _

theorem kendallTau_laplace :
    (laplace (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r)).kendallTau =
      2 / π * arcsin r :=
  kendallTau_varianceGamma hr 1 one_pos

theorem kendallTau_slash (q : ℝ) (hq : 0 < q) :
    (slash (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r) q hq).kendallTau =
      2 / π * arcsin r :=
  kendallTau_gaussianScaleMixture hr _ _ _ _

theorem kendallTau_normalLognormal (τ : ℝ≥0) :
    (normalLognormal (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r)
      τ).kendallTau = 2 / π * arcsin r :=
  kendallTau_gaussianScaleMixture hr _ _ _ _

end Families

end ProbabilityTheory.Copula
